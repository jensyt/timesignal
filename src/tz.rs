//! Support for parsing and using compiled timezone files (TZif files) and TZ strings.
//!
//! This module supports a subset of Olson timezone database features: UTC offsets and daylight
//! savings time changes, specified either directly in TZif binary data or via a TZ string (which
//! may be present in the compiled TZif file or supplied directly). This module supports versions
//! 1-4 of the TZif specification for this subset of features, and most extended POSIX features
//! for TZ strings.
//!
//! Key unsupported features are:
//! - **Leap seconds**. Unix timestamps most commonly do not include leap seconds, instead either
//!   repeating or lengthening the prior second. Given their occurrence is rare and generally not
//!   used, they are not supported in this module. This should not pose a problem in the vast
//!   majority of use cases.
//! - **Special TZ names**. The POSIX specification allows special timezone names enclosed in <...>
//!   which are not fully supported in this module. For example, "<5>6" represents a timezone named
//!   "5" with an offset of UTC-6. This specification will fail in this module. As an alternative,
//!   consider "FIVE6" which will work.
//! - **Accessing timezone names**. This module does not save timezone names.
//!
//! # Examples
//!
//! ```
//! // Parsing a file
//! let timezone1 = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();
//!
//! // Parsing a TZ string
//! let timezone2 = parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
//!
//! // Getting info for a given unix timestamp
//! let info = timezone1.info(1723433665);
//! assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
//!
//! // Getting the date for a given unix timestamp
//! let date = timezone2.date(1723433665);
//! assert_eq!(date, Some(TmWithTzInfo {
//! 	tm: Tm { sec: 25, min: 34, hour: 23, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
//! 	info: TzInfo { utoff: -14400, isdst: true }
//! }));
//! ```

use std::{error, fmt, fs, io, mem::size_of, path::Path, slice::SliceIndex};
use crate::time::{
	days_per_month,
	isleapyear,
	timestamp_from_yd,
	timestamp_from_ymd,
	wday_from_ymd,
	y_from_timestamp,
	Tm
};

/// The error type for parsing timezone data (TZif files and TZ strings).
pub enum Error {
	/// Error reading the file. The source [`io::Error`] is returned as a payload of this variant.
	FileReadError(io::Error),
	/// The file being read is not a TZif file (missing "TZif" magic bytes).
	NotATzFile,
	/// The file is not one of the four supported versions. The found version is returned as a payload
	/// of this variant.
	UnsupportedVersion(u8),
	/// The file is not a valid TZif file.
	InvalidTzFile,
	/// The TZ string is invalid or unsupported.
	InvalidOrUnsupportedTzString
}

impl From<io::Error> for Error {
	/// Wrap an [`io::Error`] in a [`Error::FileReadError`].
	fn from(error: io::Error) -> Self {
		Self::FileReadError(error)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Error::FileReadError(s) => write!(f, "{}", s),
			Error::NotATzFile => write!(f, "Not a TZ file"),
			Error::UnsupportedVersion(v) => write!(f, "Unsupported TZ version: {0} ({0:#04x})", v),
			Error::InvalidTzFile => write!(f, "Invalid TZ file"),
			Error::InvalidOrUnsupportedTzString => write!(f, "Invalid TZ string")
		}
	}
}

impl fmt::Debug for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		if let Self::FileReadError(s) = self {
			Some(s)
		} else {
			None
		}
	}
}

/// Read a big endian, unsigned 32-bit number from a byte array.
///
/// # Panics
/// This function must be called with a slice of length 4. Any other input will panic.
///
/// # Examples
///
/// ```
/// assert_eq!(read_u32(&[0, 0, 0, 1]), 1);
/// assert_eq!(read_u32(&[255, 255, 255, 255]), 4294967295);
/// ```
#[inline(always)]
fn read_u32(bytes: &[u8]) -> u32 {
	u32::from_be_bytes(bytes.try_into().unwrap())
}

/// Read a big endian, signed 32-bit number from a byte array.
///
/// # Panics
/// This function must be called with a slice of length 4. Any other input will panic.
///
/// # Examples
///
/// ```
/// assert_eq!(read_i32(&[0, 0, 0, 1]), 1);
/// assert_eq!(read_i32(&[255, 255, 255, 255]), -1);
/// ```
#[inline(always)]
fn read_i32(bytes: &[u8]) -> i32 {
	i32::from_be_bytes(bytes.try_into().unwrap())
}

/// Read a big endian, signed 64-bit number from a byte array.
///
/// # Panics
/// This function must be called with a slice of length 8. Any other input will panic.
///
/// # Examples
///
/// ```
/// assert_eq!(read_i64(&[0, 0, 0, 0, 0, 0, 0, 1]), 1);
/// assert_eq!(read_i64(&[255, 255, 255, 255, 255, 255, 255, 255]), -1);
/// ```
#[inline(always)]
fn read_i64(bytes: &[u8]) -> i64 {
	i64::from_be_bytes(bytes.try_into().unwrap())
}

/// An integral type for parsing timestamps
trait ParseType: Into<i64> {
	/// Read a big endian value from a byte array.
	///
	/// # Panics
	/// This function must be called with a slice of length `size_of::<Self>()`. Any other input will
	/// panic.
	fn read(bytes: &[u8]) -> Self;
}

impl ParseType for i32 {
	#[inline(always)]
	fn read(bytes: &[u8]) -> Self {
		read_i32(bytes)
	}
}

impl ParseType for i64 {
	#[inline(always)]
	fn read(bytes: &[u8]) -> Self {
		read_i64(bytes)
	}
}

/// Get a given index, if valid, or return [`Error::InvalidTzFile`].
#[inline(always)]
fn get_or_invalid<I>(bytes: &[u8], index: I) -> Result<&I::Output, Error>
where I: SliceIndex<[u8]> {
	bytes.get(index).ok_or(Error::InvalidTzFile)
}

/// Get a given index, if valid, or return [`Error::InvalidOrUnsupportedTzString`].
#[inline(always)]
fn get_or_invalid_tzstring<I>(bytes: &[u8], index: I) -> Result<&I::Output, Error>
where I: SliceIndex<[u8]> {
	bytes.get(index).ok_or(Error::InvalidOrUnsupportedTzString)
}

/// Get a given index, if valid, or return [`Default::default()`].
#[inline(always)]
fn get_or_default(bytes: &[u8], index: usize) -> u8 {
	bytes.get(index).copied().unwrap_or_default()
}

/// Header for the TZif file.
///
/// This header excludes the magic number (`'TZif'`) and version number.
#[cfg_attr(test, derive(Debug, PartialEq))]
struct TzHeader {
	/// Count of UT/local indicators
	isutcnt: u32,
	/// Count of standard/wall indicators
	isstdcnt: u32,
	/// Count of lead seconds
	leapcnt: u32,
	/// Count of transition times
	timecnt: u32,
	/// Count of time type records
	typecnt: u32,
	/// Number of bytes used for time zone names
	charcnt: u32
}

impl TzHeader {
	/// Parse a TZif header.
	///
	/// `bytes` should exclude the magic number, version number, and unused (reserved) components of
	/// the header. In other words, it should begin at offset +20 in the real TZif header.
	///
	/// # Errors
	///
	/// Returns [`Error::InvalidTzFile`] if the length of `bytes` is less than 24 bytes
	fn parse(bytes: &[u8]) -> Result<TzHeader, Error> {
		Ok(TzHeader {
			isutcnt: read_u32(get_or_invalid(bytes, 0..4)?),
			isstdcnt: read_u32(get_or_invalid(bytes, 4..8)?),
			leapcnt: read_u32(get_or_invalid(bytes, 8..12)?),
			timecnt: read_u32(get_or_invalid(bytes, 12..16)?),
			typecnt: read_u32(get_or_invalid(bytes, 16..20)?),
			charcnt: read_u32(get_or_invalid(bytes, 20..24)?),
		})
	}
}

/// Timezone information at a moment in time.
///
/// This type provides the UTC offset and whether standard time or daylight savings time is in
/// effect on the associated date (which is not itself stored in this type). UTC offsets are added
/// to UTC to determine the local time. For example, New York during standard time has a UTC offset
/// of `-5 hours` (or `-18000 seconds`), so `16:00 UTC` becomes `11:00 EST`.
///
/// The default value for this type is `{ utoff: 0, isdst: false }`.
#[derive(Clone, Copy, Default)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct TzInfo {
	/// The UTC offset in seconds
	pub utoff: i32,
	/// Whether standard time (`false`) or daylight savings time (`true`) is in effect
	pub isdst: bool
}

/// Calendar time with associated timezone information.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct TmWithTzInfo {
	/// The calendar time (in local timezone)
	pub tm: Tm,
	/// The timezone information for that time
	pub info: TzInfo
}

/// Parse an integer from a byte slice.
///
/// Reads as many digits [0-9] as are available and returns the parsed integer and the number of
/// digits parsed. If no digits are available, either because the `bytes` is empty or because the
/// first byte is not a digit in the range [0-9] then this function returns `(0, 0)`.
///
/// # Examples
///
/// ```
/// assert_eq!(parse_num(b"15x"), (15, 2));
/// assert_eq!(parse_num(b"x15"), (0, 0));
/// ```
fn parse_num(bytes: &[u8]) -> (u32, usize) {
	let mut i = 0;
	let mut r = 0;
	for b in bytes {
		match *b {
			v @ b'0'..=b'9' => r = r * 10 + (v - b'0') as u32,
			_ => break
		}
		i += 1
	}
	(r, i)
}

/// A TZ string date rule.
///
/// There are three types of date rules supported in POSIX TZ strings: 0-indexed Julian day,
/// 1-indexed Julian day ignoring leap days, and month/week/day.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum TzDateRule {
	/// 'J`n`' where `n` is the Julian day between 1 and 365. Leap days are ignored, so day 60 is
	/// always March 1st.
	J(u16),
	/// '`n`' where `n` is the Julian day between 0 and 365. Leap day is counted in leap years, so
	/// day 60 is March 1st in leap years but March 2nd in non-leap years.
	N(u16),
	/// 'M`m`.`w`.`d`' where `m` is the month number (1-12), `d` is the day of week (0-7 =>
	/// Sunday-Saturday), and `w` (1-5) represents the `w`th instance of day `d` in the month.
	/// If `w` is 5 then this rule selects the last instance of day `d` in the month, which could
	/// be the 4th or 5th instance depending on the day and month.
	M(u8, u8, u8)
}

impl TzDateRule {
	/// Parse one of the three supported date rules.
	///
	/// On success, this function returns a tuple containing the parsed date rule and the number of
	/// bytes consumed to parse the date rule. Note that there may be additional data in `bytes` after
	/// the parsed date rule that are ignored and will not cause an error if the input is valid before
	/// that point.
	///
	/// # Errors
	///
	/// Returns [`Error::InvalidOrUnsupportedTzString`] if `bytes` is zero length or the input is
	/// not a valid TZ date string.
	///
	/// # Examples
	///
	/// ```
	/// assert_eq!(TzDateRule::parse(b"57"), Ok((TzDateRule::N(57), 2)));
	/// assert_eq!(TzDateRule::parse(b"578"), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzDateRule::parse(b"J57"), Ok((TzDateRule::J(57), 3)));
	/// assert_eq!(TzDateRule::parse(b"J0"), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzDateRule::parse(b"J366"), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzDateRule::parse(b"M12.5.6"), Ok((TzDateRule::M(12, 5, 6), 7)));
	/// assert_eq!(TzDateRule::parse(b"M12.5.6asd"), Ok((TzDateRule::M(12, 5, 6), 7)));
	/// assert_eq!(TzDateRule::parse(b"M12.5.asd"), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzDateRule::parse(b"M13.5.6"), Err(Error::InvalidOrUnsupportedTzString));
	/// ```
	fn parse(bytes: &[u8]) -> Result<(TzDateRule, usize), Error> {
		if bytes.len() == 0 {
			return Err(Error::InvalidOrUnsupportedTzString)
		}

		// Indexing can't panic because of zero-size check above
		match bytes[0] {
			// Jn
			b'J' => {
				let (n, offset) = parse_num(get_or_invalid_tzstring(bytes, 1..)?);
				if n == 0 || n > 365 {
					Err(Error::InvalidOrUnsupportedTzString)
				} else {
					// Add 1 to offset because of the 'J'
					Ok((TzDateRule::J(n as u16), offset + 1))
				}
			}
			// n
			b'0'..=b'9' => {
				let (n, offset) = parse_num(bytes);
				if n > 365 {
					Err(Error::InvalidOrUnsupportedTzString)
				} else {
					Ok((TzDateRule::N(n as u16), offset))
				}
			}
			// Mm.w.d
			b'M' => {
				let mut total = 1;
				let (m, offset) = parse_num(get_or_invalid_tzstring(bytes, total..)?);
				total += offset;
				if offset == 0 || m < 1 || m > 12 || get_or_default(bytes, total) != b'.' {
					Err(Error::InvalidOrUnsupportedTzString)
				} else {
					// Increment for the '.'
					total += 1;
					let (w, offset) = parse_num(get_or_invalid_tzstring(bytes, total..)?);
					total += offset;
					if offset == 0 || w < 1 || w > 5 || get_or_default(bytes, total) != b'.' {
						Err(Error::InvalidOrUnsupportedTzString)
					} else {
						// Increment for the '.'
						total += 1;
						let (d, offset) = parse_num(get_or_invalid_tzstring(bytes, total..)?);
						total += offset;
						if offset == 0 || d > 6 {
							Err(Error::InvalidOrUnsupportedTzString)
						} else {
							Ok((TzDateRule::M(m as u8, w as u8, d as u8), total))
						}
					}
				}
			},
			_ => Err(Error::InvalidOrUnsupportedTzString)
		}
	}

	/// Convert this date rule into a timestamp for the given year.
	///
	/// # Examples
	///
	/// ```
	/// assert_eq!(TzDateRule::J(59).as_timestamp(2024), 1709078400);
	/// assert_eq!(TzDateRule::J(60).as_timestamp(2024), 1709251200);
	/// assert_eq!(TzDateRule::N(59).as_timestamp(2024), 1709164800);
	/// assert_eq!(TzDateRule::M(2, 5, 4).as_timestamp(2024), 1709164800);
	/// ```
	fn as_timestamp(&self, year: u16) -> i64 {
		match *self {
			TzDateRule::J(n) => timestamp_from_yd(year, n - 1, false),
			TzDateRule::N(n) => timestamp_from_yd(year, n, isleapyear(year)),
			TzDateRule::M(m, w, d) => {
				// Find the actual date from the m/w/d rule. To do this, we first figure out which weekday
				// the month starts on, then adjust the target weekday (d) to be relative to that (d'). From
				// there, it is a simple equation to find the wth weekday (7 * [w-1] + d'). Finding the last
				// wday is similarly simple: if the 5th weekday is greater than the number of days in the
				// month, subtract a week (7), otherwise keep it as-is.
				let wday = wday_from_ymd(year, m, 1);
				let wday = if d < wday { 7 + d - wday } else { d - wday };
				let w = w - 1;
				let day = if w < 4 {
					7 * w + wday + 1
				} else {
					// 7 * 4 + 1 = 29
					let v = 29 + wday;
					if v > days_per_month(year, m) {
						v - 7
					} else {
						v
					}
				};

				timestamp_from_ymd(year, m, day)
			},
		}
	}
}

/// A TZ string rule set.
///
/// The set consists of four values in two pairs, representing transition times to:
/// * Daylight savings time: date (1) and time (2)
/// * Standard time: date (3) and time (4)
///
/// Times (2, 4) are optional and default to 2am local time if missing.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct TzRule {
	/// Transition from standard time to daylight savings time (date & time)
	pub todst: (TzDateRule, i32),
	/// Transition from daylight savings time to standard time (date & time)
	pub fromdst: (TzDateRule, i32)
}

/// A TZ spec.
///
/// Specifies a standard time UTC offset and optional daylight savings time configuration.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct TzSpec {
	/// UTC offset for standard time, in seconds
	pub utoff: i32,
	/// Optional DST configuration (UTC offset in seconds and corresponding TZ rule set)
	pub dst: Option<(i32, TzRule)>
}

impl TzSpec {
	/// Parse a TZ spec from a TZ string.
	///
	/// Note that if the input slice is empty (`bytes.len() == 0`) this function returns `Ok(None)`
	/// rather than `Err(...)`.
	///
	/// # Errors
	///
	/// This function may return [`Error::InvalidOrUnsupportedTzString`] in the following cases:
	/// - `bytes` is not a POSIX-compliant TZ string
	/// - `bytes` uses an unsupported TZ string feature, for example names enclosed in '<...>'
	/// - `bytes` contains data *after* the TZ string
	///
	/// # Examples
	///
	/// ```
	/// assert_eq!(TzSpec::parse(b""), Ok(None));
	/// assert_eq!(TzSpec::parse(b"EST"), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse(b"EST5"), Ok(Some(TzSpec {
	/// 	utoff: -18000,
	/// 	dst: None
	/// })));
	/// assert_eq!(TzSpec::parse(b"XXX4YYY,J1/0,J365/25"), Ok(Some(TzSpec {
	/// 	utoff: -14400,
	/// 	dst: Some((
	/// 		-10800,
	/// 		TzRule {
	/// 			todst: (TzDateRule::J(1), 0),
	/// 			fromdst: (TzDateRule::J(365), 90000)
	/// 		}
	/// 	))
	/// })));
	/// assert_eq!(TzSpec::parse(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20"), Ok(Some(TzSpec {
	/// 	utoff: -16200,
	/// 	dst: Some((
	/// 		-24300,
	/// 		TzRule {
	/// 			todst: (TzDateRule::N(25), 11430),
	/// 			fromdst: (TzDateRule::N(280), -4800)
	/// 		}
	/// 	))
	/// })));
	/// ```
	fn parse(mut bytes: &[u8]) -> Result<Option<TzSpec>, Error> {
		if bytes.len() == 0 {
			return Ok(None);
		}

		// Read the standard timezone name
		let stdlen = bytes.iter().take_while(TzSpec::match_name).count();
		if stdlen == 0 {
			return Err(Error::InvalidOrUnsupportedTzString);
		}
		bytes = get_or_invalid_tzstring(bytes, stdlen..)?;

		// Read the standard time UTC offset
		let (utoff, offset) = TzSpec::parse_time(bytes, false)?;
		bytes = get_or_invalid_tzstring(bytes, offset..)?;

		// Read the optional DST timezone name
		let dstlen = bytes.iter().take_while(TzSpec::match_name).count();
		let dst = if dstlen == 0 {
			None
		} else {
			bytes = get_or_invalid_tzstring(bytes, dstlen..)?;

			// Read the optional DST offset
			let dstoff = if let Ok((tmpdstoff, offset)) = TzSpec::parse_time(bytes, false) {
				bytes = get_or_invalid_tzstring(bytes, offset..)?;
				tmpdstoff
			} else {
				// Default DST to 1 hour advancement. Subtract because TZ string offsets are subtracted
				// from UTC, i.e. EST5EDT -> (EST: UTC-5), (EDT: UTC-4)
				utoff - 3600
			};

			// Read required comma, since there need to be rules for transitions if DST is defined
			if get_or_default(bytes, 0) != b',' {
				return Err(Error::InvalidOrUnsupportedTzString);
			}
			bytes = get_or_invalid_tzstring(bytes, 1..)?;

			// Read the transition date rule for standard -> DST
			let (todstdate, offset) = TzDateRule::parse(bytes)?;
			bytes = get_or_invalid_tzstring(bytes, offset..)?;

			// Read the optional transition time for standard -> DST, defaulting to 2am
			let todsttime = match get_or_default(bytes, 0) {
				b'/' => {
					bytes = get_or_invalid_tzstring(bytes, 1..)?;
					let (t, offset) = TzSpec::parse_time(bytes, true)?;
					bytes = get_or_invalid_tzstring(bytes, offset..)?;
					t
				}
				_ => 7200
			};

			// Required comma to separate transition rules
			if get_or_default(bytes, 0) != b',' {
				return Err(Error::InvalidOrUnsupportedTzString);
			}
			bytes = get_or_invalid_tzstring(bytes, 1..)?;

			// Read the transition date rule for DST -> standard
			let (fromdstdate, offset) = TzDateRule::parse(bytes)?;
			bytes = get_or_invalid_tzstring(bytes, offset..)?;

			// Read the optional transition time for DST -> standard, defaulting to 2am
			let fromdsttime = match get_or_default(bytes, 0) {
				b'/' => {
					bytes = get_or_invalid_tzstring(bytes, 1..)?;
					let (t, offset) = TzSpec::parse_time(bytes, true)?;
					bytes = get_or_invalid_tzstring(bytes, offset..)?;
					t
				}
				_ => 7200
			};

			// Invert UTC offset, since we add the offset to UTC time to calculate local time, rather than
			// subtract as is done in TZ strings
			Some((-dstoff, TzRule {
				todst: (todstdate, todsttime),
				fromdst: (fromdstdate, fromdsttime)
			}))
		};

		// Ensure there's nothing left in the input
		if bytes.len() == 0 {
			// Invert UTC offset, since we add the offset to UTC time to calculate local time, rather than
			// subtract as is done in TZ strings
			Ok(Some(TzSpec {
				utoff: -utoff,
				dst
			}))
		} else {
			Err(Error::InvalidOrUnsupportedTzString)
		}
	}

	/// Match valid TZ string timezone name characters
	#[inline(always)]
	fn match_name(x: &&u8) -> bool {
		match x {
			b':' | b',' | b'-' | b'+' | b'\n' | 0 => false,
			b'0'..=b'9' => false,
			_ => true
		}
	}

	/// Parse a timestamp (hr:min:sec) from a TZ string.
	///
	/// On success, this function returns the signed timestamp converted to seconds and the number of
	/// characters consumed from the input to read the timestamp.
	///
	/// # Errors
	///
	/// This function will return [`Error::InvalidOrUnsupportedTzString`] if:
	/// - `bytes` is empty or does not contain a timestamp
	/// - The parsed timestamp components are out of bounds
	/// 	- In `extended` mode, hours +-167, else +-24
	/// 	- Minutes and seconds 0-59
	///
	/// # Examples
	///
	/// ```
	/// assert_eq!(TzSpec::parse_time(b"5", false), Ok((18000, 1)));
	/// assert_eq!(TzSpec::parse_time(b"-5", false), Ok((-18000, 2)));
	/// assert_eq!(TzSpec::parse_time(b"05:23:17", false), Ok((19397, 8)));
	/// assert_eq!(TzSpec::parse_time(b"30", true), Ok((108000, 2)));
	/// assert_eq!(TzSpec::parse_time(b"-30", true), Ok((-108000, 3)));
	/// assert_eq!(TzSpec::parse_time(b"", false), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse_time(b"5:", false), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse_time(b"25", false), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse_time(b"5:70", false), Err(Error::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse_time(b"200", true), Err(Error::InvalidOrUnsupportedTzString));
	/// ```
	fn parse_time(mut bytes: &[u8], extended: bool) -> Result<(i32, usize), Error> {
		let mut result;
		let mut index;

		let (sign, offset) = match get_or_invalid_tzstring(bytes, 0)? {
			b'-' => (-1, 1),
			b'+' => (1, 1),
			_ => (1, 0)
		};
		index = offset;
		bytes = get_or_invalid_tzstring(bytes, offset..)?;

		// Read hours (required)
		let (hours, offset) = parse_num(bytes);
		let limit = if extended { 167 } else { 24 };
		if offset == 0 || hours > limit {
			return Err(Error::InvalidOrUnsupportedTzString);
		}
		result = hours * 3600;
		index += offset;
		bytes = get_or_invalid_tzstring(bytes, offset..)?;

		// Read optional minutes and seconds
		for m in [60, 1] {
			match bytes.get(0).copied() {
				Some(b':') => bytes = get_or_invalid_tzstring(bytes, 1..)?,
				_ => break
			}

			let (minsec, offset) = parse_num(bytes);
			if offset == 0 || minsec > 59 {
				return Err(Error::InvalidOrUnsupportedTzString);
			}
			result += minsec * m;
			index += offset + 1;
			bytes = get_or_invalid_tzstring(bytes, offset..)?
		}

		Ok((sign * result as i32, index))
	}

	/// Get timezone info for a given moment in time.
	///
	/// # Examples
	///
	/// ```
	/// let spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap().unwrap();
	/// assert_eq!(spec.info(1710053999), TzInfo { utoff: -18000, isdst: false });
	/// assert_eq!(spec.info(1710054000), TzInfo { utoff: -14400, isdst: true });
	/// assert_eq!(spec.info(1730613599), TzInfo { utoff: -14400, isdst: true });
	/// assert_eq!(spec.info(1730613600), TzInfo { utoff: -18000, isdst: false });
	/// ```
	fn info(&self, time: i64) -> TzInfo {
		if let Some((dstoff, dstrule)) = self.dst {
			// Find the transition times for the timestamp's year. Note that we subtract UTC offsets
			// because we're moving from local time to UTC time, rather than UTC to local.
			let y = y_from_timestamp(time);
			let todst = dstrule.todst.0.as_timestamp(y) + dstrule.todst.1 as i64 - self.utoff as i64;
			let fromdst = dstrule.fromdst.0.as_timestamp(y) + dstrule.fromdst.1 as i64 - dstoff as i64;
			// Possibilities:
			// 1. time < todst < fromdst -> not dst
			// 2. todst <= time < fromdst -> dst
			// 3. todst < fromdst <= time -> not dst
			// 4. time < fromdst < todst -> dst
			// 5. fromdst <= time < todst -> not dst
			// 6. fromdst < todst <= time -> dst
			// 7. time < todst = fromdst -> dst      (equivalent to 4.)
			// 8. todst = fromdst <= time -> dst     (equivalent to 6.)
			let isdst = if todst < fromdst {
				todst <= time && time < fromdst
			} else {
				time < fromdst || todst <= time
			};
			TzInfo {
				utoff: if isdst { dstoff } else { self.utoff },
				isdst
			}
		} else {
			// If there's no DST config, this is really simple...
			TzInfo {
				utoff: self.utoff,
				isdst: false
			}
		}
	}
}

/// Timezone configuration.
///
/// This type allows you to convert UTC timestamps to calendar dates in the local timezone,
/// accounting for optional daylight savings time rules. It supports both fixed transition times
/// (as defined in TZif files) and computing transition times using (optional) TZ strings.
///
/// # Examples
///
/// ```
/// // Parsing a TZ string
/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
///
/// // Getting info for a given unix timestamp
/// let info = timezone.info(1723433665);
/// assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
///
/// // Getting the date for a given unix timestamp
/// let date = timezone.date(1723433665);
/// assert_eq!(date, Some(TmWithTzInfo {
/// 	tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
/// 	info: TzInfo { utoff: -25200, isdst: true }
/// }));
/// ```
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Timezone {
	/// Precomputed transition times and corresponding timezone info
	times: Box<[(i64, TzInfo)]>,
	/// TZ spec for computing additional transition times
	spec: Option<TzSpec>
}

impl Timezone {
	/// Get timezone info for a given moment in time.
	///
	/// This function first checks for precomputed transition times, falling back to a TZ rule only
	/// if there are no precomputed transition times or `time` is greater than or equal to the last
	/// precomputed transition time. If `time` is before the first precomputed transition time, this
	/// function assumes the timezone matches the first precomputed transition time. This is
	/// consistent with most timezone implementations.
	///
	/// Finally, if there are no precomputed transition times and no TZ rule, this function always
	/// returns the default [`TzInfo`]: `{ utoff: 0, isdst: false }`.
	///
	/// # Examples
	///
	/// ```
	/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(timezone.info(1723433665), TzInfo { utoff: -25200, isdst: true });
	/// ```
	pub fn info(&self, time: i64) -> TzInfo {
		// Check precomputed transition times
		let t = match self.times.binary_search_by_key(&time, |&(t, _)| t) {
			// Exact match, use it unless it points to the last time (which is not intended for use)
			Ok(t) => if t < self.times.len() - 1 { t } else { t + 1 },
			// Inexact match, use the previous
			Err(t) => if t < self.times.len() { t.saturating_sub(1) } else { t },
		};
		// Get the associated timezone info, or compute it if needed & possible
		self.times.get(t).map(|&(_, v)| v).unwrap_or_else(|| {
			match self.spec {
				Some(spec) => spec.info(time),
				None => TzInfo::default()
			}
		})
	}

	/// Get calendar date info for a given `time` in the specified timezone.
	///
	/// For invalid times (`time < 0`), this function returns `None`.
	///
	/// # Examples
	///
	/// ```
	/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(timezone.date(1723433665), Some(TmWithTzInfo {
	/// 	tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
	/// 	info: TzInfo { utoff: -25200, isdst: true }
	/// }));
	/// ```
	pub fn date(&self, time: i64) -> Option<TmWithTzInfo> {
		let info = self.info(time);

		if let Some(tm) = Tm::new(time + info.utoff as i64) {
			Some(TmWithTzInfo { tm, info })
		} else {
			None
		}
	}

	/// Get the set of unique UTC offsets (in seconds) in this timezone.
	///
	/// While it may seem like there can only be two offsets (standard and daylight savings time),
	/// it's possible for precomputed transition times to span over changes in DST rules. This may
	/// be rare, but do not assume there are only two possible offset values.
	pub fn offsets(&self) -> Vec<i32> {
		let mut r: Vec<i32> = Vec::with_capacity(8);
		// Closure to append only unique values
		let mut append = |v| {
			if !r.contains(&v) {
				r.push(v);
			}
		};

		// Append precomputed transition times
		for v in self.times.iter() {
			append(v.1.utoff);
		}

		// Append optional TZ spec times
		if let Some(spec) = self.spec {
			append(spec.utoff);
			if let Some((dst, _)) = spec.dst {
				append(dst);
			}
		}

		r
	}

	/// Get the [`TzSpec`] for this timezone, if specified.
	///
	/// Note that when set, this value is technically only valid for future dates/times, and may be
	/// invalid for prior dates if timezone or DST rules have changed in the past. For example, the US
	/// changed DST rules in 2007 from `M4.1.0,M10.5.0` to `M3.2.0,M11.1.0`. If using the currently
	/// valid `TzSpec`, any transition times computed before 2007 would be incorrect.
	pub fn spec(&self) -> Option<TzSpec> {
		self.spec
	}
}

/// Parse a byte slice containing TZif data
///
/// This function assumes the first 20 bytes of the TZif file have already been parsed and
/// excluded from `bytes`.
///
/// `T` determines whether transition times are treated as 4-byte (TZif version 1) or 8-byte
/// (TZif version 2+) signed integers. The only valid types are `i32` and `i64`.
///
/// `parse_spec` determines whether to try to read a TZ string from the end of the file
/// (TZif version 2+).
///
/// # Errors
///
/// Returns [`Error::InvalidTzFile`] if the TZif file is malformed, for example there is less data
/// in `bytes` than expected or transition times map to invalid transition type indices.
///
/// Returns [`Error::InvalidOrUnsupportedTzString`] if `parse_spec` is `true` and the TZ string is
/// invalid or uses unsupported features. This error does not occur if the TZ string is simply
/// empty.
fn parse_internal<T>(mut bytes: &[u8], parse_spec: bool) -> Result<Timezone, Error>
where T: ParseType
{
	let h = TzHeader::parse(bytes)?;
	bytes = get_or_invalid(bytes, 24..)?;

	// Get transition times
	let times = bytes.chunks_exact(size_of::<T>())
		             .take(h.timecnt as usize)
		             .map(|c| T::read(c));
	bytes = get_or_invalid(bytes, h.timecnt as usize * size_of::<T>()..)?;

	// Get transition time type indices (time -> type mapping)
	let type_indices = bytes.iter()
		                    .take(h.timecnt as usize)
		                    .copied();
	bytes = get_or_invalid(bytes, h.timecnt as usize..)?;

	// Get transition types
	let types: Box<[TzInfo]> = bytes.chunks_exact(6)
		                          .take(h.typecnt as usize)
		                          .map(|c|
		                          	TzInfo {
		                          		utoff: read_i32(&c[0..4]),
		                          		isdst: c[4] > 0
		                          	}
		                          )
		                          .collect();

	// Read optional TZ string
	let spec = if parse_spec {
		// Jump to the end of the file
		let offset = 6 * h.typecnt as usize
				   + h.charcnt as usize
				   + (4 + size_of::<T>()) * h.leapcnt as usize
				   + h.isstdcnt as usize
				   + h.isutcnt as usize;
		bytes = get_or_invalid(bytes, offset..)?;

		// TZ string is enclosed in newlines
		if get_or_default(bytes, 0) != b'\n' {
			return Err(Error::InvalidTzFile)
		}
		let (e, b) = get_or_invalid(bytes, 1..)?.split_last().ok_or(Error::InvalidTzFile)?;
		if *e != b'\n' {
			return Err(Error::InvalidTzFile)
		}

		// Parse the TZ string
		TzSpec::parse(b)?
	} else {
		None
	};

	// Create a timezone, mapping the transition times to types
	let mut t = Timezone {
		times: times.zip(type_indices)
	                .map_while(|(t, i)| Some((t.into(), *types.get(i as usize)?)))
	                .collect(),
		spec
	};

	// If an error was encountered above (i.e. a transition time maps to an invalid type index), then
	// map_while will exit early and the total count will be wrong
	if t.times.len() != h.timecnt as usize {
		return Err(Error::InvalidTzFile);
	} else if t.times.len() == 0 && t.spec.is_none() {
		// Special case where there are no precomputed transition times and no TZ string, but there is
		// at least one transition type. In that case, we can assume the first type applies to all
		// times. This is consistent with common timezone implementations.
		if types.len() > 0 {
			t.times = Box::new([(i64::MIN, types[0]), (i64::MAX, types[0])]);
		} else {
			return Err(Error::InvalidTzFile);
		}
	}

	Ok(t)
}

/// Parse a TZif file.
///
/// # Errors
///
/// May return the following errors:
/// - [`Error::FileReadError`] if the file could not be read
/// - [`Error::NotATzFile`] if the file does not begin with the 'TZif' magic bytes
/// - [`Error::UnsupportedVersion`] if the file version is not 1, 2, 3, or 4
/// - [`Error::InvalidTzFile`] if the file is not properly formatted
/// - [`Error::InvalidOrUnsupportedTzString`] if the optional TZ string is malformed
///
/// # Examples
///
/// ```
/// let timezone = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();
/// ```
pub fn parse_file<P>(file: P) -> Result<Timezone, Error>
where
	P: AsRef<Path>
{
	let bytes = fs::read(file)?;
	parse_bytes(bytes.as_slice())
}

/// Parse a byte slice containing a TZif file.
///
/// # Errors
///
/// May return the following errors:
/// - [`Error::NotATzFile`] if the file does not begin with the 'TZif' magic bytes
/// - [`Error::UnsupportedVersion`] if the file version is not 1, 2, 3, or 4
/// - [`Error::InvalidTzFile`] if the file is not properly formatted
/// - [`Error::InvalidOrUnsupportedTzString`] if the optional TZ string is malformed
pub fn parse_bytes(bytes: &[u8]) -> Result<Timezone, Error> {
	// Check for magic bytes
	if read_u32(get_or_invalid(bytes, 0..4)?) != 0x545a6966 {
		return Err(Error::NotATzFile);
	}

	// Check for version
	match get_or_invalid(bytes, 4)? {
		// Version 1
		0 => parse_internal::<i32>(get_or_invalid(bytes, 20..)?, false),
		// Versions 2, 3, 4
		50..=52 => {
			// Skip to the v2 header
			let h = TzHeader::parse(get_or_invalid(bytes, 20..)?)?;
			let offset = 5 * h.timecnt
					   + 6 * h.typecnt
					   + h.charcnt
					   + 8 * h.leapcnt
					   + h.isstdcnt
					   + h.isutcnt
					   + 64;
			parse_internal::<i64>(get_or_invalid(bytes, offset as usize..)?, true)
		},
		// Any other version is not supported (none at the time of this writing)
		v => Err(Error::UnsupportedVersion(*v))
	}
}

/// Parse a byte slice containing a TZ string.
///
/// This function does not precompute any transition times, so all calls to functions on the
/// returned timezone will compute transition times during the call.
///
/// # Errors
///
/// Returns [`Error::InvalidOrUnsupportedTzString`] if the TZ string is malformed
///
/// # Examples
///
/// ```
/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
/// let info = timezone.info(1723433665);
/// assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
/// ```
pub fn parse_tzstring(tzstring: &[u8]) -> Result<Timezone, Error> {
	Ok(Timezone {
		times: Box::new([]),
		spec: TzSpec::parse(tzstring)?
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::iter::from_fn;

	// Allow comparison for errors
	impl PartialEq for Error {
		fn eq(&self, other: &Self) -> bool {
			match (self, other) {
				(Error::FileReadError(l), Error::FileReadError(r)) => l.kind() == r.kind(),
				(Error::NotATzFile, Error::NotATzFile) => true,
				(Error::UnsupportedVersion(l), Error::UnsupportedVersion(r)) => l.eq(r),
				(Error::InvalidTzFile, Error::InvalidTzFile) => true,
				(Error::InvalidOrUnsupportedTzString, Error::InvalidOrUnsupportedTzString) => true,
				_ => false
			}
		}
	}

	#[test]
	fn tz_header() {
		assert_eq!(TzHeader::parse(b"\x00\x00\x00\x01\
									 \x00\x00\x00\x02\
									 \x00\x00\x00\x03\
									 \x00\x00\x00\x04\
									 \x00\x00\x00\x05\
									 \x00\x00\x00\x06"),
			Ok(TzHeader {
				isutcnt:1,
				isstdcnt: 2,
				leapcnt: 3,
				timecnt: 4,
				typecnt: 5,
				charcnt: 6
			})
		);
	}

	#[test]
	fn tz_spec_parse_time() {
		assert_eq!(TzSpec::parse_time(b"5", false), Ok((18000, 1)));
		assert_eq!(TzSpec::parse_time(b"-5", false), Ok((-18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05", false), Ok((18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05:23", false), Ok((19380, 5)));
		assert_eq!(TzSpec::parse_time(b"05:23:17", false), Ok((19397, 8)));
		assert_eq!(TzSpec::parse_time(b"30", true), Ok((108000, 2)));
		assert_eq!(TzSpec::parse_time(b"-30", true), Ok((-108000, 3)));

		assert_eq!(TzSpec::parse_time(b"", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"g", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5::", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5::0", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b":1", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"25", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:70", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"200", true), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"200:70", true), Err(Error::InvalidOrUnsupportedTzString));
	}

	#[test]
	fn tz_date_rule_parse() {
		assert_eq!(TzDateRule::parse(b"0"), Ok((TzDateRule::N(0), 1)));
		assert_eq!(TzDateRule::parse(b"5"), Ok((TzDateRule::N(5), 1)));
		assert_eq!(TzDateRule::parse(b"57"), Ok((TzDateRule::N(57), 2)));
		assert_eq!(TzDateRule::parse(b"578"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"366"), Err(Error::InvalidOrUnsupportedTzString));

		assert_eq!(TzDateRule::parse(b"J0"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"J1"), Ok((TzDateRule::J(1), 2)));
		assert_eq!(TzDateRule::parse(b"J5"), Ok((TzDateRule::J(5), 2)));
		assert_eq!(TzDateRule::parse(b"J57"), Ok((TzDateRule::J(57), 3)));
		assert_eq!(TzDateRule::parse(b"J578"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"J366"), Err(Error::InvalidOrUnsupportedTzString));

		assert_eq!(TzDateRule::parse(b"M1.2.3"), Ok((TzDateRule::M(1, 2, 3), 6)));
		assert_eq!(TzDateRule::parse(b"M12.5.6"), Ok((TzDateRule::M(12, 5, 6), 7)));
		assert_eq!(TzDateRule::parse(b"M13.5.6"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M12.6.6"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M12.5.7"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1.2."), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1.2"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1."), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M"), Err(Error::InvalidOrUnsupportedTzString));

		assert_eq!(TzDateRule::parse(b""), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1,2.3"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1.2,3"), Err(Error::InvalidOrUnsupportedTzString));
	}

	#[test]
	fn tz_date_rule_as_timestamp() {
		assert_eq!(TzDateRule::N(0).as_timestamp(2024), 1704067200);
		assert_eq!(TzDateRule::N(58).as_timestamp(2024), 1709078400);
		assert_eq!(TzDateRule::N(59).as_timestamp(2024), 1709164800);
		assert_eq!(TzDateRule::N(60).as_timestamp(2024), 1709251200);
		assert_eq!(TzDateRule::N(300).as_timestamp(2024), 1729987200);
		assert_eq!(TzDateRule::N(365).as_timestamp(2024), 1735603200);

		assert_eq!(TzDateRule::J(1).as_timestamp(2024), 1704067200);
		assert_eq!(TzDateRule::J(58).as_timestamp(2024), 1708992000);
		assert_eq!(TzDateRule::J(59).as_timestamp(2024), 1709078400);
		assert_eq!(TzDateRule::J(60).as_timestamp(2024), 1709251200);
		assert_eq!(TzDateRule::J(300).as_timestamp(2024), 1729987200);
		assert_eq!(TzDateRule::J(365).as_timestamp(2024), 1735603200);

		assert_eq!(TzDateRule::M(1, 1, 0).as_timestamp(2024), 1704585600);
		assert_eq!(TzDateRule::M(1, 2, 0).as_timestamp(2024), 1705190400);
		assert_eq!(TzDateRule::M(1, 3, 0).as_timestamp(2024), 1705795200);
		assert_eq!(TzDateRule::M(1, 4, 0).as_timestamp(2024), 1706400000);
		assert_eq!(TzDateRule::M(1, 5, 0).as_timestamp(2024), 1706400000);
		assert_eq!(TzDateRule::M(1, 1, 1).as_timestamp(2024), 1704067200);
		assert_eq!(TzDateRule::M(1, 2, 1).as_timestamp(2024), 1704672000);
		assert_eq!(TzDateRule::M(1, 3, 1).as_timestamp(2024), 1705276800);
		assert_eq!(TzDateRule::M(1, 4, 1).as_timestamp(2024), 1705881600);
		assert_eq!(TzDateRule::M(1, 5, 1).as_timestamp(2024), 1706486400);
		assert_eq!(TzDateRule::M(1, 1, 5).as_timestamp(2024), 1704412800);
		assert_eq!(TzDateRule::M(1, 2, 5).as_timestamp(2024), 1705017600);
		assert_eq!(TzDateRule::M(1, 3, 5).as_timestamp(2024), 1705622400);
		assert_eq!(TzDateRule::M(1, 4, 5).as_timestamp(2024), 1706227200);
		assert_eq!(TzDateRule::M(1, 5, 5).as_timestamp(2024), 1706227200);
		assert_eq!(TzDateRule::M(9, 1, 5).as_timestamp(2024), 1725580800);
		assert_eq!(TzDateRule::M(9, 2, 5).as_timestamp(2024), 1726185600);
		assert_eq!(TzDateRule::M(9, 3, 5).as_timestamp(2024), 1726790400);
		assert_eq!(TzDateRule::M(9, 4, 5).as_timestamp(2024), 1727395200);
		assert_eq!(TzDateRule::M(9, 5, 5).as_timestamp(2024), 1727395200);
	}

	#[test]
	fn tz_spec_parse() {
		assert_eq!(TzSpec::parse(b""), Ok(None));
		assert_eq!(TzSpec::parse(b"\n"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse(b"EST"), Err(Error::InvalidOrUnsupportedTzString));

		assert_eq!(TzSpec::parse(b"EST5"), Ok(Some(TzSpec {
			utoff: -18000,
			dst: None
		})));
		assert_eq!(TzSpec::parse(b"CET-1CEST,M3.5.0,M10.5.0/3"), Ok(Some(TzSpec {
			utoff: 3600,
			dst: Some((
				7200,
				TzRule {
					todst: (TzDateRule::M(3, 5, 0), 7200),
					fromdst: (TzDateRule::M(10, 5, 0), 10800)
				}
			))
		})));
		assert_eq!(TzSpec::parse(b"ABC-12DEF,M11.1.0,M1.2.1/147"), Ok(Some(TzSpec {
			utoff: 43200,
			dst: Some((
				46800,
				TzRule {
					todst: (TzDateRule::M(11, 1, 0), 7200),
					fromdst: (TzDateRule::M(1, 2, 1), 529200)
				}
			))
		})));
		assert_eq!(TzSpec::parse(b"IST-2IDT,M3.4.4/26,M10.5.0"), Ok(Some(TzSpec {
			utoff: 7200,
			dst: Some((
				10800,
				TzRule {
					todst: (TzDateRule::M(3, 4, 4), 93600),
					fromdst: (TzDateRule::M(10, 5, 0), 7200)
				}
			))
		})));
		assert_eq!(TzSpec::parse(b"XXX4YYY,J1/0,J365/25"), Ok(Some(TzSpec {
			utoff: -14400,
			dst: Some((
				-10800,
				TzRule {
					todst: (TzDateRule::J(1), 0),
					fromdst: (TzDateRule::J(365), 90000)
				}
			))
		})));
		assert_eq!(TzSpec::parse(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20"), Ok(Some(TzSpec {
			utoff: -16200,
			dst: Some((
				-24300,
				TzRule {
					todst: (TzDateRule::N(25), 11430),
					fromdst: (TzDateRule::N(280), -4800)
				}
			))
		})));

		assert_eq!(parse_tzstring(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20").unwrap().spec, Some(TzSpec {
			utoff: -16200,
			dst: Some((
				-24300,
				TzRule {
					todst: (TzDateRule::N(25), 11430),
					fromdst: (TzDateRule::N(280), -4800)
				}
			))
		}));
	}

	#[test]
	fn tz_spec_info() {
		let mut spec = TzSpec::parse(b"EST5").unwrap().unwrap();
		// Closure to create an iterator that iterates between Jan 1, 2024 and Dec 31, 2024, one day
		// at a time
		let create_iterator = || {
			let mut time = 1704092400;
			from_fn(move || {
				time += 86400;
				if time <= 1735632000 {
					Some(time)
				} else {
					None
				}
			})
		};
		for t in create_iterator() {
			assert_eq!(spec.info(t), TzInfo {
				utoff: -18000,
				isdst: false
			}, "time: {}", t);
		}

		spec = TzSpec::parse(b"EST5EDT,70,230").unwrap().unwrap();
		for t in create_iterator() {
			assert_eq!(spec.info(t),
				if t < 1710140400 || t >= 1723960800 {
					TzInfo {
						utoff: -18000,
						isdst: false
					}
				} else {
					TzInfo {
						utoff: -14400,
						isdst: true
					}
				}, "time: {}", t);
		}
		assert_eq!(spec.info(1710140399), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1710140399);
		assert_eq!(spec.info(1710140400), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1710140400);
		assert_eq!(spec.info(1723960799), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1723960799);
		assert_eq!(spec.info(1723960800), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1723960800);

		spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap().unwrap();
		for t in create_iterator() {
			assert_eq!(spec.info(t),
				if t < 1710054000 || t >= 1730613600 {
					TzInfo {
						utoff: -18000,
						isdst: false
					}
				} else {
					TzInfo {
						utoff: -14400,
						isdst: true
					}
				}, "time: {}", t);
		}
		assert_eq!(spec.info(1710053999), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1710053999);
		assert_eq!(spec.info(1710054000), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1710054000);
		assert_eq!(spec.info(1730613599), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1730613599);
		assert_eq!(spec.info(1730613600), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1730613600);

		spec = TzSpec::parse(b"EST5EDT,M3.2.0/4,M11.1.0/-2").unwrap().unwrap();
		for t in create_iterator() {
			assert_eq!(spec.info(t),
				if t < 1710061200 || t >= 1730599200 {
					TzInfo {
						utoff: -18000,
						isdst: false
					}
				} else {
					TzInfo {
						utoff: -14400,
						isdst: true
					}
				}, "time: {}", t);
		}
		assert_eq!(spec.info(1710061199), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1710061199);
		assert_eq!(spec.info(1710061200), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1710061200);
		assert_eq!(spec.info(1730599199), TzInfo { utoff: -14400, isdst: true }, "time: {}", 1730599199);
		assert_eq!(spec.info(1730599200), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1730599200)
	}

	#[test]
	fn timezone_info() {
		let mut tz = Timezone {
			times: Box::new([]),
			spec: None
		};
		assert_eq!(tz.info(1704672000), TzInfo { utoff: 0, isdst: false });

		tz.spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(tz.info(1704672000), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710053999), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710054000), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613600), TzInfo { utoff: -18000, isdst: false });

		tz.times = Box::new([(1710054000, TzInfo { utoff: -20000, isdst: false }),
		 					 (1720054000, TzInfo { utoff: -10000, isdst: true }),
							 (1730054000, TzInfo { utoff: -5000, isdst: false })]);
		assert_eq!(tz.info(1704672000), TzInfo { utoff: -20000, isdst: false });
		assert_eq!(tz.info(1710053999), TzInfo { utoff: -20000, isdst: false });
		assert_eq!(tz.info(1720054001), TzInfo { utoff: -10000, isdst: true });
		assert_eq!(tz.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613600), TzInfo { utoff: -18000, isdst: false });
	}

	#[test]
	fn timezone_offsets() {
		let mut tz = Timezone {
			times: Box::new([]),
			spec: None
		};

		assert_eq!(tz.offsets(), vec!());

		tz.spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(tz.offsets(), vec![-18000, -14400]);

		tz.times = Box::new([(1710054000, TzInfo { utoff: -20000, isdst: false }),
		 					 (1720054000, TzInfo { utoff: -10000, isdst: true }),
							 (1730054000, TzInfo { utoff: -20000, isdst: false }),
							 (1740054000, TzInfo { utoff: -10000, isdst: true }),
							 (1750054000, TzInfo { utoff: -5000, isdst: false })]);
		assert_eq!(tz.offsets(), vec![-20000, -10000, -5000, -18000, -14400]);
	}

	#[test]
	fn module_doctest() {
		// Parsing a file
		let timezone1 = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();

		// Parsing a TZ string
		let timezone2 = parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").unwrap();

		// Getting info for a given unix timestamp
		let info = timezone1.info(1723433665);
		assert_eq!(info, TzInfo { utoff: -25200, isdst: true });

		// Getting the date for a given unix timestamp
		let date = timezone2.date(1723433665);
		assert_eq!(date, Some(TmWithTzInfo {
			tm: Tm { sec: 25, min: 34, hour: 23, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
			info: TzInfo { utoff: -14400, isdst: true }
		}));


		// Documentation for read_u32
		assert_eq!(read_u32(&[0, 0, 0, 1]), 1);
		assert_eq!(read_u32(&[255, 255, 255, 255]), 4294967295);

		// Documentation for read_i32
		assert_eq!(read_i32(&[0, 0, 0, 1]), 1);
		assert_eq!(read_i32(&[255, 255, 255, 255]), -1);

		// Documentation for read_i64
		assert_eq!(read_i64(&[0, 0, 0, 0, 0, 0, 0, 1]), 1);
		assert_eq!(read_i64(&[255, 255, 255, 255, 255, 255, 255, 255]), -1);

		// Documentation for parse_num
		assert_eq!(parse_num(b"15x"), (15, 2));
		assert_eq!(parse_num(b"x15"), (0, 0));

		// Documentation for TzDateRule::parse
		assert_eq!(TzDateRule::parse(b"57"), Ok((TzDateRule::N(57), 2)));
		assert_eq!(TzDateRule::parse(b"578"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"J57"), Ok((TzDateRule::J(57), 3)));
		assert_eq!(TzDateRule::parse(b"J0"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"J366"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M12.5.6"), Ok((TzDateRule::M(12, 5, 6), 7)));
		assert_eq!(TzDateRule::parse(b"M12.5.6asd"), Ok((TzDateRule::M(12, 5, 6), 7)));
		assert_eq!(TzDateRule::parse(b"M12.5.asd"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M13.5.6"), Err(Error::InvalidOrUnsupportedTzString));

		// Documentation for TzDateRule::as_timestamp
		assert_eq!(TzDateRule::N(59).as_timestamp(2024), 1709164800);
		assert_eq!(TzDateRule::J(59).as_timestamp(2024), 1709078400);
		assert_eq!(TzDateRule::J(60).as_timestamp(2024), 1709251200);
		assert_eq!(TzDateRule::M(2, 5, 4).as_timestamp(2024), 1709164800);

		// Documentation for TzSpec::parse
		assert_eq!(TzSpec::parse(b""), Ok(None));
		assert_eq!(TzSpec::parse(b"EST"), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse(b"EST5"), Ok(Some(TzSpec {
			utoff: -18000,
			dst: None
		})));
		assert_eq!(TzSpec::parse(b"XXX4YYY,J1/0,J365/25"), Ok(Some(TzSpec {
			utoff: -14400,
			dst: Some((
				-10800,
				TzRule {
					todst: (TzDateRule::J(1), 0),
					fromdst: (TzDateRule::J(365), 90000)
				}
			))
		})));
		assert_eq!(TzSpec::parse(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20"), Ok(Some(TzSpec {
			utoff: -16200,
			dst: Some((
				-24300,
				TzRule {
					todst: (TzDateRule::N(25), 11430),
					fromdst: (TzDateRule::N(280), -4800)
				}
			))
		})));

		// Documentation for TzSpec::parse_time
		assert_eq!(TzSpec::parse_time(b"5", false), Ok((18000, 1)));
		assert_eq!(TzSpec::parse_time(b"-5", false), Ok((-18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05:23:17", false), Ok((19397, 8)));
		assert_eq!(TzSpec::parse_time(b"30", true), Ok((108000, 2)));
		assert_eq!(TzSpec::parse_time(b"-30", true), Ok((-108000, 3)));
		assert_eq!(TzSpec::parse_time(b"", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"25", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:70", false), Err(Error::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"200", true), Err(Error::InvalidOrUnsupportedTzString));

		// Documentation for TzSpec::info
		let spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap().unwrap();
		assert_eq!(spec.info(1710053999), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(spec.info(1710054000), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(spec.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(spec.info(1730613600), TzInfo { utoff: -18000, isdst: false });

		// Documentation to Timezone
		// Parsing a TZ string
		let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();

		// Getting info for a given unix timestamp
		let info = timezone.info(1723433665);
		assert_eq!(info, TzInfo { utoff: -25200, isdst: true });

		// Getting the date for a given unix timestamp
		let date = timezone.date(1723433665);
		assert_eq!(date, Some(TmWithTzInfo {
			tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
			info: TzInfo { utoff: -25200, isdst: true }
		}));
	}
}
