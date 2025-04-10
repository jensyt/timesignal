//! Support for parsing TZ strings.
//!
//! This module supports parsing and generating [`TzInfo`] for [TZ strings]. Most extended POSIX
//! features are supported, except:
//! - **Special TZ names**. The POSIX specification allows special timezone names enclosed in <...>
//!   which are not fully supported in this module. For example, "<5>6" represents a timezone named
//!   "5" with an offset of UTC-6. This specification will fail in this module. As an alternative,
//!   consider "FIVE6" which will work.
//! - **Accessing timezone names**. This module does not save timezone names.
//!
//! [TZ strings]: https://www.gnu.org/software/libc/manual/html_node/TZ-Variable.html
//!
//! # Examples
//!
//! ```
//! # use time::{time::Tm, tz::{parse_tzstring, parse_tzstring_const, TzInfo, TmWithTzInfo}};
//! // Parsing a TZ string at runtime
//! let timezone = parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
//!
//! // Getting info for a given unix timestamp
//! let info = timezone.info(1723433665);
//! assert_eq!(info, TzInfo { utoff: -14400, isdst: true });
//!
//! // Alternatively, use compile-time evaluation
//! let timezone = parse_tzstring_const!(b"EST5EDT,M3.2.0,M11.1.0");
//!
//! // Getting the date for a given unix timestamp
//! let date = timezone.date(1723433665);
//! assert_eq!(date, Some(TmWithTzInfo {
//! 	tm: Tm { sec: 25, min: 34, hour: 23, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
//! 	info: TzInfo { utoff: -14400, isdst: true }
//! }));
//! ```

use core::{error, fmt, ops::RangeFrom};
use crate::time::{
	days_per_month,
	isleapyear,
	timestamp_from_yd,
	timestamp_from_ymd,
	wday_from_ymd,
	y_from_timestamp
};
use super::{get_first_or_default, Timezone, TzInfo};

/// The error type for parsing timezone data (TZ strings).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TzStringError {
	/// Empty input.
	MissingTzString,
	/// Missing a required [`TzDateRule`].
	MissingTzDateRule,
	/// A date component of a [`TzDateRule`] was out of range.
	DateOutOfRange,
	/// A time component was out of range.
	TimeOutOfRange,
	/// The [`TzDateRule`] had an invalid specifier (only 'J', 'M', or '' are allowed).
	InvalidTzDateRuleSpecifier,
	/// Found unexpected bytes after a valid [`TzSpec`].
	UnexpectedInput,
	/// The TZ string is invalid or unsupported.
	InvalidOrUnsupportedTzString
}

impl fmt::Display for TzStringError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			TzStringError::MissingTzString => f.write_str("Missing TZ string"),
			TzStringError::MissingTzDateRule => f.write_str("Missing TZ date rule"),
			TzStringError::DateOutOfRange => f.write_str("Date component out of range"),
			TzStringError::TimeOutOfRange => f.write_str("Time component out of range"),
			TzStringError::InvalidTzDateRuleSpecifier => f.write_str("Invalid date rule"),
			TzStringError::UnexpectedInput => f.write_str("Unexpected input at end of TZ string"),
			TzStringError::InvalidOrUnsupportedTzString => f.write_str("Invalid TZ string")
		}
	}
}

impl error::Error for TzStringError {}

/// Get first byte, if valid, or return [`TzStringError::InvalidOrUnsupportedTzString`].
#[inline(always)]
const fn get_first_or_invalid(bytes: &[u8]) -> Result<u8, TzStringError> {
	match bytes.first() {
		Some(v) => Ok(*v),
		None => Err(TzStringError::InvalidOrUnsupportedTzString)
	}
}

/// Get a given index, if valid, or return [`TzStringError::InvalidOrUnsupportedTzString`].
#[inline(always)]
const fn get_or_invalid_range(bytes: &[u8], index: RangeFrom<usize>) -> Result<&[u8], TzStringError> {
	match bytes.split_at_checked(index.start) {
		Some((_, v)) => Ok(v),
		None => Err(TzStringError::InvalidOrUnsupportedTzString)
	}
}

/// Emulate the ? operator in const functions
macro_rules! throw {
	($expr:expr) => {
		match $expr {
			Ok(v) => v,
			Err(e) => return Err(e)
		}
	};
}

/// Parse an integer from a byte slice.
///
/// Reads as many digits [0-9] as are available and returns the parsed integer and the number of
/// digits parsed. If no digits are available, either because the `bytes` is empty or because the
/// first byte is not a digit in the range [0-9] then this function returns `(0, 0)`.
///
/// # Examples
///
/// ```ignore
/// assert_eq!(parse_num(b"15x"), (15, 2));
/// assert_eq!(parse_num(b"x15"), (0, 0));
/// ```
const fn parse_num(bytes: &[u8]) -> (u32, usize) {
	let mut i = 0;
	let mut r: u32 = 0;
	let len = bytes.len();
	while i < len {
		match bytes[i] {
			v @ b'0'..=b'9' => {
				r = match r.checked_mul(10) {
					Some(x) => match x.checked_add((v - b'0') as u32) {
						Some(v) => v,
						None => return (u32::MAX, i)
					},
					None => return (u32::MAX, i)
				};
			}
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
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TzDateRule {
	/// 'J`n`' where `n` is the Julian day between 1 and 365. Leap days are ignored, so day 60 is
	/// always March 1st.
	J(u16),
	/// '`n`' where `n` is the Julian day between 0 and 365. Leap day is counted in leap years, so
	/// day 60 is March 1st in leap years but March 2nd in non-leap years.
	N(u16),
	/// 'M`m`.`w`.`d`' where `m` is the month number (1-12), `d` is the day of week (0-6 =>
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
	/// May return the following errors:
	/// - [`TzStringError::MissingTzDateRule`] if `bytes` is zero length
	/// - [`TzStringError::InvalidOrUnsupportedTzString`] if the input is not a valid TZ date string
	/// - [`TzStringError::DateOutOfRange`] if a date component is out of the allowable range
	/// - [`TzStringError::InvalidTzDateRuleSpecifier`] if the first character isn't `'J'`, `'M'`, or
	///   a number (`0-9`).
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::{TzStringError, TzDateRule};
	/// assert_eq!(TzDateRule::parse(b"57"), Ok((TzDateRule::N(57), 2)));
	/// assert_eq!(TzDateRule::parse(b"578"), Err(TzStringError::DateOutOfRange));
	/// assert_eq!(TzDateRule::parse(b"J57"), Ok((TzDateRule::J(57), 3)));
	/// assert_eq!(TzDateRule::parse(b"J0"), Err(TzStringError::DateOutOfRange));
	/// assert_eq!(TzDateRule::parse(b"J366"), Err(TzStringError::DateOutOfRange));
	/// assert_eq!(TzDateRule::parse(b"M12.5.6"), Ok((TzDateRule::M(12, 5, 6), 7)));
	/// assert_eq!(TzDateRule::parse(b"M12.5.6asd"), Ok((TzDateRule::M(12, 5, 6), 7)));
	/// assert_eq!(TzDateRule::parse(b"M12.5.asd"), Err(TzStringError::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzDateRule::parse(b"M13.5.6"), Err(TzStringError::DateOutOfRange));
	/// ```
	pub const fn parse(bytes: &[u8]) -> Result<(TzDateRule, usize), TzStringError> {
		if bytes.len() == 0 {
			return Err(TzStringError::MissingTzDateRule)
		}

		// Indexing can't panic because of zero-size check above
		match bytes[0] {
			// Jn
			b'J' => {
				let (n, offset) = parse_num(throw!(get_or_invalid_range(bytes, 1..)));
				if n == 0 || n > 365 {
					Err(TzStringError::DateOutOfRange)
				} else {
					// Add 1 to offset because of the 'J'
					Ok((TzDateRule::J(n as u16), offset + 1))
				}
			}
			// n
			b'0'..=b'9' => {
				let (n, offset) = parse_num(bytes);
				if n > 365 {
					Err(TzStringError::DateOutOfRange)
				} else {
					Ok((TzDateRule::N(n as u16), offset))
				}
			}
			// Mm.w.d
			b'M' => {
				let mut total = 1;
				let (m, offset) = parse_num(throw!(get_or_invalid_range(bytes, total..)));
				total += offset;

				let mut b = throw!(get_or_invalid_range(bytes, total..));
				if offset == 0 || get_first_or_default(b) != b'.' {
					Err(TzStringError::InvalidOrUnsupportedTzString)
				} else if m < 1 || m > 12 {
					Err(TzStringError::DateOutOfRange)
				} else {
					// Increment for the '.'
					total += 1;
					let (w, offset) = parse_num(throw!(get_or_invalid_range(bytes, total..)));
					total += offset;

					b = throw!(get_or_invalid_range(bytes, total..));
					if offset == 0 || get_first_or_default(b) != b'.' {
						Err(TzStringError::InvalidOrUnsupportedTzString)
					} else if w < 1 || w > 5 {
						Err(TzStringError::DateOutOfRange)
					} else {
						// Increment for the '.'
						total += 1;
						let (d, offset) = parse_num(throw!(get_or_invalid_range(bytes, total..)));
						total += offset;

						if offset == 0 {
							Err(TzStringError::InvalidOrUnsupportedTzString)
						} else if d > 6 {
							Err(TzStringError::DateOutOfRange)
						} else {
							Ok((TzDateRule::M(m as u8, w as u8, d as u8), total))
						}
					}
				}
			},
			_ => Err(TzStringError::InvalidTzDateRuleSpecifier)
		}
	}

	/// Convert this date rule into a timestamp for the given year.
	///
	/// # Panics
	///
	/// This function panics in debug mode if the [`TzDateRule`] is cofigured with ranges outside
	/// those stated in the documentation.
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::TzDateRule;
	/// assert_eq!(TzDateRule::J(59).as_timestamp(2024), 1709078400);
	/// assert_eq!(TzDateRule::J(60).as_timestamp(2024), 1709251200);
	/// assert_eq!(TzDateRule::N(59).as_timestamp(2024), 1709164800);
	/// assert_eq!(TzDateRule::M(2, 5, 4).as_timestamp(2024), 1709164800);
	/// ```
	pub fn as_timestamp(&self, year: u16) -> i64 {
		match *self {
			TzDateRule::J(n) => {
				debug_assert!(1 <= n && n <= 365);
				timestamp_from_yd(year, n - 1, false)
			},
			TzDateRule::N(n) => {
				debug_assert!(n <= 365);
				timestamp_from_yd(year, n, isleapyear(year))
			},
			TzDateRule::M(m, w, d) => {
				debug_assert!(1 <= m && m <= 12);
				debug_assert!(1 <= w && w <= 5);
				debug_assert!(d <= 6);
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
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TzRule {
	/// Transition from standard time to daylight savings time (date & time)
	pub todst: (TzDateRule, i32),
	/// Transition from daylight savings time to standard time (date & time)
	pub fromdst: (TzDateRule, i32)
}

/// A TZ spec.
///
/// Specifies a standard time UTC offset and optional daylight savings time configuration.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TzSpec {
	/// UTC offset for standard time, in seconds
	pub utoff: i32,
	/// Optional DST configuration (UTC offset in seconds and corresponding TZ rule set)
	pub dst: Option<(i32, TzRule)>
}

impl TzSpec {
	/// Parse a TZ spec from a TZ string.
	///
	/// # Errors
	///
	/// This function may return [`TzStringError`] in the following cases:
	/// - `bytes.len() == 0`
	/// - `bytes` is not a POSIX-compliant TZ string
	/// - `bytes` uses an unsupported TZ string feature, for example names enclosed in '<...>'
	/// - `bytes` contains data *after* the TZ string
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::{TzSpec, TzDateRule, TzRule, TzStringError};
	/// assert_eq!(TzSpec::parse(b""), Err(TzStringError::MissingTzString));
	/// assert_eq!(TzSpec::parse(b"EST"), Err(TzStringError::InvalidOrUnsupportedTzString));
	/// assert_eq!(TzSpec::parse(b"EST5"), Ok(TzSpec {
	/// 	utoff: -18000,
	/// 	dst: None
	/// }));
	/// assert_eq!(TzSpec::parse(b"XXX4YYY,J1/0,J365/25"), Ok(TzSpec {
	/// 	utoff: -14400,
	/// 	dst: Some((
	/// 		-10800,
	/// 		TzRule {
	/// 			todst: (TzDateRule::J(1), 0),
	/// 			fromdst: (TzDateRule::J(365), 90000)
	/// 		}
	/// 	))
	/// }));
	/// assert_eq!(TzSpec::parse(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20"), Ok(TzSpec {
	/// 	utoff: -16200,
	/// 	dst: Some((
	/// 		-24300,
	/// 		TzRule {
	/// 			todst: (TzDateRule::N(25), 11430),
	/// 			fromdst: (TzDateRule::N(280), -4800)
	/// 		}
	/// 	))
	/// }));
	/// ```
	pub const fn parse(mut bytes: &[u8]) -> Result<TzSpec, TzStringError> {
		if bytes.len() == 0 {
			return Err(TzStringError::MissingTzString);
		}

		// Read the standard timezone name
		let stdlen = TzSpec::match_name(bytes);
		if stdlen == 0 {
			return Err(TzStringError::InvalidOrUnsupportedTzString);
		}
		bytes = throw!(get_or_invalid_range(bytes, stdlen..));

		// Read the standard time UTC offset
		let (utoff, offset) = throw!(TzSpec::parse_time(bytes, false));
		bytes = throw!(get_or_invalid_range(bytes, offset..));

		// Read the optional DST timezone name
		let dstlen = TzSpec::match_name(bytes);
		let dst = if dstlen == 0 {
			None
		} else {
			bytes = throw!(get_or_invalid_range(bytes, dstlen..));

			// Read the optional DST offset
			let dstoff = if let Ok((tmpdstoff, offset)) = TzSpec::parse_time(bytes, false) {
				bytes = throw!(get_or_invalid_range(bytes, offset..));
				tmpdstoff
			} else {
				// Default DST to 1 hour advancement. Subtract because TZ string offsets are subtracted
				// from UTC, i.e. EST5EDT -> (EST: UTC-5), (EDT: UTC-4)
				utoff - 3600
			};

			// Read required comma, since there need to be rules for transitions if DST is defined
			if get_first_or_default(bytes) != b',' {
				return Err(TzStringError::MissingTzDateRule);
			}
			bytes = throw!(get_or_invalid_range(bytes, 1..));

			// Read the transition date rule for standard -> DST
			let (todstdate, offset) = throw!(TzDateRule::parse(bytes));
			bytes = throw!(get_or_invalid_range(bytes, offset..));

			// Read the optional transition time for standard -> DST, defaulting to 2am
			let todsttime = match get_first_or_default(bytes) {
				b'/' => {
					bytes = throw!(get_or_invalid_range(bytes, 1..));
					let (t, offset) = throw!(TzSpec::parse_time(bytes, true));
					bytes = throw!(get_or_invalid_range(bytes, offset..));
					t
				}
				_ => 7200
			};

			// Required comma to separate transition rules
			if get_first_or_default(bytes) != b',' {
				return Err(TzStringError::MissingTzDateRule);
			}
			bytes = throw!(get_or_invalid_range(bytes, 1..));

			// Read the transition date rule for DST -> standard
			let (fromdstdate, offset) = throw!(TzDateRule::parse(bytes));
			bytes = throw!(get_or_invalid_range(bytes, offset..));

			// Read the optional transition time for DST -> standard, defaulting to 2am
			let fromdsttime = match get_first_or_default(bytes) {
				b'/' => {
					bytes = throw!(get_or_invalid_range(bytes, 1..));
					let (t, offset) = throw!(TzSpec::parse_time(bytes, true));
					bytes = throw!(get_or_invalid_range(bytes, offset..));
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
			Ok(TzSpec {
				utoff: -utoff,
				dst
			})
		} else {
			Err(TzStringError::UnexpectedInput)
		}
	}

	/// Match valid TZ string timezone name characters
	const fn match_name(bytes: &[u8]) -> usize {
		let mut i = 0;
		let len = bytes.len();
		while i < len {
			match bytes[i] {
				b':' | b',' | b'-' | b'+' | b'\n' | 0 => break,
				b'0'..=b'9' => break,
				_ => i += 1
			}
		}
		i
	}

	/// Parse a timestamp (hr:min:sec) from a TZ string.
	///
	/// On success, this function returns the signed timestamp converted to seconds and the number of
	/// characters consumed from the input to read the timestamp.
	///
	/// # Errors
	///
	/// Returns [`TzStringError::InvalidOrUnsupportedTzString`] if `bytes` is empty or does not
	/// contain a timestamp.
	///
	/// Returns [`TzStringError::TimeOutOfRange`] if the parsed timestamp components are out of bounds
	/// - In `extended` mode, hours +-167, else +-24
	/// - Minutes and seconds 0-59
	///
	/// # Examples
	///
	/// ```ignore
	/// # use time::tz::{TzSpec, Error};
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
	const fn parse_time(mut bytes: &[u8], extended: bool) -> Result<(i32, usize), TzStringError> {
		let mut result;
		let mut index;

		let (sign, offset) = match throw!(get_first_or_invalid(bytes)) {
			b'-' => (-1, 1),
			b'+' => (1, 1),
			_ => (1, 0)
		};
		index = offset;
		bytes = throw!(get_or_invalid_range(bytes, offset..));

		// Read hours (required)
		let (hours, offset) = parse_num(bytes);
		let limit = if extended { 167 } else { 24 };
		if offset == 0 {
			return Err(TzStringError::InvalidOrUnsupportedTzString);
		} else if hours > limit {
			return Err(TzStringError::TimeOutOfRange);
		}
		result = hours * 3600;
		index += offset;
		bytes = throw!(get_or_invalid_range(bytes, offset..));

		// Read optional minutes and seconds
		let mut m = 60;
		while m > 0 {
			match get_first_or_default(bytes) {
				b':' => bytes = throw!(get_or_invalid_range(bytes, 1..)),
				_ => break
			}

			let (minsec, offset) = parse_num(bytes);
			if offset == 0 {
				return Err(TzStringError::InvalidOrUnsupportedTzString);
			} else if minsec > 59 {
				return Err(TzStringError::TimeOutOfRange);
			}
			result += minsec * m;
			index += offset + 1;
			bytes = throw!(get_or_invalid_range(bytes, offset..));
			m /= 60;
		}

		Ok((sign * result as i32, index))
	}

	/// Get timezone info for a given moment in time.
	///
	/// # Panics
	///
	/// This function may panic in debug mode if the [`TzSpec`] is configured with values outside of
	/// their stated ranges. Note that using the return value of [`TzSpec::parse`] should never panic.
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::{TzSpec, TzInfo};
	/// let spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(spec.info(1710053999), TzInfo { utoff: -18000, isdst: false });
	/// assert_eq!(spec.info(1710054000), TzInfo { utoff: -14400, isdst: true });
	/// assert_eq!(spec.info(1730613599), TzInfo { utoff: -14400, isdst: true });
	/// assert_eq!(spec.info(1730613600), TzInfo { utoff: -18000, isdst: false });
	/// ```
	pub fn info(&self, time: i64) -> TzInfo {
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

/// Parse a constant byte slice containing a TZ string.
///
/// # Panics
///
/// This macro performs compile-time evaluation of the input and panics if [`TzSpec::parse`]
/// returns any of the [`TzStringError`] variants.
///
/// # Examples
/// ```
/// # use time::tz::parse_tzstring_const;
/// // This call will not panic at compile time and will guarantee a valid Timezone
/// let _tz = parse_tzstring_const!(b"CET-1CEST,M3.5.0,M10.5.0/3");
/// ```
///
/// ```compile_fail
/// // The following line will panic at compile time with error "Date component out of range"
/// let _tz = parse_tzstring_const!(b"CET-1CEST,M35.5.0,M10.5.0/3");
/// // The issue is here ------------------------^^
/// ```
#[macro_export]
macro_rules! parse_tzstring_const {
	($str:literal) => {
		$crate::tz::Timezone::from(const {
			match $crate::tz::TzSpec::parse($str) {
				Ok(v) => v,
				Err($crate::tz::TzStringError::MissingTzString) => panic!("Missing TZ string"),
				Err($crate::tz::TzStringError::MissingTzDateRule) => panic!("Missing TZ date rule"),
				Err($crate::tz::TzStringError::DateOutOfRange) => panic!("Date component out of range"),
				Err($crate::tz::TzStringError::TimeOutOfRange) => panic!("Time component out of range"),
				Err($crate::tz::TzStringError::InvalidTzDateRuleSpecifier) => panic!("Invalid date rule"),
				Err($crate::tz::TzStringError::UnexpectedInput) => panic!("Unexpected input at end of TZ string"),
				Err($crate::tz::TzStringError::InvalidOrUnsupportedTzString) => panic!("Invalid TZ string")
			}
		})
	}
}
pub use parse_tzstring_const;

/// Parse a byte slice containing a TZ string.
///
/// When parsing constant TZ strings known at compile-time, prefer [`parse_tzstring_const`] which
/// will evaluate the TZ string and give a compiler error if it is invalid.
///
/// # Errors
///
/// Returns [`TzStringError`] if the TZ string is malformed.
///
/// # Examples
///
/// ```
/// # use time::tz::{parse_tzstring, TzInfo};
/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
/// let info = timezone.info(1723433665);
/// assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
/// ```
pub fn parse_tzstring(tzstring: &[u8]) -> Result<Timezone, TzStringError> {
	TzSpec::parse(tzstring).map(Timezone::from)
}

#[cfg(test)]
mod tests {
	use super::*;
	use core::iter::from_fn;

	#[test]
	fn tz_spec_parse_time() {
		assert_eq!(TzSpec::parse_time(b"5", false), Ok((18000, 1)));
		assert_eq!(TzSpec::parse_time(b"-5", false), Ok((-18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05", false), Ok((18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05:23", false), Ok((19380, 5)));
		assert_eq!(TzSpec::parse_time(b"05:23:17", false), Ok((19397, 8)));
		assert_eq!(TzSpec::parse_time(b"30", true), Ok((108000, 2)));
		assert_eq!(TzSpec::parse_time(b"-30", true), Ok((-108000, 3)));

		assert_eq!(TzSpec::parse_time(b"", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"g", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5::", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5::0", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b":1", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"25", false), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"5:70", false), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"200", true), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"200:70", true), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"4294967296", true), Err(TzStringError::TimeOutOfRange));
	}

	#[test]
	fn tz_date_rule_parse() {
		assert_eq!(TzDateRule::parse(b"0"), Ok((TzDateRule::N(0), 1)));
		assert_eq!(TzDateRule::parse(b"5"), Ok((TzDateRule::N(5), 1)));
		assert_eq!(TzDateRule::parse(b"57"), Ok((TzDateRule::N(57), 2)));
		assert_eq!(TzDateRule::parse(b"578"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"366"), Err(TzStringError::DateOutOfRange));

		assert_eq!(TzDateRule::parse(b"J0"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"J1"), Ok((TzDateRule::J(1), 2)));
		assert_eq!(TzDateRule::parse(b"J5"), Ok((TzDateRule::J(5), 2)));
		assert_eq!(TzDateRule::parse(b"J57"), Ok((TzDateRule::J(57), 3)));
		assert_eq!(TzDateRule::parse(b"J578"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"J366"), Err(TzStringError::DateOutOfRange));

		assert_eq!(TzDateRule::parse(b"M1.2.3"), Ok((TzDateRule::M(1, 2, 3), 6)));
		assert_eq!(TzDateRule::parse(b"M12.5.6"), Ok((TzDateRule::M(12, 5, 6), 7)));
		assert_eq!(TzDateRule::parse(b"M13.5.6"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"M12.6.6"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"M12.5.7"), Err(TzStringError::DateOutOfRange));
		assert_eq!(TzDateRule::parse(b"M1.2."), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1.2"), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1."), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1"), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M"), Err(TzStringError::InvalidOrUnsupportedTzString));

		assert_eq!(TzDateRule::parse(b""), Err(TzStringError::MissingTzDateRule));
		assert_eq!(TzDateRule::parse(b"M1,2.3"), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzDateRule::parse(b"M1.2,3"), Err(TzStringError::InvalidOrUnsupportedTzString));
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

		// Ensure extreme inputs don't panic
		TzDateRule::N(365).as_timestamp(0);
		TzDateRule::N(365).as_timestamp(u16::MAX);
		TzDateRule::J(365).as_timestamp(0);
		TzDateRule::J(365).as_timestamp(u16::MAX);
		TzDateRule::M(12, 5, 6).as_timestamp(0);
		TzDateRule::M(12, 5, 6).as_timestamp(u16::MAX);
	}

	#[test]
	fn tz_spec_parse() {
		assert_eq!(TzSpec::parse(b""), Err(TzStringError::MissingTzString));
		assert_eq!(TzSpec::parse(b"\n"), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse(b"EST"), Err(TzStringError::InvalidOrUnsupportedTzString));

		assert_eq!(TzSpec::parse(b"EST5"), Ok(TzSpec {
			utoff: -18000,
			dst: None
		}));
		assert_eq!(TzSpec::parse(b"CET-1CEST,M3.5.0,M10.5.0/3"), Ok(TzSpec {
			utoff: 3600,
			dst: Some((
				7200,
				TzRule {
					todst: (TzDateRule::M(3, 5, 0), 7200),
					fromdst: (TzDateRule::M(10, 5, 0), 10800)
				}
			))
		}));
		assert_eq!(TzSpec::parse(b"ABC-12DEF,M11.1.0,M1.2.1/147"), Ok(TzSpec {
			utoff: 43200,
			dst: Some((
				46800,
				TzRule {
					todst: (TzDateRule::M(11, 1, 0), 7200),
					fromdst: (TzDateRule::M(1, 2, 1), 529200)
				}
			))
		}));
		assert_eq!(TzSpec::parse(b"IST-2IDT,M3.4.4/26,M10.5.0"), Ok(TzSpec {
			utoff: 7200,
			dst: Some((
				10800,
				TzRule {
					todst: (TzDateRule::M(3, 4, 4), 93600),
					fromdst: (TzDateRule::M(10, 5, 0), 7200)
				}
			))
		}));
		assert_eq!(TzSpec::parse(b"XXX4YYY,J1/0,J365/25"), Ok(TzSpec {
			utoff: -14400,
			dst: Some((
				-10800,
				TzRule {
					todst: (TzDateRule::J(1), 0),
					fromdst: (TzDateRule::J(365), 90000)
				}
			))
		}));
		assert_eq!(TzSpec::parse(b"XXX4:30YYY6:45,25/3:10:30,280/-1:20"), Ok(TzSpec {
			utoff: -16200,
			dst: Some((
				-24300,
				TzRule {
					todst: (TzDateRule::N(25), 11430),
					fromdst: (TzDateRule::N(280), -4800)
				}
			))
		}));

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
		let mut spec = TzSpec::parse(b"EST5").unwrap();
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

		spec = TzSpec::parse(b"EST5EDT,70,230").unwrap();
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

		spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
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

		spec = TzSpec::parse(b"EST5EDT,M3.2.0/4,M11.1.0/-2").unwrap();
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
		assert_eq!(spec.info(1730599200), TzInfo { utoff: -18000, isdst: false }, "time: {}", 1730599200);

		// Check extreme inputs don't panic
		spec.info(i64::MIN);
		spec.info(i64::MAX);
	}

	#[test]
	fn private_doctest() {
		// Documentation for parse_num
		assert_eq!(parse_num(b"15x"), (15, 2));
		assert_eq!(parse_num(b"x15"), (0, 0));

		// Documentation for TzSpec::parse_time
		assert_eq!(TzSpec::parse_time(b"5", false), Ok((18000, 1)));
		assert_eq!(TzSpec::parse_time(b"-5", false), Ok((-18000, 2)));
		assert_eq!(TzSpec::parse_time(b"05:23:17", false), Ok((19397, 8)));
		assert_eq!(TzSpec::parse_time(b"30", true), Ok((108000, 2)));
		assert_eq!(TzSpec::parse_time(b"-30", true), Ok((-108000, 3)));
		assert_eq!(TzSpec::parse_time(b"", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"5:", false), Err(TzStringError::InvalidOrUnsupportedTzString));
		assert_eq!(TzSpec::parse_time(b"25", false), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"5:70", false), Err(TzStringError::TimeOutOfRange));
		assert_eq!(TzSpec::parse_time(b"200", true), Err(TzStringError::TimeOutOfRange));
	}
}
