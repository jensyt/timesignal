//! Support for parsing TZif files.
//!
//! This module supports a subset of Olson timezone database features: UTC offsets and daylight
//! savings time changes, specified either directly in TZif binary data or via an included TZ
//! string. This module supports versions 1-4 of the TZif specification for this subset of
//! features, and most extended POSIX features for TZ strings.
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
//! All functions is this module require the `alloc` feature. The helper function [`parse_file`]
//! additionally requires the `std` feature.
//!
//! # Examples
//!
//! ```
//! # use time::{time::Tm, tz::{parse_tzstring, TzInfo, TmWithTzInfo}};
//! # #[cfg(feature = "std")] use time::tz::parse_file;
//! # #[cfg(feature = "std")] {
//! // Parsing a file
//! let timezone = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();
//!
//! // Getting info for a given unix timestamp
//! let info = timezone.info(1723433665);
//! assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
//!
//! // Getting the date for a given unix timestamp
//! let date = timezone.date(1723433665);
//! assert_eq!(date, Some(TmWithTzInfo {
//! 	tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
//! 	info: TzInfo { utoff: -25200, isdst: true }
//! }));
//! # }
//! ```

use core::{error, fmt, slice::SliceIndex};
use alloc::{boxed::Box, string::String};
#[cfg(feature = "std")]
use std::{fs, io, path::Path, string::ToString};
use super::tzstring::{TzStringError, TzSpec};
use super::{Timezone, TzInfo, get_or_default};

/// The error type for parsing timezone data (TZif files).
#[derive(Debug, PartialEq)]
pub enum TzFileError {
	/// Error reading the file. The reason is returned as a payload of this variant.
	FileReadError(String),
	/// The file being read is not a TZif file (missing "TZif" magic bytes).
	NotATzFile,
	/// The file is not one of the four supported versions. The found version is returned as a payload
	/// of this variant.
	UnsupportedVersion(u8),
	/// The file is not a valid TZif file.
	InvalidTzFile,
	/// The included TZ string is invalid or unsupported.
	InvalidOrUnsupportedTzString(TzStringError)
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg(feature = "std")]
impl From<io::Error> for TzFileError {
	/// Wrap an [`io::Error`] in a [`TzFileError::FileReadError`].
	fn from(error: io::Error) -> Self {
		Self::FileReadError(error.to_string())
	}
}

impl From<TzStringError> for TzFileError {
	/// Wrap a [`TzStringError`] in a [`TzFileError::InvalidOrUnsupportedTzString`].
	fn from(error: TzStringError) -> Self {
		Self::InvalidOrUnsupportedTzString(error)
	}
}

impl fmt::Display for TzFileError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			TzFileError::FileReadError(s) => write!(f, "{}", s),
			TzFileError::NotATzFile => write!(f, "Not a TZ file"),
			TzFileError::UnsupportedVersion(v) => write!(f, "Unsupported TZ version: {0} ({0:#04x})", v),
			TzFileError::InvalidTzFile => write!(f, "Invalid TZ file"),
			TzFileError::InvalidOrUnsupportedTzString(e) => write!(f, "{}", e)
		}
	}
}

impl error::Error for TzFileError {}

/// Read a big endian, unsigned 32-bit number from a byte array.
///
/// # Panics
/// This function must be called with a slice of length 4. Any other input will panic.
///
/// # Examples
///
/// ```ignore
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
/// ```ignore
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
/// ```ignore
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

/// Get a given index, if valid, or return [`TzFileError::InvalidTzFile`].
#[inline(always)]
pub(super) fn get_or_invalid<I>(bytes: &[u8], index: I) -> Result<&I::Output, TzFileError>
where I: SliceIndex<[u8]> {
	bytes.get(index).ok_or(TzFileError::InvalidTzFile)
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
	/// Returns [`TzFileError::InvalidTzFile`] if the length of `bytes` is less than 24 bytes
	fn parse(bytes: &[u8]) -> Result<TzHeader, TzFileError> {
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
/// Returns [`TzFileError::InvalidTzFile`] if the TZif file is malformed, for example there is
/// less data in `bytes` than expected or transition times map to invalid transition type indices.
///
/// Returns [`TzFileError::InvalidOrUnsupportedTzString`] if `parse_spec` is `true` and the TZ
/// string is invalid or uses unsupported features. This error does not occur if the TZ string is
/// simply empty.
fn parse_internal<T>(mut bytes: &[u8], parse_spec: bool) -> Result<Timezone, TzFileError>
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
			return Err(TzFileError::InvalidTzFile)
		}
		let (e, b) = get_or_invalid(bytes, 1..)?.split_last().ok_or(TzFileError::InvalidTzFile)?;
		if *e != b'\n' {
			return Err(TzFileError::InvalidTzFile)
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
		return Err(TzFileError::InvalidTzFile);
	} else if t.times.len() == 0 && t.spec.is_none() {
		// Special case where there are no precomputed transition times and no TZ string, but there is
		// at least one transition type. In that case, we can assume the first type applies to all
		// times. This is consistent with common timezone implementations.
		if types.len() > 0 {
			t.times = Box::new([(i64::MIN, types[0]), (i64::MAX, types[0])]);
		} else {
			return Err(TzFileError::InvalidTzFile);
		}
	}

	Ok(t)
}

/// Parse a byte slice containing a TZif file.
///
/// # Errors
///
/// May return the following errors:
/// - [`TzFileError::NotATzFile`] if the file does not begin with the 'TZif' magic bytes
/// - [`TzFileError::UnsupportedVersion`] if the file version is not 1, 2, 3, or 4
/// - [`TzFileError::InvalidTzFile`] if the file is not properly formatted
/// - [`TzFileError::InvalidOrUnsupportedTzString`] if the optional TZ string is malformed
pub fn parse_bytes(bytes: &[u8]) -> Result<Timezone, TzFileError> {
	// Check for magic bytes
	if read_u32(get_or_invalid(bytes, 0..4)?) != 0x545a6966 {
		return Err(TzFileError::NotATzFile);
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
		v => Err(TzFileError::UnsupportedVersion(*v))
	}
}

/// Parse a TZif file.
///
/// # Errors
///
/// May return the following errors:
/// - [`TzFileError::FileReadError`] if the file could not be read
/// - [`TzFileError::NotATzFile`] if the file does not begin with the 'TZif' magic bytes
/// - [`TzFileError::UnsupportedVersion`] if the file version is not 1, 2, 3, or 4
/// - [`TzFileError::InvalidTzFile`] if the file is not properly formatted
/// - [`TzFileError::InvalidOrUnsupportedTzString`] if the optional TZ string is malformed
///
/// # Examples
///
/// ```
/// # use time::tz::parse_file;
/// let timezone = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg(feature = "std")]
pub fn parse_file<P>(file: P) -> Result<Timezone, TzFileError>
where
	P: AsRef<Path>
{
	let bytes = fs::read(file)?;
	parse_bytes(bytes.as_slice())
}

#[cfg(test)]
mod tests {
	use super::*;

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
	fn private_doctest() {
		// Documentation for read_u32
		assert_eq!(read_u32(&[0, 0, 0, 1]), 1);
		assert_eq!(read_u32(&[255, 255, 255, 255]), 4294967295);

		// Documentation for read_i32
		assert_eq!(read_i32(&[0, 0, 0, 1]), 1);
		assert_eq!(read_i32(&[255, 255, 255, 255]), -1);

		// Documentation for read_i64
		assert_eq!(read_i64(&[0, 0, 0, 0, 0, 0, 0, 1]), 1);
		assert_eq!(read_i64(&[255, 255, 255, 255, 255, 255, 255, 255]), -1);
	}
}
