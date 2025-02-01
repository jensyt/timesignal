//! Parse date time strings like `YYYY-MM-DD HH:mm:ss.sss`.
//!
//! This module provides a single function, [`parse_timestamp`], which can be used to parse a date
//! time string into a Unix timestamp, represented by [`TimeSpec`].
//!
//! # Examples
//! ```
//! # use time::{parse::parse_timestamp, time::TimeSpec};
//! assert_eq!(
//! 	parse_timestamp(b"2025-02-18T12:30:45Z"),
//! 	Ok(TimeSpec { sec: 1739881845, nsec: 0 })
//! );
//! assert_eq!(
//! 	parse_timestamp(b"2025-02-18T12:30:45+01:00"),
//! 	Ok(TimeSpec { sec: 1739878245, nsec: 0 })
//! );
//! assert_eq!(
//! 	parse_timestamp(b"2025-02-18 12:30:45 -01:00"),
//! 	Ok(TimeSpec { sec: 1739885445, nsec: 0 })
//! );
//! ```
//!
//! See [`parse_timestamp`] for more details on the supported input formats.

use core::{error, fmt};
use crate::time::{days_per_month, timestamp_from_ymd, TimeSpec};

/// Error type for parsing date time strings.
#[derive(Debug, PartialEq)]
pub enum ParseError {
	/// Expected a year, but it was missing or malformed.
	MissingYear,
	/// Expected a month, but it was missing or malformed.
	MissingMonth,
	/// The supplied month was outside of [1, 12].
	MonthOutOfRange,
	/// Expected a day, but it was missing or malformed.
	MissingDay,
	/// The supplied day was outside of [1, 28|29|30|31] depending on the month & year.
	DayOutOfRange,
	/// Expected hours, but it was missing or malformed.
	MissingHours,
	/// The supplied hour was outside of [0, 23].
	HoursOutOfRange,
	/// Hour was supplied but minutes were missing.
	MissingMinutes,
	/// The supplied minutes were outside of [0, 59].
	MinutesOutOfRange,
	/// Expected seconds, but it was missing or malformed.
	MissingSeconds,
	/// The supplied seconds were outside of [0, 59].
	SecondsOutOfRange,
	/// Expected milliseconds, but it was missing or malformed.
	MissingMilliseconds,
	/// Found unexpected bytes after a valid date time string.
	UnexpectedInput
}

impl fmt::Display for ParseError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			ParseError::MissingYear => write!(f, "Year missing or malformed"),
			ParseError::MissingMonth => write!(f, "Month missing or malformed"),
			ParseError::MonthOutOfRange => write!(f, "Month out of range"),
			ParseError::MissingDay => write!(f, "Day missing or malformed"),
			ParseError::DayOutOfRange => write!(f, "Day out of range"),
			ParseError::MissingHours => write!(f, "Hours missing or malformed"),
			ParseError::HoursOutOfRange => write!(f, "Hours out of range"),
			ParseError::MissingMinutes => write!(f, "Minutes missing or malformed"),
			ParseError::MinutesOutOfRange => write!(f, "Minutes out of range"),
			ParseError::MissingSeconds => write!(f, "Seconds missing or malformed"),
			ParseError::SecondsOutOfRange => write!(f, "Seconds out of range"),
			ParseError::MissingMilliseconds => write!(f, "Milliseconds missing or malformed"),
			ParseError::UnexpectedInput => write!(f, "Unexected input at end of date time string"),
		}
	}
}

impl error::Error for ParseError {}

/// Parse a fixed-length, unsigned integer.
///
/// `N` must be less than 5 to ensure the parsed value fits into a u16 with no possible overflow.
fn parse_num<const N: usize>(bytes: &[u8], e: ParseError) -> Result<(&[u8], u16), ParseError> {
	// Only allow numbers that can safely fit in u16
	const { assert!(N < 5); }

	if bytes.len() < N {
		return Err(e);
	}

	let mut r: u16 = 0;
	for i in 0..N {
		// Indexing won't panic because we checked bytes.len() above
		r = match bytes[i] {
			// Don't need checked math because we can't overflow
			v @ b'0'..=b'9' => r * 10 + (v - b'0') as u16,
			_ => return Err(e)
		};
	}

	Ok((&bytes[N..], r))
}

/// Parse a date time string into a Unix timestamp.
///
/// This functions parses strings in a format similar to the Javascript date time string format
/// described [here]. The key differences to the Javascript date time string format are:
/// - Extended years are not supported.
/// - When a timezone is omitted, all dates/times are assumed to be UTC.
/// - The special case of 24:00:00 time is not allowed.
/// - The literal `T` may be a space to separate date and time.
/// - A space between the time and timezone is allowed.
///
/// Examples of valid formats:
/// - `YYYY`
/// - `YYYY-MM`
/// - `YYYY-MM-DD`
/// - `YYYY-MM-DDTHH:mm` or `YYYY-MM-DD HH:mm`
/// - `YYYY-MM-DDTHH:mm:ss` or `YYYY-MM-DD HH:mm:ss`
/// - `YYYY-MM-DDTHH:mm:ss.sss` or `YYYY-MM-DD HH:mm:ss.sss`
/// - Each of the prior three bullets followed by `Z`, ` Z`, `+HH:mm`, `-HH:mm`, ` +HH:mm`, or
///   ` -HH:mm`
///
/// [here]: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Date#date_time_string_format
///
/// # Errors
///
/// Returns [`ParseError`] if the input was malformed or invalid in any way. This includes cases
/// where a valid timestamp was read but additional characters remain in `bytes`.
///
/// # Examples
/// ```
/// # use time::{parse::parse_timestamp, time::TimeSpec};
/// assert_eq!(
/// 	parse_timestamp(b"2025"),
/// 	Ok(TimeSpec { sec: 1735689600, nsec: 0 })
/// );
/// assert_eq!(
/// 	parse_timestamp(b"2025-02-18"),
/// 	Ok(TimeSpec { sec: 1739836800, nsec: 0 })
/// );
/// assert_eq!(
/// 	parse_timestamp(b"2025-02-18 12:30"),
/// 	Ok(TimeSpec { sec: 1739881800, nsec: 0 })
/// );
/// assert_eq!(
/// 	parse_timestamp(b"2025-02-18T12:30:45.123"),
/// 	Ok(TimeSpec { sec: 1739881845, nsec: 123000000 })
/// );
/// ```
pub fn parse_timestamp(bytes: &[u8]) -> Result<TimeSpec, ParseError> {
	let (bytes, year) = parse_num::<4>(bytes, ParseError::MissingYear)?;
	if bytes.len() == 0 {
		return Ok(TimeSpec {
			sec: timestamp_from_ymd(year, 1, 1),
			nsec: 0
		});
	}

	// Optional month
	let (bytes, month) = match bytes.split_first() {
		Some((b'-', b @ _)) => parse_num::<2>(b, ParseError::MissingMonth)?,
		_ => return Err(ParseError::UnexpectedInput),
	};
	if month == 0 || month > 12 {
		return Err(ParseError::MonthOutOfRange);
	}
	if bytes.len() == 0 {
		return Ok(TimeSpec {
			sec: timestamp_from_ymd(year, month as u8, 1),
			nsec: 0
		});
	}

	// Optional day
	let (bytes, day) = match bytes.split_first() {
		Some((b'-', b @ _)) => parse_num::<2>(b, ParseError::MissingDay)?,
		_ => return Err(ParseError::UnexpectedInput),
	};
	if day == 0 || day > days_per_month(year, month as u8) as u16 {
		return Err(ParseError::DayOutOfRange);
	}
	let mut timestamp = TimeSpec {
		sec: timestamp_from_ymd(year, month as u8, day as u8),
		nsec: 0
	};
	if bytes.len() == 0 {
		return Ok(timestamp);
	}

	// Optional hours
	let (bytes, hours) = match bytes.split_first() {
		Some((b'T' | b' ', b @ _)) => parse_num::<2>(b, ParseError::MissingHours)?,
		_ => return Err(ParseError::UnexpectedInput),
	};
	if hours > 23 {
		return Err(ParseError::HoursOutOfRange);
	}
	timestamp.sec += hours as i64 * 3600;
	if bytes.len() == 0 {
		return Err(ParseError::MissingMinutes);
	}

	// Required minutes
	let (bytes, minutes) = match bytes.split_first() {
		Some((b':', b @ _)) => parse_num::<2>(b, ParseError::MissingMinutes)?,
		_ => return Err(ParseError::UnexpectedInput),
	};
	if minutes > 59 {
		return Err(ParseError::MinutesOutOfRange);
	}
	timestamp.sec += minutes as i64 * 60;
	if bytes.len() == 0 {
		return Ok(timestamp);
	}

	// Optional seconds
	let (bytes, seconds) = match bytes.split_first() {
		Some((b':', b @ _)) => parse_num::<2>(b, ParseError::MissingSeconds)?,
		_ => return Err(ParseError::UnexpectedInput),
	};
	if seconds > 59 {
		return Err(ParseError::SecondsOutOfRange);
	}
	timestamp.sec += seconds as i64;
	if bytes.len() == 0 {
		return Ok(timestamp);
	}

	// Optional milliseconds
	let bytes = match bytes.split_first() {
		Some((b'.', b @ _)) => {
			let (bytes, ms) = parse_num::<3>(b, ParseError::MissingMilliseconds)?;
			timestamp.nsec = ms as i64 * 1000000;
			bytes
		},
		_ => bytes,
	};
	if bytes.len() == 0 {
		return Ok(timestamp);
	}

	// Optional timezone offset (hours)
	let bytes = match bytes.split_first() {
		Some((b' ', b @ _)) => b,
		_ => bytes
	};
	let ((bytes, hours), neg) = match bytes.split_first() {
		Some((b'+', b @ _)) => (parse_num::<2>(b, ParseError::MissingHours)?, false),
		Some((b'-', b @ _)) => (parse_num::<2>(b, ParseError::MissingHours)?, true),
		Some((b'Z', b @ _)) => {
			if b.len() == 0 {
				return Ok(timestamp)
			} else {
				return Err(ParseError::UnexpectedInput)
			}
		},
		_ => return Err(ParseError::UnexpectedInput),
	};
	if hours > 23 {
		return Err(ParseError::HoursOutOfRange);
	}
	if neg {
		timestamp.sec += hours as i64 * 3600;
	} else {
		timestamp.sec -= hours as i64 * 3600;
	}
	if bytes.len() == 0 {
		return Err(ParseError::MissingMinutes);
	}

	// Required timezone offset (minutes)
	let (bytes, minutes) = match bytes.split_first() {
		Some((b':', b @ _)) => parse_num::<2>(b, ParseError::MissingMinutes)?,
		_ => return Err(ParseError::MissingMinutes),
	};
	if minutes > 59 {
		return Err(ParseError::MinutesOutOfRange);
	}
	if neg {
		timestamp.sec += minutes as i64 * 60;
	} else {
		timestamp.sec -= minutes as i64 * 60;
	}
	if bytes.len() == 0 {
		Ok(timestamp)
	} else {
		Err(ParseError::UnexpectedInput)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn parse_timestamp_test() {
		// Year only
		assert_eq!(parse_timestamp(b"2025"), Ok(TimeSpec { sec: 1735689600, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025 "), Err(ParseError::UnexpectedInput));

		// Year-Month
		assert_eq!(parse_timestamp(b"2025-"), Err(ParseError::MissingMonth));
		assert_eq!(parse_timestamp(b"2025-2"), Err(ParseError::MissingMonth));
		assert_eq!(parse_timestamp(b"2025-02"), Ok(TimeSpec { sec: 1738368000, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-25"), Err(ParseError::MonthOutOfRange));

		// Year-Month-Day
		assert_eq!(parse_timestamp(b"2025-02-"), Err(ParseError::MissingDay));
		assert_eq!(parse_timestamp(b"2025-02-1"), Err(ParseError::MissingDay));
		assert_eq!(parse_timestamp(b"2025-02-18"), Ok(TimeSpec { sec: 1739836800, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-29"), Err(ParseError::DayOutOfRange));

		// Date + Hours:Minutes
		assert_eq!(parse_timestamp(b"2025-02-18T"), Err(ParseError::MissingHours));
		assert_eq!(parse_timestamp(b"2025-02-18T12"), Err(ParseError::MissingMinutes));
		assert_eq!(parse_timestamp(b"2025-02-18T12:"), Err(ParseError::MissingMinutes));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30"), Ok(TimeSpec { sec: 1739881800, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18 12:30"), Ok(TimeSpec { sec: 1739881800, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18T24:00"), Err(ParseError::HoursOutOfRange));
		assert_eq!(parse_timestamp(b"2025-02-18T12:60"), Err(ParseError::MinutesOutOfRange));

		// Date + Hours:Minutes:Seconds
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:"), Err(ParseError::MissingSeconds));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45"), Ok(TimeSpec { sec: 1739881845, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18 12:30:45"), Ok(TimeSpec { sec: 1739881845, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:60"), Err(ParseError::SecondsOutOfRange));

		// With milliseconds
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45."), Err(ParseError::MissingMilliseconds));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45.123"), Ok(TimeSpec { sec: 1739881845, nsec: 123000000 }));

		// With timezone
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45Z"), Ok(TimeSpec { sec: 1739881845, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45+01:00"), Ok(TimeSpec { sec: 1739878245, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45-01:00"), Ok(TimeSpec { sec: 1739885445, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18 12:30:45 Z"), Ok(TimeSpec { sec: 1739881845, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18 12:30:45 +01:00"), Ok(TimeSpec { sec: 1739878245, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18 12:30:45 -01:00"), Ok(TimeSpec { sec: 1739885445, nsec: 0 }));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45+24:00"), Err(ParseError::HoursOutOfRange));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45+01:60"), Err(ParseError::MinutesOutOfRange));

		// Invalid formats
		assert_eq!(parse_timestamp(b""), Err(ParseError::MissingYear));
		assert_eq!(parse_timestamp(b"202X-01-01"), Err(ParseError::MissingYear));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45+"), Err(ParseError::MissingHours));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45+01"), Err(ParseError::MissingMinutes));
		assert_eq!(parse_timestamp(b"2025-02-18T12:30:45Zinvalid"), Err(ParseError::UnexpectedInput));
	}
}
