//! Support for command line argument parsing.
//!
//! See [crate] documentation for details on command line arguments and examples.

use std::error::Error;
use std::ffi::OsString;
use std::fmt::{Display, Debug};
use std::num::NonZero;
use std::str::FromStr;
use crate::{tz, tz::Timezone};

/// Known time signal types.
///
/// Not all of these signal types are currently implemented!
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum SignalType {
	/// Junghans's proprietary time signal. [More](crate::junghans).
	Junghans,
	/// Germany's [DCF77](https://en.wikipedia.org/wiki/DCF77).
	DCF77,
	/// USA's [WWVB](https://en.wikipedia.org/wiki/WWVB).
	WWVB,
	/// Japan's [JJY40](https://en.wikipedia.org/wiki/JJY).
	JJY40,
	/// Japan's [JJY60](https://en.wikipedia.org/wiki/JJY).
	JJY60,
	/// UK's [MSF](https://en.wikipedia.org/wiki/Time_from_NPL_(MSF)).
	MSF
}

impl FromStr for SignalType {
	type Err = ArgumentsError;

	/// Parse a string into a [`SignalType`].
	///
	/// The parsing is case insensitive. Returns [`ArgumentsError::InvalidSignal`] if the input string
	/// is not one of the defined signals.
	///
	/// # Examples
	///
	/// ```
	/// assert_eq!(SignalType::from_str("junghans"), Ok(SignalType::Junghans));
	/// assert_eq!(SignalType::from_str("JUNGHANS"), Ok(SignalType::Junghans));
	/// assert_eq!(SignalType::from_str("dcf77"), Ok(SignalType::DCF77));
	/// assert_eq!(SignalType::from_str("DCF77"), Ok(SignalType::DCF77));
	/// assert_eq!(
	///		SignalType::from_str("junghanss"),
	///		Err(ArgumentsError::InvalidSignal(String::from("junghanss")))
	/// );
	/// ```
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s.to_ascii_lowercase().as_str() {
			"junghans" => Ok(SignalType::Junghans),
			"dcf77" => Ok(SignalType::DCF77),
			"wwvb" => Ok(SignalType::WWVB),
			"jjy40" => Ok(SignalType::JJY40),
			"jjy60" => Ok(SignalType::JJY60),
			"msf" => Ok(SignalType::MSF),
			_ => Err(ArgumentsError::InvalidSignal(s.to_string()))
		}
	}
}

/// The error type for parsing command line arguments.
#[cfg_attr(test, derive(PartialEq))]
pub enum ArgumentsError {
	/// The option was unrecognized. The option is returned as the payload of this variant.
	UnrecognizedOption(String),
	/// Error converting an option or parameter to UTF-8. Options are required to be UTF-8, as are
	/// most parameters (except the parameter to `-t` / `--timezone`). The argument index and original
	/// [`OsString`] that could not be converted are returned as the payload of this variant.
	InvalidUTF8(usize, OsString),
	/// The required time signal was missing.
	MissingSignal,
	/// The provided time signal was invalid. The supplied time signal argument is returned as the
	/// payload of this variant.
	InvalidSignal(String),
	/// The provided message count was invalid. The supplied count argument is returned as the payload
	/// of this variant.
	InvalidCount(String),
	/// The parameter for an option was not supplied. The option is returned as the payload for this
	/// variant.
	MissingParameter(String),
	/// An error occured while parsing the provided timezone. The underlying timezone error is
	/// returned as the payload for this variant.
	TimezoneError(tz::Error),
	/// Help option (-h) was included, so print help details and exit.
	Help
}

impl Display for ArgumentsError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ArgumentsError::UnrecognizedOption(s) => write!(f, "Unrecognized option: {}", s),
			ArgumentsError::InvalidUTF8(i, v) => write!(f, "Invalid UTF-8 in argument {}: {:?}", i, v),
			ArgumentsError::MissingSignal => write!(f, "Missing signal input"),
			ArgumentsError::InvalidSignal(s) => write!(f, "Invalid signal: {}", s),
			ArgumentsError::InvalidCount(s) => write!(f, "Invalid count: {}", s),
			ArgumentsError::MissingParameter(s) => write!(f, "Missing parameter for option {}", s),
			ArgumentsError::TimezoneError(t) => write!(f, "Timezone error: {}", t),
			ArgumentsError::Help => write!(f, "Help requested")
		}
	}
}

impl Debug for ArgumentsError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		Display::fmt(self, f)
	}
}

impl Error for ArgumentsError {}

/// Convert an argument to [`&str`].
///
/// The function takes the argument index `i`, optional argument name `a`, and the argument `s`.
///
/// # Errors
///
/// Returns [`ArgumentsError::InvalidUTF8`] if the argument could not be converted to UTF-8 or
/// [`ArgumentsError::MissingParameter`] if the argument is `None`.
///
/// # Examples
///
/// ```
/// let valid = OsString::from_str("test").unwrap();
///	assert_eq!(
///		arg_to_str(1, Some("arg"), Some(&valid)),
///		Ok("test")
///	);
///	assert_eq!(
///		arg_to_str(1, Some("arg"), None),
///		Err(ArgumentsError::MissingParameter(String::from("arg")))
///	);
///
///	let invalid = unsafe { OsString::from_encoded_bytes_unchecked(vec![b't', 0xff, b's', b't']) };
///	assert_eq!(
///		arg_to_str(1, Some("arg"), Some(&invalid)),
///		Err(ArgumentsError::InvalidUTF8(1, invalid.clone()))
///	);
/// ```
fn arg_to_str<'a, 'b>(i: usize, a: Option<&'a str>, s: Option<&'b OsString>)
	-> Result<&'b str, ArgumentsError>
{
	match s {
		Some(v) => v.to_str().ok_or_else(|| ArgumentsError::InvalidUTF8(i, v.clone())),
		None => Err(ArgumentsError::MissingParameter(a.map(String::from).unwrap_or_default()))
	}
}

/// Parsed command line arguments.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Arguments {
	/// The time signal type.
	pub signal: SignalType,
	/// The number of messages to transmit.
	pub count: NonZero<usize>,
	/// The configured timezone (if provided).
	pub timezone: Option<Timezone>,
	/// The configured NTP server (if provided).
	pub ntp: Option<String>
}

impl Arguments {
	/// Parse command line arguments.
	///
	/// The input can be any type that implements [`Iterator`] that yields [`OsString`], though
	/// typically this would be [`std::env::args_os`]. This function assumes that the application
	/// name is **not** supplied as the first item yielded by `args`, see examples for common use.
	///
	/// # Errors
	///
	/// This function can return any of the variants in [`ArgumentsError`]. See that documentation
	/// for more details.
	///
	/// # Examples
	///
	/// ```
	/// let args = match Arguments::parse(std::env::args_os().skip(1)) {
	/// 	Ok(a) => a,
	/// 	Err(e) => {
	/// 		// Handle error
	/// 		panic!("{}", e);
	/// 	}
	/// };
	/// ```
	pub fn parse(mut args: impl Iterator<Item = OsString>) -> Result<Arguments, ArgumentsError>
	{
		let mut signal: Result<SignalType, ArgumentsError> = Err(ArgumentsError::MissingSignal);
		let mut count: Option<NonZero<usize>> = None;
		let mut timezone: Option<Timezone> = None;
		let mut ntp: Option<String> = None;
		let mut arg = args.next();
		let mut i = 0;
		loop {
			if arg.is_none() { break; }
			match arg_to_str(i, None, arg.as_ref())? {
				n @ ("-n" | "-c" | "--count") => {
					count = Some(
						arg_to_str(i+1, Some(n), args.next().as_ref())
						.and_then(
							|v| v.parse().map_err(|_| ArgumentsError::InvalidCount(v.to_string()))
						)?
					);
					// Increment because we called args.next()
					i += 1;
				},
				t @ ("-t" | "--timezone") => {
					if let Some(a) = args.next() {
						timezone = Some(tz::parse_file(a.as_os_str()).or_else(|e| {
							if let tz::Error::FileReadError(_) = e {
								tz::parse_tzstring(a.as_encoded_bytes())
							} else {
								Err(e)
							}
						}).map_err(|e| ArgumentsError::TimezoneError(e))?);
					} else {
						return Err(ArgumentsError::MissingParameter(t.to_string()))
					}
					// Increment because we called args.next()
					i += 1;
				},
				"--ntp" => {
					ntp = Some(String::from(arg_to_str(i+1, Some("--ntp"), args.next().as_ref())?))
				},
				"-h" => return Err(ArgumentsError::Help),
				v => {
					if v.starts_with('-') {
						return Err(ArgumentsError::UnrecognizedOption(v.to_string()));
					}

					signal = SignalType::from_str(v)
				}
			}
			arg = args.next();
			// Increment because we called args.next()
			i += 1;
		}

		Ok(Arguments {
			signal: signal?,
			count: count.unwrap_or(unsafe { NonZero::new_unchecked(4) }),
			timezone,
			ntp
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn signal_type_test() {
		assert_eq!(SignalType::from_str("junghans"), Ok(SignalType::Junghans));
		assert_eq!(SignalType::from_str("JUNGHANS"), Ok(SignalType::Junghans));
		assert_eq!(SignalType::from_str("dcf77"), Ok(SignalType::DCF77));
		assert_eq!(SignalType::from_str("DCF77"), Ok(SignalType::DCF77));
		assert_eq!(SignalType::from_str("wwvb"), Ok(SignalType::WWVB));
		assert_eq!(SignalType::from_str("WWVB"), Ok(SignalType::WWVB));
		assert_eq!(SignalType::from_str("jjy40"), Ok(SignalType::JJY40));
		assert_eq!(SignalType::from_str("JJY40"), Ok(SignalType::JJY40));
		assert_eq!(SignalType::from_str("jjy60"), Ok(SignalType::JJY60));
		assert_eq!(SignalType::from_str("JJY60"), Ok(SignalType::JJY60));
		assert_eq!(SignalType::from_str("msf"), Ok(SignalType::MSF));
		assert_eq!(SignalType::from_str("MSF"), Ok(SignalType::MSF));

		assert_eq!(
			SignalType::from_str("junghanss"),
			Err(ArgumentsError::InvalidSignal(String::from("junghanss")))
		);

		assert_eq!(
			SignalType::from_str("junghan"),
			Err(ArgumentsError::InvalidSignal(String::from("junghan")))
		);

		assert_eq!(
			SignalType::from_str("lkjgf8o3"),
			Err(ArgumentsError::InvalidSignal(String::from("lkjgf8o3")))
		);
	}

	#[test]
	fn arg_to_str_test() {
		let valid = OsString::from_str("test").unwrap();
		assert_eq!(
			arg_to_str(1, Some("arg"), Some(&valid)),
			Ok("test")
		);
		assert_eq!(
			arg_to_str(1, Some("arg"), None),
			Err(ArgumentsError::MissingParameter(String::from("arg")))
		);

		let invalid = unsafe { OsString::from_encoded_bytes_unchecked(vec![b't', 0xff, b's', b't']) };
		assert_eq!(
			arg_to_str(1, Some("arg"), Some(&invalid)),
			Err(ArgumentsError::InvalidUTF8(1, invalid.clone()))
		);
	}

	#[test]
	fn arguments_parse_test() {
		let args: Vec<_> = vec![
			"-n", "5",
			"-t", "EST5EDT,M3.2.0,M11.1.0",
			"--ntp", "time.google.com",
			"junghans",
			"-c", "7",
			"--timezone", "/usr/share/zoneinfo/America/Los_Angeles",
			"dcf77",
			"-n", "asd",
			"-n", "0",
			"-n", "-5",
			"-t", "EST5EDT"
		].into_iter().map(OsString::from_str).map(Result::unwrap).collect();

		assert_eq!(
			// -n 5 -t EST5EDT,M3.2.0,M11.1.0 --ntp time.google.com junghans
			Arguments::parse(args.iter().take(7).cloned()),
			Ok(Arguments {
				signal: SignalType::Junghans,
				count: NonZero::new(5).unwrap(),
				timezone: tz::parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").ok(),
				ntp: Some(String::from("time.google.com"))
			})
		);

		assert_eq!(
			// -n 5 junghans
			Arguments::parse(args.iter().take(2).chain(args.iter().skip(6).take(1)).cloned()),
			Ok(Arguments {
				signal: SignalType::Junghans,
				count: NonZero::new(5).unwrap(),
				timezone: None,
				ntp: None
			})
		);

		assert_eq!(
			// -t EST5EDT,M3.2.0,M11.1.0 junghans
			Arguments::parse(args.iter().skip(2).take(2).chain(args.iter().skip(6).take(1)).cloned()),
			Ok(Arguments {
				signal: SignalType::Junghans,
				count: NonZero::new(4).unwrap(),
				timezone: tz::parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").ok(),
				ntp: None
			})
		);

		assert_eq!(
			// --ntp time.google.com junghans
			Arguments::parse(args.iter().skip(4).take(3).cloned()),
			Ok(Arguments {
				signal: SignalType::Junghans,
				count: NonZero::new(4).unwrap(),
				timezone: None,
				ntp: Some(String::from("time.google.com"))
			})
		);

		assert_eq!(
			// -c 7 --timezone /usr/share/zoneinfo/America/Los_Angeles dcf77
			Arguments::parse(args.iter().skip(7).take(5).cloned()),
			Ok(Arguments {
				signal: SignalType::DCF77,
				count: NonZero::new(7).unwrap(),
				timezone: tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok(),
				ntp: None
			})
		);

		assert_eq!(
			// -n 5 -c 7 -t EST5EDT,M3.2.0,M11.1.0 --timezone /usr/share/zoneinfo/America/Los_Angeles dcf77
			Arguments::parse(args.iter().take(4).chain(args.iter().skip(7).take(5)).cloned()),
			Ok(Arguments {
				signal: SignalType::DCF77,
				count: NonZero::new(7).unwrap(),
				timezone: tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok(),
				ntp: None
			})
		);

		assert_eq!(
			// -n 5
			Arguments::parse(args.iter().take(2).cloned()),
			Err(ArgumentsError::MissingSignal)
		);

		assert_eq!(
			// -n
			Arguments::parse(args.iter().take(1).cloned()),
			Err(ArgumentsError::MissingParameter(String::from("-n")))
		);

		assert_eq!(
			// -n asd
			Arguments::parse(args.iter().skip(12).take(2).cloned()),
			Err(ArgumentsError::InvalidCount(String::from("asd")))
		);

		assert_eq!(
			// -n 0
			Arguments::parse(args.iter().skip(14).take(2).cloned()),
			Err(ArgumentsError::InvalidCount(String::from("0")))
		);

		assert_eq!(
			// -n -5
			Arguments::parse(args.iter().skip(16).take(2).cloned()),
			Err(ArgumentsError::InvalidCount(String::from("-5")))
		);

		assert!(
			// -t EST5EDT junghans
			Arguments::parse(
				args.iter().skip(18).take(2).chain(args.iter().skip(6).take(1)).cloned()
			).is_err()
		);
	}
}
