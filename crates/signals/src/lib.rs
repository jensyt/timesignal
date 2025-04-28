//! Generate time signals.
//!
//! This crate can generate public time signals ([DCF77], [WWVB], and [JJY40/60]) as well as a
//! proprietary time signal ([Junghans]). Each signal can be written into a supplied buffer at
//! a desired sample rate.
//!
//! This crate is `no_std` by default. In order to support a variety of `no_std` environments this
//! crate includes a simplified version of 32-bit sine from `libm`.
//!
//! Enabling feature `std` makes three significant changes:
//!	- Uses [`f32::sin`] from the standard library as the implementation for 32-bit sine function.
//! - Adds support for parsing TZif files into [`time::tz::Timezone`].
//! - Changes the default behavior of several time signals (except for `wasm32` targets):
//! 	| Signal       | Default Timezone (`no_std`)  | Default Timezone (`std`)               |
//! 	| ------------ | ---------------------------- | -------------------------------------- |
//! 	| [`junghans`] | `UTC0`                       | `/etc/localtime`                       |
//! 	| [`wwvb`]     | `EST5EDT,M3.2.0,M11.1.0`     | `/usr/share/zoneinfo/America/New_York` |
//! 	| [`dcf77`]    | `CET-1CEST,M3.5.0,M10.5.0/3` | `/usr/share/zoneinfo/Europe/Berlin`    |
//! 	| [`jjy`]      | `JST-9`                      | `/usr/share/zoneinfo/Asia/Tokyo`       |
//!
//! [DCF77]: https://en.wikipedia.org/wiki/DCF77
//! [WWVB]: https://en.wikipedia.org/wiki/WWVB
//! [JJY40/60]: https://en.wikipedia.org/wiki/JJY
//! [Junghans]: junghans
//!
//! # Examples
//! ```
//! # use signals::{wwvb, MessageGenerator};
//! # use time;
//! // Construct a WWVB object to generate messages
//! let d = wwvb::new(None).expect("Error reading default timezone");
//!
//! // Get a message for the current time
//! let m = d.get_message(&mut time::now().unwrap());
//! match m {
//! 	Ok(m) => {
//! 		// Make a writer that converts the message into wire format at 48 kHz
//! 		let mut writer = wwvb::make_writer::<48000>();
//! 		// Sample the message at 48 kHz
//! 		let mut s = m.sample::<48000>();
//! 		// Create a buffer with enough space to hold 15s of the encoded message
//! 		let mut buf = Vec::<f32>::with_capacity(720000);
//! 		unsafe {
//! 			buf.set_len(720000);
//! 		}
//! 		let buf = buf.as_mut_slice();
//!
//! 		// Write the 60s message in four 15s chunks
//! 		for _ in 0..4 {
//! 			// Write the message to the buffer
//! 			writer(&mut s, buf);
//!
//! 			// Use the results in buf
//! 		}
//! 	},
//! 	Err(e) => {
//! 		// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
//! 		eprintln!("{}", e);
//! 	}
//! }
//! ```

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "std")]
extern crate std;

use core::{error, fmt};
use time::{TimeSpec, tz};

pub mod junghans;
pub mod dcf77;
pub mod wwvb;
pub mod jjy;

/// A time signal message to transmit.
#[derive(Default, Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Message {
	/// The packed, binary message to be transmitted. LSB first by convention, but technially each
	/// time signal module can decide how to interpret this value.
	pub packed: u64,
	/// An alternate, packed, binary message to be transmitted. This is useful for time signals that
	/// transmit both an amplitude and phase modulated message, where the messages may be different
	/// between the two formats (e.g. WWVB).
	pub packed_alt: u64,
	/// Time-signal-dependent time delay, used to ensure message transmission aligns exactly with the
	/// time being transmitted. Measured in nanoseconds.
	pub delay: i64,
	/// Whether the message represents a time period or instant that includes a leap second, which
	/// requires special handling in most time signals.
	pub leap: bool
}

impl Message {
	/// Create a new message.
	///
	/// This function sets [`Message::packed_alt`] to `0` and [`Message::leap`] to `false`.
	pub fn new(packed: u64, delay: i64) -> Message {
		Message {
			packed,
			packed_alt: 0,
			delay,
			leap: false
		}
	}

	/// Create a new message with all fields.
	///
	/// This function does not do any further processing on the inputs.
	pub fn new_with_alt(packed: u64, packed_alt: u64, delay: i64, leap: bool) -> Message {
		Message {
			packed,
			packed_alt,
			delay,
			leap
		}
	}

	/// Sample the message at the given rate (`N`).
	///
	/// This function should be called with the appropriate sampling rate before passing a [`Message`]
	/// to a writer.
	pub fn sample<const N: u64>(mut self) -> SampledMessage<N> {
		// Calculate GCD between N and 1,000,000,000 to reduce likelihood of overflow
		let (n, d) = const { shrink(N, 1000000000) };
		self.delay = (self.delay * n as i64) / d as i64;
		SampledMessage(self)
	}
}

/// A message that has been prepared for writing at a given sample rate, `N`.
#[derive(Default, Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct SampledMessage<const N: u64>(Message);

impl<const N: u64> SampledMessage<N> {
	/// Resample the message from rate `N` to rate `M`.
	///
	/// As with all sampling, this may be lossy. It is best to sample the original message at `M`
	/// instead of resampling.
	pub fn resample<const M: u64>(mut self) -> SampledMessage<M> {
		// Calculate GCD between M and N to reduce likelihood of overflow
		let (n, d) = const { shrink(M, N) };
		self.0.delay = (self.0.delay * n as i64) / d as i64;
		SampledMessage(self.0)
	}
}

/// Find the minimum `(u, v)` such that `x * u / v == x * l / r` assuming no overflow.
///
/// This function calculates the greatest common denominator between `l` and `r`, and then returns
/// `l / gcd` and `r / gcd`. This transformation can be helpful to reduce the likelihood of
/// overflow.
///
/// # Examples
/// ```ignore
/// assert_eq!(shrink(500, 10), (50, 1));
///
/// // Uncommenting the below lines would lead to overflow
/// // let (l, r) = (1000, 500000);
/// // assert_eq!(1234567890987654321_u64 * l / r, 2469135781975308_u64);
///
/// // But this works, because (l, r) = (1, 500)
/// let (l, r) = const { shrink(1000, 500000) };
/// assert_eq!(1234567890987654321_u64 * l / r, 2469135781975308_u64);
/// ```
const fn shrink(l: u64, r: u64) -> (u64, u64) {
	// Source: https://en.wikipedia.org/wiki/Binary_GCD_algorithm
	if l == 0 || r == 0 { return (l, r) }

	let i = l.trailing_zeros();
	let j = r.trailing_zeros();
	let k = if j < i { j } else { i };
	let mut u = l >> i;
	let mut v = r >> j;

	loop {
		if u > v {
			let tmp = u;
			u = v;
			v = tmp;
		}

		v -= u;

		if v == 0 {
			let gcd = u << k;
			break (l / gcd, r / gcd)
		}

		v >>= v.trailing_zeros();
	}
}

/// The error type for constructing messages.
#[cfg_attr(test, derive(PartialEq))]
pub enum MessageError {
	/// The input time is before the Unix epoch (Jan 1, 1970) and not supported. The unsupported time
	/// is provided in the payload.
	UnsupportedTime(i64),
	/// The timezone offset is not valid for this message format. The supplied offset (in seconds) is
	/// provided in the payload.
	UnsupportedTimezoneOffset(i32),
	/// Error parsing the default timezone. The underlying error is provided in the payload.
	#[cfg(not(feature = "std"))]
	TimezoneError(tz::TzStringError),
	/// Error parsing the default timezone. The underlying error is provided in the payload.
	#[cfg(feature = "std")]
	#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
	TimezoneError(tz::TzFileError)
}

impl fmt::Display for MessageError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			MessageError::UnsupportedTime(x) => write!(f, "Unsupported time: {}", x),
			MessageError::UnsupportedTimezoneOffset(x) => write!(f, "Unsupported local timezone offset: {}", x),
			MessageError::TimezoneError(x) => write!(f, "Timezone error: {}", x),
		}
	}
}

impl fmt::Debug for MessageError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

impl error::Error for MessageError {}

/// Trait for time signal message generators.
pub trait MessageGenerator {
	/// Get a message for the given time.
	///
	/// It is up to the message generator to determine how to generate a message for `time`. For
	/// example, Junghans and DCF77 encode the instant at the **end** of the message, while WWVB
	/// encodes the instant at the **beginning** of the message.
	///
	/// It is also up to the message generator to use the fields in the returned [`Message`] as
	/// needed, though by convention [`Message::packed`] and [`Message::packed_alt`] should be
	/// transmitted LSB first. For sampling to work as expected, [`Message::delay`] should be in
	/// nanoseconds, since it will be converted to sample time prior to being passed to a writer.
	///
	/// This function should adjust `time` to the next timestamp for which a message should be
	/// generated.
	fn get_message(&self, time: &mut TimeSpec) -> Result<Message, MessageError>;
}

/// 32-bit sine function.
///
/// This version simply uses [`f32::sin`].
#[cfg(any(test, feature = "std"))]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[inline(always)]
fn sin32(x: f32) -> f32 {
	x.sin()
}

#[cfg(all(not(test), not(feature = "std")))]
mod sin;
#[cfg(all(not(test), not(feature = "std")))]
use sin::sin32;

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn sample_test() {
		assert_eq!(shrink(500, 10), (50, 1));
		// Uncommenting the below line would lead to overflow
		// assert_eq!(1234567890987654321_u64 * 1000 / 500000, 2469135781975308_u64);
		let (l, r) = const { shrink(1000, 500000) };
		assert_eq!(1234567890987654321 * l / r, 2469135781975308);

		let m = Message::new(0, 123456789);
		assert_eq!(m.sample::<48000>(), SampledMessage::<48000>(Message::new(0, 5925)));
		assert_eq!(m.sample::<192000>(), SampledMessage::<192000>(Message::new(0, 23703)));
		assert_eq!(m.sample::<48000>().resample::<192000>(), SampledMessage::<192000>(Message::new(0, 23700)));
		assert_eq!(m.sample::<192000>().resample::<48000>(), SampledMessage::<48000>(Message::new(0, 5925)));
	}
}
