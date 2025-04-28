//! Support for transmitting the JJY time signal.
//!
//! See [JJY documentation](https://www.nict.go.jp/en/sts/jjy_signal.html) for details. This module
//! implements the time-related features of JJY's time code, but notably excludes the alternate
//! transmission mode during minutes 15 and 45, including call sign announcement and service
//! interruption bits. During these minutes, the signal is transmitted as it is for every other
//! minute.
//!
//! JJY technically supports two frequencies, 40 kHz and 60 kHz. This module does not differentiate
//! between the two because it transmits audio on a base frequency for which both 40 kHz and 60 kHz
//! are harmonics. The base frequency is 20 kHz, making 40 kHz the 2nd harmonic and 60 kHz the 3rd
//! harmonic.
//!
//! Unlike most other time codes, JJY synchronizes the start of the minute to 55% of full power
//! transmission rather than the upward zero crossing of the first marker.
//!
//! # Examples
//! ```
//! # use signals::{jjy, MessageGenerator};
//! # use time;
//! // Construct a JJY object to generate messages
//! let d = jjy::new(None).expect("Error reading default timezone");
//!
//! // Get a message for the current time
//! let m = d.get_message(&mut time::now().unwrap());
//! match m {
//! 	Ok(m) => {
//! 		// Make a writer that converts the message into wire format at 48 kHz
//! 		let mut writer = jjy::make_writer::<48000>();
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

use crate::{Message, MessageError, MessageGenerator, SampledMessage};
use core::f32::consts::PI;
use crate::sin32;
use time::{nextleapsecond, tz::{self, Timezone}, TimeSpec};

/// An unpacked / uncompressed JJY message.
///
/// This type contains all of the components of the encoded JJY message, but in an unpacked
/// format that is easier to inspect. See [`MessageUncompressed::pack`] for details on getting and
/// using the packed message, which can be transmitted to a watch.
///
/// # Examples
/// ```ignore
/// // Japan (JST) timezone, UTC+9
/// let timezone = time::tz::parse_tzstring_const!(b"JST-9");
///
/// // Saturday, July 4, 2020. 11:36:58 JST
/// let m = MessageUncompressed::new(1593830218, &timezone).unwrap();
/// assert_eq!(m.min_ones, 6);            // Minute 36
/// assert_eq!(m.min_tens, 3);
/// assert_eq!(m.hour_ones, 1);           // Hour 11
/// assert_eq!(m.hour_tens, 1);
/// assert_eq!(m.yday_ones, 6);           // Day 186
/// assert_eq!(m.yday_tens, 8);
/// assert_eq!(m.yday_huns, 1);
/// assert_eq!(m.year_ones, 0);           // Year [20]20
/// assert_eq!(m.year_tens, 2);
/// assert_eq!(m.day_of_week, 6);         // Saturday
/// assert_eq!(m.leapsecond, 0);          // No leap second this month
///
/// let packed = m.pack();
/// assert_eq!(packed.reverse_bits(), 0x3304214180103000);
/// ```
struct MessageUncompressed {
	/// Minutes ones digit, ranged [0, 9].
	min_ones: u8,
	/// Minutes tens digit, ranged [0, 5].
	min_tens: u8,
	/// Hour ones digit, ranged [0, 9].
	hour_ones: u8,
	/// Hour tens digit, ranged [0, 2].
	hour_tens: u8,
	/// Day of year ones digit, ranged [0, 9].
	yday_ones: u8,
	/// Day of year tens digit, ranged [0, 9].
	yday_tens: u8,
	/// Day of year hundreds digit, ranged [0, 3].
	yday_huns: u8,
	/// Year ones digit, ranged [0, 9].
	year_ones: u8,
	/// Year tens digit, ranged [0, 9].
	year_tens: u8,
	/// Day of week, ranged [0, 6], where 0=Sunday, 6=Saturday.
	day_of_week: u8,
	/// Whether there is an upcoming leap second at the end of the month (`0x3`) or not (`0x0`).
	leapsecond: u8
}

impl MessageUncompressed {
	/// Create a new JJY message.
	///
	/// Input `time` should be greater than or equal to zero. `timezone` is used to set the UTC offset
	/// configuration for `time`.
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTime`] if `time < 0`.
	fn new(time: i64, timezone: &Timezone) -> Result<MessageUncompressed, MessageError> {
		let date = timezone.date(time).ok_or(MessageError::UnsupportedTime(time))?;

		// Calculate leap second info
		let leapsecond = match nextleapsecond(time)
						.map(|(t, _)| t - time)
						.filter(|&t| 0 < t && t <= 2419200) // 28 days
		{
			Some(_) => 0x3,
			None => 0x0,
		};

		Ok(MessageUncompressed {
			min_ones: date.tm.min % 10,
			min_tens: date.tm.min / 10,
			hour_ones: date.tm.hour % 10,
			hour_tens: date.tm.hour / 10,
			yday_ones: (date.tm.yday % 10) as u8,
			yday_tens: ((date.tm.yday / 10) % 10) as u8,
			yday_huns: (date.tm.yday / 100) as u8,
			year_ones: date.tm.year % 10,
			year_tens: (date.tm.year / 10) % 10,
			day_of_week: date.tm.wday,
			leapsecond
		})
	}

	/// Pack the message into the bit format used to transmit.
	///
	/// Returns a 64-bit value where each bit represents one second of the transmission. The LSB is
	/// the first bit to transmit. The MSB 5 bits are unused and not to be transmitted.
	fn pack(&self) -> u64 {
		// JJY uses even parity bits over the minute and hour.
		let min =  (self.min_ones & 0xf)
				| ((self.min_tens & 0x7) << 5);
		let min_parity = (min.count_ones() & 0x1) as u8;

		let hour =  (self.hour_ones & 0xf)
				 | ((self.hour_tens & 0x3) << 5);
		let hour_parity = (hour.count_ones() & 0x1) as u8;

		let mut a: u64 = (min   as u64)        << 55;
		a |= (hour              as u64)        << 45;
		a |= ((self.yday_huns   as u64) & 0x3) << 40;
		a |= ((self.yday_tens   as u64) & 0xf) << 35;
		a |= ((self.yday_ones   as u64) & 0xf) << 30;
		a |= ((hour_parity      as u64) & 0x1) << 27;
		a |= ((min_parity       as u64) & 0x1) << 26;
		a |= ((self.year_tens   as u64) & 0xf) << 19;
		a |= ((self.year_ones   as u64) & 0xf) << 15;
		a |= ((self.day_of_week as u64) & 0x7) << 11;
		a |= ((self.leapsecond  as u64) & 0x3) << 9;

		a.reverse_bits()
	}
}

/// JJY message generator.
///
/// Messages returned from [`JJY::get_message`] should be used with the writer returned by
/// [`make_writer`].
///
/// # Examples
///
/// ```
/// # use signals::jjy::JJY;
/// # use signals::MessageGenerator;
/// // Construct a JJY object to generate messages
/// let d = JJY::new(None).expect("Error reading default timezone");
///
/// // Get a message for the current time
/// let m = d.get_message(&mut time::now().unwrap());
/// match m {
/// 	Ok(mut m) => {
/// 		// Use the message
/// 	},
/// 	Err(e) => {
/// 		// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
/// 		eprintln!("{}", e);
/// 	}
/// }
/// ```
pub struct JJY {
	jp_tz: Timezone
}

/// Construct a new JJY object.
///
/// This is a convenience function, see [`JJY::new`] for details.
#[inline(always)]
pub fn new(timezone: Option<Timezone>) -> Result<JJY, MessageError> {
	JJY::new(timezone)
}

impl JJY {
	/// Construct a new JJY object.
	///
	/// If the input `timezone` is `None`, this function defaults to `JST-9` or reading
	/// `/usr/share/zoneinfo/Asia/Tokyo` (feature `std`) for timezone information.
	///
	/// # Errors
	///
	/// Returns [`MessageError::TimezoneError`] if there was an error reading
	/// `/usr/share/zoneinfo/Asia/Tokyo`.
	///
	/// # Examples
	///
	/// ```
	/// # use signals::jjy::JJY;
	/// let d = JJY::new(None);
	/// match d {
	/// 	Ok(_d) => {
	/// 		// Create & use messages
	/// 	},
	/// 	Err(_) => {
	/// 		// Known valid offset (UTC+9) that cannot fail
	/// 		let _d = JJY::new(
	/// 			Some(time::tz::parse_tzstring_const!(b"JST-9"))
	/// 		).unwrap();
	/// 		// Create & use messages
	/// 	}
	/// }
	/// ```
	pub fn new(timezone: Option<Timezone>) -> Result<JJY, MessageError> {
		match timezone {
			Some(t) => Ok(JJY { jp_tz: t }),
			#[cfg(all(not(target_arch = "wasm32"), feature = "std"))]
			None => tz::parse_file("/usr/share/zoneinfo/Asia/Tokyo")
						.map(|t| JJY { jp_tz: t })
						.map_err(|e| MessageError::TimezoneError(e)),
			#[cfg(any(target_arch = "wasm32", not(feature = "std")))]
			None => Ok(JJY {
				jp_tz: tz::parse_tzstring_const!(b"JST-9")
			})
		}
	}
}

impl MessageGenerator for JJY {
	/// Get a message for the given time.
	///
	/// This function returns a message for the minute that started on or before `time`, i.e. the
	/// message represents the instant at the **beginning** of the transmission.
	///
	/// The following fields of the returned message are used:
	/// - [`Message::packed`]: the amplitude modulated message, LSB first.
	/// - [`Message::delay`]: the current time within the minute, in nanoseconds.
	/// - [`Message::leap`]: true if a leap second should be inserted at the end of this message.
	///
	/// This function adjusts `time` to the next timestamp for which a message should be generated,
	/// which is exactly the beginning of the next minute.
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTime`] if the minute that includes `time` is less than
	/// zero.
	///
	/// # Examples
	///
	/// ```
	/// # use signals::jjy::JJY;
	/// # use signals::MessageGenerator;
	/// # use time::TimeSpec;
	/// let jjy = JJY::new(None).unwrap();
	/// // Sat, July 4, 2020. 11:07:25 JST (02:07:25 UTC)
	/// let mut time = TimeSpec {
	///     sec: 1593828445,
	///     nsec: 123456789
	/// };
	///
	/// let message = jjy.get_message(&mut time).unwrap();
	/// // Sat, July 4, 2020. 11:08:00 JST (02:08:00 UTC)
	/// assert_eq!(time.sec, 1593828480);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x384214184103000);
	/// assert_eq!(message.delay, 25123456789);
	/// assert_eq!(message.leap, false);
	///
	/// let message = jjy.get_message(&mut time).unwrap();
	/// // Sat, July 4, 2020. 11:09:00 JST (02:09:00 UTC)
	/// assert_eq!(time.sec, 1593828540);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x404214184103000);
	/// assert_eq!(message.delay, 0);
	/// assert_eq!(message.leap, false);
	/// ```
	fn get_message(&self, time: &mut TimeSpec) -> Result<Message, MessageError> {
		// Find the start of this minute (exactly)
		let time_in_min = time.sec % 60;
		let sec = time.sec - time_in_min;

		// Compute the message
		let message = MessageUncompressed::new(sec, &self.jp_tz)?;
		let am = message.pack();

		// Calculate where we are within the minute (in nanoseconds)
		let ns = time_in_min * 1000000000 + time.nsec;

		// Calculate if this is a minute with leap second
		let nextsec = sec + 60;
		let leap = nextleapsecond(nextsec).filter(|(t, _)| *t == nextsec).is_some();

		// Increment the clock
		time.sec = nextsec;
		time.nsec = 0;

		Ok(Message::new_with_alt(am, am, ns, leap))
	}
}

/// Possible amplitude modulated signal bit values.
#[derive(Clone, Copy)]
enum AMBit {
	/// Binary value 0 (`false`) or 1 (`true`).
	Value(bool),
	/// Special marker bit.
	Marker
}

/// State machine for transmitting messages.
#[derive(Clone, Copy)]
enum WriterState {
	/// Transmitting start of message indicator.
	Start,
	/// Transmitting a message bit. The payload indicates which bit (`u8`, 0-indexed starting with the
	/// LSB) and the value of that bit.
	Bit(u8, AMBit),
	/// Transmitting a leap second zero bit.
	Leap,
	/// Transmitting end of message indicator.
	End,
}

impl WriterState {
	/// Advance the state machine to the next state.
	///
	/// The state machine advances as follows:
	/// - `Start` => `Bit(0, AMBit::Marker, _)`
	/// - `Bit(n, _, _)` => `Bit(n + 1, AMBit::Marker, _)` if `n % 10 == 8` else
	///   `Bit(n + 1, AMBit::Value(_), _)`
	/// - `Bit(58, _, _)` => `Leap` if `message.leap` else `End`
	/// - `Leap` => `End`
	/// - `End` => `Start`
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance(&mut self, message: &mut Message) {
		*self = match *self {
			WriterState::Start => WriterState::Bit(0, AMBit::Marker),
			WriterState::Bit(bit, _) => {
				message.packed >>= 1;
				if bit < 58 {
					if bit % 10 == 8 {
						WriterState::Bit(bit + 1, AMBit::Marker)
					} else {
						WriterState::Bit(bit + 1, AMBit::Value(message.packed & 1 > 0))
					}
				} else if message.leap {
					WriterState::Leap
				} else {
					WriterState::End
				}
			},
			WriterState::Leap => WriterState::End,
			WriterState::End => WriterState::Start
		}
	}

	/// Advance the state machine to a given bit.
	///
	/// Automatically advances back to `Start` state if appropriate.
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance_to(&mut self, message: &mut Message, bit: u8) {
		*self = if bit < 59 {
			message.packed >>= bit;
			if bit % 10 == 9 {
				WriterState::Bit(bit, AMBit::Marker)
			} else {
				WriterState::Bit(bit, AMBit::Value(message.packed & 1 > 0))
			}
		} else if message.leap {
			WriterState::Leap
		} else {
			WriterState::End
		}
	}
}

/// Make a writer to transmit JJY messages sampled at `S` Hz.
///
/// Returns a closure with state initialized to begin transmitting a sequence of messages. The
/// closure takes two inputs:
/// 1. The message to transmit. This value is consumed during transmission.
/// 2. The buffer to write the transmitted values into (ranging [-1, 1]).
///
/// The closure returns a tuple with two values:
/// 1. The number of samples written. This is typically the number of samples in the input buffer,
///    but can be less if the message is transmitted completely.
/// 2. A boolean indicating whether the message has been transmitted completely.
///
/// The writer maintains state, so subsequent calls to the closure will continue writing the
/// message until it is completely written. After message completion, another message can be
/// transmitted simply by calling with a new message.
///
/// The returned closure operates in sample space rather than absolute time, meaning all time
/// increments are `1/S` seconds.
///
/// *Note: this writer actually writes messages with a 20 kHz carrier, so the true 40/60 kHz
/// carrier signal is the second/third harmonic of the output. This is because a 40/60 kHz signal
/// cannot be adequately sampled at common audio output frequencies.*
///
/// # Examples
///
/// ```
/// # use signals::jjy::{JJY, make_writer};
/// # use signals::MessageGenerator;
/// // Construct a JJY object to generate messages
/// let d = JJY::new(None).expect("Error reading New York timezone");
///
/// // Get a message for the current time
/// let m = d.get_message(&mut time::now().unwrap()).expect("Time must be >=0");
/// // Convert from absolute time to sample time
/// let mut s = m.sample::<48000>();
/// // Make a writer that converts the message into wire format at 48 kHz
/// let mut writer = make_writer::<48000>();
/// // Create a buffer to write 21.33ms of signal at a time
/// let mut buf = Vec::<f32>::with_capacity(1024);
/// unsafe {
/// 	buf.set_len(1024);
/// }
/// let buf = buf.as_mut_slice();
///
/// loop {
/// 	// Write the message to the buffer
/// 	let (_i, done) = writer(&mut s, buf);
/// 	// Use the results in buf
/// 	if done { break; }
/// };
/// ```
pub fn make_writer<const S: u64>() -> impl FnMut(&mut SampledMessage<S>, &mut [f32]) -> (usize, bool) {
	let mut i: u64 = 0;
	let mut bitstart: u64 = 0;
	let mut state = WriterState::Start;
	move |message: &mut SampledMessage<S>, data: &mut [f32]| -> (usize, bool) {
		let message = &mut message.0;

		// Move to the right bit position if we're starting mid-message
		if message.delay > 0 {
			let m = message.delay as u64;
			let bit = m / S; // 1 bit per second
			bitstart = i + (bit * S);
			i += m;
			message.delay = 0;
			state.advance_to(message, bit as u8);
		} else if let WriterState::Start = state {
			state.advance(message);
		}

		let start = i;
		let mut bitend = bitstart + S;
		let mut message_completed = false;
		for sample in data.iter_mut() {
			let timing_on = match state {
				WriterState::Bit(_, AMBit::Marker) | WriterState::End => S*2/10, // 200ms
				WriterState::Bit(_, AMBit::Value(true)) => S*5/10, // 500ms
				WriterState::Bit(_, AMBit::Value(false)) | WriterState::Leap => S*8/10, // 800ms
				_ => 0,
			};

			// Calculate amplitude modulation
			let power = if i < bitstart + timing_on {
				1.0
			} else {
				0.1
			};

			let pos = (i % S) as f32 / S as f32;
			// Constant 0.58236424 ensures that the signal crosses 55% of amplitude on the zero second
			// marker start, i.e. arcsin(0.55)
			*sample = power * sin32(PI * 2. * 60000. / 3. * pos + 0.58236424);
			i += 1;

			if i >= bitend {
				bitstart = i;
				bitend = bitstart + S;
				state.advance(message);
				if let WriterState::Start = state {
					message_completed = true;
					break;
				}
			}
		}

		((i - start) as usize, message_completed)
	}
}

#[cfg(test)]
mod tests {
	extern crate std;
	use std::vec::Vec;
	use time::tz;
	use super::*;

	#[test]
	fn message_test() {
		let timezone = tz::parse_tzstring_const!(b"JST-9");
		// Fri, Jun 10 2016 17:15:18 UTC
		let m = MessageUncompressed::new(1465546518, &timezone).unwrap();
		assert_eq!(m.min_ones, 5);
		assert_eq!(m.min_tens, 1);
		assert_eq!(m.hour_ones, 7);
		assert_eq!(m.hour_tens, 1);
		assert_eq!(m.yday_ones, 2);
		assert_eq!(m.yday_tens, 6);
		assert_eq!(m.yday_huns, 1);
		assert_eq!(m.year_ones, 6);
		assert_eq!(m.year_tens, 1);
		assert_eq!(m.leapsecond, 0x0);
		assert_eq!(m.day_of_week, 5);

		let a = m.pack();
		assert_eq!(a.reverse_bits(), 0x1284E130840B2800);
	}

	#[test]
	fn timing_test() {
		let jjy = JJY::new(None).unwrap();
		// Sun, May 26, 2024. 16:57:25 UTC.
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let message = jjy.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742680);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x538021220C120800);
		assert_eq!(message.delay, 25123456789);
		assert_eq!(message.leap, false);

		let message = jjy.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742740);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x540021220C120800);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);

		time.sec = 741484740;
		let message = jjy.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484800);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x548101408849A600);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, true);

		let message = jjy.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484860);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x000121408049A000);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);
	}

	fn get_message(j: &JJY, time: &mut TimeSpec) -> SampledMessage<48000> {
		j.get_message(time).unwrap().sample()
	}

	fn calculate_power(buffer: &[f32]) -> f32 {
		if buffer.len() == 0 {
			0.
		} else {
			buffer.iter().copied().reduce(|acc, x| acc + x.abs()).unwrap_or(0.) / (buffer.len() as f32)
		}
	}

	fn check_is_high(buffer: &[f32]) {
		let p = calculate_power(buffer);
		assert!((p - 0.63).abs() < 0.01, "High signal expected power of 0.63, saw {}", p)
	}

	fn check_is_low(buffer: &[f32]) {
		let p = calculate_power(buffer);
		assert!((p - 0.063).abs() < 0.01, "Low signal expected power of 0.095, saw {}", p)
	}

	fn check_is_marker(buffer: &[f32], bound: usize) {
		check_is_high(&buffer[bound..bound + 9600]);
		check_is_low(&buffer[bound + 9600..bound + 48000]);
	}

	fn check_is_one(buffer: &[f32], bound: usize) {
		check_is_high(&buffer[bound..bound + 24000]);
		check_is_low(&buffer[bound + 24000..bound + 48000]);
	}

	fn check_is_zero(buffer: &[f32], bound: usize) {
		check_is_high(&buffer[bound..bound + 38400]);
		check_is_low(&buffer[bound + 38400..bound + 48000]);
	}

	#[test]
	fn transmit_test() {
		let mut writer = make_writer();
		let jjy = JJY::new(None).unwrap();
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let mut buf = Vec::<f32>::with_capacity(2900000);
		unsafe {
			buf.set_len(2900000);
		}
		let buf = buf.as_mut_slice();

		let mut message = get_message(&jjy, &mut time);
		assert_eq!(message.0.packed.reverse_bits(), 0x538021220C120800);
		assert_eq!(writer(&mut message, buf).0, 1674075);
		check_is_high(&buf[0..32474]);
		check_is_low(&buf[32474..42075]);
		let mut bound = 42075;
		let mut packed = 0x538021220C120800_u64.reverse_bits() >> 26;
		for i in 26..60 {
			let bit = (packed & 1) > 0;
			if i % 10 == 9 {
				check_is_marker(buf, bound);
			} else if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			}
			bound += 48000;

			packed >>= 1;
		}

		message = get_message(&jjy, &mut time);
		assert_eq!(writer(&mut message, buf).0, 2880000);
		let mut packed = 0x540021220C120800_u64.reverse_bits() >> 1;
		check_is_marker(buf, 0);
		let mut bound = 48000;
		for i in 1..59 {
			let bit = (packed & 1) > 0;
			if i % 10 == 9 {
				check_is_marker(buf, bound);
			} else if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			}
			bound += 48000;

			packed >>= 1;
		}
	}

	#[test]
	fn module_doctest() {
		// Documentation for MessageUncompressed
		// Japan (JST) timezone, UTC+9
		let timezone = time::tz::parse_tzstring_const!(b"JST-9");

		// Saturday, July 4, 2020. 11:36:58 JST
		let m = MessageUncompressed::new(1593830218, &timezone).unwrap();
		assert_eq!(m.min_ones, 6);            // Minute 36
		assert_eq!(m.min_tens, 3);
		assert_eq!(m.hour_ones, 1);           // Hour 11
		assert_eq!(m.hour_tens, 1);
		assert_eq!(m.yday_ones, 6);           // Day 186
		assert_eq!(m.yday_tens, 8);
		assert_eq!(m.yday_huns, 1);
		assert_eq!(m.year_ones, 0);           // Year [20]20
		assert_eq!(m.year_tens, 2);
		assert_eq!(m.day_of_week, 6);         // Saturday
		assert_eq!(m.leapsecond, 0);          // No leap second this month

		let packed = m.pack();
		assert_eq!(packed.reverse_bits(), 0x3304214180103000);
	}
}
