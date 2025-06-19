//! Support for transmitting the MSF time signal.
//!
//! See [MSF documentation](https://en.wikipedia.org/wiki/Time_from_NPL_(MSF)) for details. This
//! module implements the slow code format of the MSF time signal, since the fast code was
//! discontinued in 1998. All features of the slow code are implemented.
//!
//! # Examples
//! ```
//! # use signals::{msf, MessageGenerator};
//! # use time;
//! // Construct an MSF object to generate messages
//! let d = msf::new(None).expect("Error reading default timezone");
//!
//! // Get a message for the current time
//! let m = d.get_message(&mut time::now().unwrap());
//! match m {
//! 	Ok(m) => {
//! 		// Make a writer that converts the message into wire format at 48 kHz
//! 		let mut writer = msf::make_writer::<48000>();
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
use crate::common::DUT1_TIMES;

/// All known UT1-UTC offsets.
///
/// Values are pre-encoded for transmission, where the MSB eight bits indicate positive offsets and
/// the LSB eight bits indicate negative offsets. Each bit is 1 when `abs(offset) >= bit`, for
/// example `0xE0 -> 0b11100000` means `0.3` since three bits are set. Only offsets between between
/// [0.0, +-0.8] are supported. Full example: `0x00F8` means `-0.5`.
///
/// This constant is split into two tables ([`DUT1_TIMES`] and [`DUT1_VALS`]) to optimize for space.
/// The two tables must be kept in sync, where `DUT1_TIMES` represents the time of a change in the
/// UT1-UTC offset, and `DUT1_VALS` represents the encoded UT1-UTC offset at that time.
const DUT1_VALS: [u16; 113] = [
	0xC000, 0x8000, 0x0000, 0x0080,
	0x00F8, 0xE000, 0xC000, 0x8000,
	0x0000, 0x00E0, 0xFC00, 0xF000,
	0xE000, 0xC000, 0x0000, 0x0080,
	0xFF00, 0xE000, 0xC000, 0x8000,
	0x0000, 0x0080, 0x00C0, 0x00E0,
	0x00F0, 0xF800, 0xF000, 0xE000,
	0xC000, 0x8000, 0x0000, 0x0080,
	0x00C0, 0x00E0, 0x00F0, 0x00F8,
	0xF800, 0xF000, 0xE000, 0xC000,
	0x8000, 0x0000, 0x0080, 0x00C0,
	0x00E0, 0xFE00, 0xFC00, 0xF800,
	0xF000, 0xE000, 0xC000, 0x8000,
	0x0000, 0x0080, 0x00C0, 0x00E0,
	0x00F0, 0x00F8, 0x00FC, 0xE000,
	0xC000, 0x8000, 0x0000, 0x0080,
	0x00C0, 0x00E0, 0x00F0, 0x00F8,
	0x00FC, 0xE000, 0xC000, 0x8000,
	0x0000, 0x0080, 0x00C0, 0x00E0,
	0x00F0, 0x00F8, 0x00FC, 0xF000,
	0xE000, 0xC000, 0x8000, 0x0000,
	0x0080, 0x00C0, 0x00E0, 0x00F0,
	0x00F8, 0x00FC, 0x00FE, 0xE000,
	0xC000, 0x8000, 0x0000, 0x0080,
	0x00C0, 0x00E0, 0x00F0, 0xFC00,
	0xF800, 0xF000, 0xE000, 0xC000,
	0x8000, 0x0000, 0x0080, 0x00C0,
	0x0080, 0x0000, 0x8000, 0x0000,
	0x8000
];

/// An unpacked / uncompressed MSF message.
///
/// This type contains all of the components of the encoded MSF message, but in an unpacked
/// format that is easier to inspect. See [`MessageUncompressed::pack`] for details on getting and
/// using the packed message, which can be transmitted.
///
/// # Examples
/// ```ignore
/// // UK timezone, UTC+0 (standard time) / UTC+1 (daylight saving time)
/// let timezone = tz::parse_tzstring_const!(b"GMT0BST,M3.5.0/1,M10.5.0");
///
/// // Saturday, July 4, 2020. 11:56:58 UTC+1 / 10:56:58 UTC.
/// let m = MessageUncompressed::new(1593860218, &timezone).unwrap();
/// assert_eq!(m.min_ones, 6);    // Minute 56
/// assert_eq!(m.min_tens, 5);
/// assert_eq!(m.hour_ones, 1);   // Hour 11
/// assert_eq!(m.hour_tens, 1);
/// assert_eq!(m.day_ones, 4);    // Day 04
/// assert_eq!(m.day_tens, 0);
/// assert_eq!(m.month_ones, 7);  // Month 07
/// assert_eq!(m.month_tens, 0);
/// assert_eq!(m.year_ones, 0);   // Year [20]20
/// assert_eq!(m.year_tens, 2);
/// assert_eq!(m.day_of_week, 6); // Saturday (0=Sunday, 6=Saturday)
/// assert_eq!(m.summer_time, 1); // BST in effect, no change within the hour
///
/// let packed = m.pack();
/// assert_eq!(a.reverse_bits(), 0x8000101C4C8D67E0);
/// assert_eq!(b.reverse_bits(), 0x80600000000000E0);
/// ```
struct MessageUncompressed {
	/// DUT1 encoded value. See [`DUT1_TIMES`] for more details.
	dut1: u16,
	/// Year ones digit, ranged [0, 9]
	year_ones: u8,
	/// Year tens digit, ranged [0, 9]
	year_tens: u8,
	/// Month ones digit, ranged [0, 9]
	month_ones: u8,
	/// Month tens digit, ranged [0, 1]
	month_tens: u8,
	/// Day of month ones digit, ranged [0, 9]
	day_ones: u8,
	/// Day of month tens digit, ranged [0, 3]
	day_tens: u8,
	/// Day of week, ranged [0, 6], where 0=Sunday, 6=Saturday
	day_of_week: u8,
	/// Hour ones digit, ranged [0, 9]
	hour_ones: u8,
	/// Hour tens digit, ranged [0, 2]
	hour_tens: u8,
	/// Minute ones digit, ranged [0, 9]
	min_ones: u8,
	/// Minute tens digit, ranged [0, 5]
	min_tens: u8,
	/// Summer time (DST) flags:
	/// - Bits 6-7: Unused
	/// - Bit 5: Summer time changing in the next hour
	/// - Bits 1-4: Unused
	/// - Bit 0: Summer time currently in effect
	summer_time: u8
}

impl MessageUncompressed {
	/// Create a new MSF message.
	///
	/// Input `time` should be greater than or equal to zero. `timezone` is used to set the UTC offset
	/// configuration for `time` and determine if summer time (DST) is in effect.
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTime`] if `time < 0`.
	fn new(time: i64, timezone: &Timezone) -> Result<MessageUncompressed, MessageError> {
		let date = timezone.date(time).ok_or(MessageError::UnsupportedTime(time))?;

		// Get DUT1 value (difference between UTC and UT1)
		let dut1 = (|| {
			const { assert!(DUT1_TIMES.len() == DUT1_VALS.len()); }
			for (&t, &d) in DUT1_TIMES.iter().zip(DUT1_VALS.iter()).rev() {
				if t <= time { return d }
			}
			0
		})();

		// Determine if there's a DST change in the next hour + 1 minute
		let dstchange = (date.info.isdst != timezone.info(time + 3660).isdst) as u8;

		Ok(MessageUncompressed {
			dut1,
			year_ones: date.tm.year % 10,
			year_tens: (date.tm.year / 10) % 10,
			month_ones: date.tm.mon % 10,
			month_tens: date.tm.mon / 10,
			day_ones: date.tm.day % 10,
			day_tens: date.tm.day / 10,
			day_of_week: date.tm.wday,
			hour_ones: date.tm.hour % 10,
			hour_tens: date.tm.hour / 10,
			min_ones: date.tm.min % 10,
			min_tens: date.tm.min / 10,
			summer_time: (dstchange << 5) | (date.info.isdst as u8)
		})
	}

	/// Pack the message into the bit format used to transmit.
	///
	/// Returns a tuple of two values, corresponding to the A and B message bits, respectively. The
	/// LSB is the first bit to transmit. The MSB 4 bits are unused and not to be transmitted.
	fn pack(&self) -> (u64, u64) {
		// MSF uses odd parity bits over the year, day, day of week, and time.
		let year =  (self.year_ones & 0xf)
				 | ((self.year_tens & 0x7) << 4);
		let year_parity = (year.count_ones() & 0x1) ^ 0x1;

		let day =  (self.day_ones & 0xf)
				| ((self.day_tens & 0x3) << 4);
		let day_parity = (day.count_ones() & 0x1) ^ 0x1;

		let dow_parity = (self.day_of_week.count_ones() & 0x1) ^ 0x1;

		let time = ((self.hour_tens as u16 & 0x3) << 11)
				 | ((self.hour_ones as u16 & 0xf) << 7)
				 | ((self.min_tens  as u16 & 0x7) << 4)
				 |  (self.min_ones  as u16 & 0xf);
		let time_parity = (time.count_ones() & 0x1) ^ 0x1;

		let mut a: u64 = 0x80000000000007E0;
		a |=  (year             as u64)        << 39;
		a |= ((self.month_tens  as u64) & 0x1) << 38;
		a |= ((self.month_ones  as u64) & 0xf) << 34;
		a |=  (day              as u64)        << 28;
		a |= ((self.day_of_week as u64) & 0x7) << 25;
		a |=  (time             as u64)        << 12;

		let mut b: u64 = 0x8000000000000000;
		b |=  (self.dut1                as u64)         << 47;
		b |=  (year_parity              as u64)         << 9;
		b |=  (day_parity               as u64)         << 8;
		b |=  (dow_parity               as u64)         << 7;
		b |=  (time_parity              as u64)         << 6;
		b |= ((self.summer_time         as u64) & 0x21) << 5;

		(a.reverse_bits(), b.reverse_bits())
	}
}

/// MSF message generator.
///
/// Messages returned from [`MSF::get_message`] should be used with the writer returned by
/// [`make_writer`].
///
/// # Examples
///
/// ```
/// # use signals::msf::MSF;
/// # use signals::MessageGenerator;
/// // Construct an MSF object to generate messages
/// let d = MSF::new(None).expect("Error reading default timezone");
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
pub struct MSF {
	uk_tz: Timezone
}

/// Construct a new MSF object.
///
/// This is a convenience function, see [`MSF::new`] for details.
#[inline(always)]
pub fn new(timezone: Option<Timezone>) -> Result<MSF, MessageError> {
	MSF::new(timezone)
}

impl MSF {
	/// Construct a new MSF object.
	///
	/// If the input `timezone` is `None`, this function defaults to `GMT0BST,M3.5.0/1,M10.5.0` or
	/// reading `/usr/share/zoneinfo/Europe/London` (feature `std`) for timezone information.
	///
	/// # Errors
	///
	/// Returns [`MessageError::TimezoneError`] if there was an error reading
	/// `/usr/share/zoneinfo/Europe/London`.
	///
	/// # Examples
	///
	/// ```
	/// # use signals::msf::MSF;
	/// let d = MSF::new(None);
	/// match d {
	/// 	Ok(_d) => {
	/// 		// Create & use messages
	/// 	},
	/// 	Err(_) => {
	/// 		// Known valid offset (UTC / UTC+1) that cannot fail
	/// 		let _d = MSF::new(
	/// 			Some(time::tz::parse_tzstring_const!(b"GMT0BST,M3.5.0/1,M10.5.0"))
	/// 		).unwrap();
	/// 		// Create & use messages
	/// 	}
	/// }
	/// ```
	pub fn new(timezone: Option<Timezone>) -> Result<MSF, MessageError> {
		match timezone {
			Some(t) => Ok(MSF { uk_tz: t }),
			#[cfg(all(not(target_arch = "wasm32"), feature = "std"))]
			None => tz::parse_file("/usr/share/zoneinfo/Europe/London")
					.map(|t| MSF { uk_tz: t })
					.map_err(|e| MessageError::TimezoneError(e)),
			#[cfg(any(target_arch = "wasm32", not(feature = "std")))]
			None => Ok(MSF {
				uk_tz: tz::parse_tzstring_const!(b"GMT0BST,M3.5.0/1,M10.5.0")
			})
		}
	}
}

impl MessageGenerator for MSF {
	/// Get a message for the given time.
	///
	/// This function returns a message for the minute that started on or before `time`, i.e. the
	/// message represents the instant at the **beginning** of the transmission.
	///
	/// All fields of the returned message are used:
	/// - [`Message::packed`]: the A message bits, LSB first.
	/// - [`Message::packed_alt`]: the B message bits, LSB first.
	/// - [`Message::delay`]: the current time within the minute, in nanoseconds.
	/// - [`Message::leap`]: true if a leap second should be inserted in this message.
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
	/// # use signals::msf::MSF;
	/// # use signals::MessageGenerator;
	/// # use time::TimeSpec;
	/// let msf = MSF::new(None).unwrap();
	/// // Sun, May 26, 2024. 16:57:25 UTC.
	/// let mut time = TimeSpec {
	/// 	sec: 1716742645,
	/// 	nsec: 123456789
	/// };
	///
	/// let message = msf.get_message(&mut time).unwrap();
	/// assert_eq!(time.sec, 1716742680);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x8000121660BD77E0);
	/// assert_eq!(message.packed_alt.reverse_bits(), 0x80000000000002A0);
	/// assert_eq!(message.delay, 25123456789);
	/// assert_eq!(message.leap, false);
	///
	/// let message = msf.get_message(&mut time).unwrap();
	/// assert_eq!(time.sec, 1716742740);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x8000121660BD87E0);
	/// assert_eq!(message.packed_alt.reverse_bits(), 0x80000000000002A0);
	/// assert_eq!(message.delay, 0);
	/// assert_eq!(message.leap, false);
	/// ```
	fn get_message(&self, time: &mut TimeSpec) -> Result<Message, MessageError> {
		// Find the start of this minute (exactly)
		let time_in_min = time.sec % 60;
		let sec = time.sec - time_in_min;

		// Compute the message
		let message = MessageUncompressed::new(sec, &self.uk_tz)?;
		let (a, b) = message.pack();

		// Calculate where we are within the minute (in nanoseconds)
		let ns = time_in_min * 1000000000 + time.nsec;

		// Calculate if this is a minute with leap second
		let nextsec = sec + 60;
		let leap = nextleapsecond(nextsec).filter(|(t, _)| *t == nextsec).is_some();

		// Increment the clock
		time.sec = nextsec;
		time.nsec = 0;

		Ok(Message::new_with_alt(a, b, ns, leap))
	}
}

/// State machine for transmitting messages.
#[derive(Clone, Copy)]
enum WriterState {
	/// Transmitting start of message indicator.
	Start,
	/// Transmitting a message bit. The payload indicates which bit (u8, 0-indexed starting with LSB)
	/// and the values of the A and B bits.
	Bit(u8, bool, bool),
	/// Transmitting a leap second bit.
	Leap
}

impl WriterState {
	/// Advance the state machine to the next state.
	///
	/// The state machine advances as follows:
	/// - `Start` => `Bit(1, _, _)`
	/// - `Bit(n, _, _)` => `Bit(n + 1, _, _)`
	/// - `Bit(16, _, _)` => `Leap` if `message.leap` else `Bit(17, _, _)`
	/// - `Leap` => `Bit(17, _, _)`
	/// - `Bit(59, _, _` => `Start`
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance(&mut self, message: &mut Message) {
		*self = match *self {
			WriterState::Start => {
				message.packed >>= 1;
				message.packed_alt >>= 1;
				WriterState::Bit(1, message.packed & 1 > 0, message.packed_alt & 1 > 0)
			}
			WriterState::Bit(bit, _, _) => {
				message.packed >>= 1;
				message.packed_alt >>= 1;
				if bit == 16 && message.leap {
					WriterState::Leap
				} else if bit < 59 {
					WriterState::Bit(bit + 1, message.packed & 1 > 0, message.packed_alt & 1 > 0)
				} else {
					WriterState::Start
				}
			},
			WriterState::Leap => WriterState::Bit(17, message.packed & 1 > 0, message.packed_alt & 1 > 0)
		}
	}

	/// Advance the state machine to a given bit.
	///
	/// Automatically advances back to `Start` state if appropriate.
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance_to(&mut self, message: &mut Message, bit: u8) {
		*self = if bit == 0 {
			WriterState::Start
		} else if message.leap && bit == 17 {
			message.packed >>= 17;
			message.packed_alt >>= 17;
			WriterState::Leap
		} else {
			let bit = if message.leap && bit > 16 { bit - 1 } else { bit };
			message.packed >>= bit;
			message.packed_alt >>= bit;
			WriterState::Bit(bit, message.packed & 1 > 0, message.packed_alt & 1 > 0)
		}
	}
}

/// Make a writer to transmit MSF messages sampled at `S` Hz.
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
/// *Note: this writer actually writes messages with a 20 kHz carrier, so the true 60 kHz carrier
/// signal is the third harmonic of the output. This is because a 60 kHz signal cannot be
/// adequately sampled at common audio output frequencies.*
///
/// # Examples
///
/// ```
/// # use signals::msf::{MSF, make_writer};
/// # use signals::MessageGenerator;
/// // Construct a MSF object to generate messages
/// let d = MSF::new(None).expect("Error reading London timezone");
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
		}

		let start = i;
		let mut bitend = bitstart + S;
		let mut message_completed = false;
		for sample in data.iter_mut() {
			let off = match state {
				WriterState::Start => i < bitstart + S*5/10, // Off if <500ms
				WriterState::Leap => i < bitstart + S/10, // Off if <100ms
				WriterState::Bit(_, a, b) => {
					if i < bitstart + S/10 { // Off if <100ms
						true
					} else if i < bitstart + S*2/10 { // Off if 100-200ms and a is 1
						a
					} else if i < bitstart + S*3/10 { // Off is 200-300ms and b is 1
						b
					} else {
						false
					}
				}
			};

			if off {
				*sample = 0.0;
			} else {
				let pos = (i % S) as f32 / S as f32;
				*sample = sin32(PI * 2. * 60000. / 3. * pos);
			}
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
	use super::*;

	#[test]
	fn message_test() {
		// UK timezone (GMT/BST)
		let timezone = tz::parse_tzstring_const!(b"GMT0BST,M3.5.0/1,M10.5.0");

		// Saturday, July 4, 2020. 11:56:00 BST (10:56:00 UTC)
		let time = 1593860160;

		let m = MessageUncompressed::new(time, &timezone).unwrap();

		assert_eq!(m.min_ones, 6);    // Minute 56
		assert_eq!(m.min_tens, 5);
		assert_eq!(m.hour_ones, 1);   // Hour 11
		assert_eq!(m.hour_tens, 1);
		assert_eq!(m.day_ones, 4);    // Day 04
		assert_eq!(m.day_tens, 0);
		assert_eq!(m.month_ones, 7);  // Month 07
		assert_eq!(m.month_tens, 0);
		assert_eq!(m.year_ones, 0);   // Year [20]20
		assert_eq!(m.year_tens, 2);
		assert_eq!(m.day_of_week, 6); // Saturday
		assert_eq!(m.summer_time, 1); // BST in effect, no change coming within the hour

		let (a, b) = m.pack();
		assert_eq!(a.reverse_bits(), 0x8000101C4C8D67E0);
		assert_eq!(b.reverse_bits(), 0x80600000000000E0);
	}

	#[test]
	fn timing_test() {
		let msf = MSF::new(None).unwrap();
		// Sun, May 26, 2024. 16:57:25 UTC.
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let message = msf.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742680);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x8000121660BD77E0);
		assert_eq!(message.packed_alt.reverse_bits(), 0x80000000000002A0);
		assert_eq!(message.delay, 25123456789);
		assert_eq!(message.leap, false);

		let message = msf.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742740);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x8000121660BD87E0);
		assert_eq!(message.packed_alt.reverse_bits(), 0x80000000000002A0);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);

		time.sec = 741484740;
		let message = msf.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484800);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x8000099C180597E0);
		assert_eq!(message.packed_alt.reverse_bits(), 0x8070000000000060);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, true);

		let message = msf.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484860);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x8000099C180807E0);
		assert_eq!(message.packed_alt.reverse_bits(), 0xFE00000000000020);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);
	}

	fn get_message(m: &MSF, time: &mut TimeSpec) -> SampledMessage<48000> {
		m.get_message(time).unwrap().sample()
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
		assert!(p.abs() < 0.01, "Low signal expected power of 0.00, saw {}", p)
	}

	fn check_bits(buffer: &[f32], bound: usize, a: bool, b: bool) {
		check_is_low(&buffer[bound..bound + 4800]);
		if a {
			check_is_low(&buffer[bound + 4800..bound + 9600]);
		} else {
			check_is_high(&buffer[bound + 4800..bound + 9600]);
		}
		if b {
			check_is_low(&buffer[bound + 9600..bound + 14400]);
		} else {
			check_is_high(&buffer[bound + 9600..bound + 14400]);
		}
		check_is_high(&buffer[bound + 14400..bound + 48000]);
	}

	#[test]
	fn transmit_test() {
		let mut writer = make_writer();
		let msf = MSF::new(None).unwrap();
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let mut buf = Vec::<f32>::with_capacity(2900000);
		unsafe {
			buf.set_len(2900000);
		}
		let buf = buf.as_mut_slice();

		let mut message = get_message(&msf, &mut time);
		assert_eq!(message.0.packed.reverse_bits(), 0x8000121660BD77E0);
		assert_eq!(message.0.packed_alt.reverse_bits(), 0x80000000000002A0);
		assert_eq!(writer(&mut message, buf).0, 1674075);
		check_is_high(&buf[0..42075]);
		let mut bound = 42075;
		let mut a = 0x8000121660BD77E0_u64.reverse_bits() >> 26;
		let mut b = 0x80000000000002A0_u64.reverse_bits() >> 26;
		for _ in 26..60 {
			let abit = (a & 1) > 0;
			let bbit = (b & 1) > 0;
			check_bits(buf, bound, abit, bbit);
			bound += 48000;

			a >>= 1;
			b >>= 1;
		}

		message = get_message(&msf, &mut time);
		assert_eq!(writer(&mut message, buf).0, 2880000);
		let mut a = 0x8000121660BD87E0_u64.reverse_bits() >> 1;
		let mut b = 0x80000000000002A0_u64.reverse_bits() >> 1;
		check_is_low(&buf[0..24000]);
		check_is_high(&buf[24000..48000]);
		let mut bound = 48000;
		for _ in 1..59 {
			let abit = (a & 1) > 0;
			let bbit = (b & 1) > 0;
			check_bits(buf, bound, abit, bbit);
			bound += 48000;

			a >>= 1;
			b >>= 1;
		}
	}

	#[test]
	fn module_doctest() {
		// UK timezone, UTC+0 (standard time) / UTC+1 (daylight saving time)
		let timezone = tz::parse_tzstring_const!(b"GMT0BST,M3.5.0/1,M10.5.0");

		// Saturday, July 4, 2020. 11:56:58 UTC+1 / 10:56:58 UTC.
		let m = MessageUncompressed::new(1593860218, &timezone).unwrap();
		assert_eq!(m.min_ones, 6);    // Minute 56
		assert_eq!(m.min_tens, 5);
		assert_eq!(m.hour_ones, 1);   // Hour 11
		assert_eq!(m.hour_tens, 1);
		assert_eq!(m.day_ones, 4);    // Day 04
		assert_eq!(m.day_tens, 0);
		assert_eq!(m.month_ones, 7);  // Month 07
		assert_eq!(m.month_tens, 0);
		assert_eq!(m.year_ones, 0);   // Year [20]20
		assert_eq!(m.year_tens, 2);
		assert_eq!(m.day_of_week, 6); // Saturday (0=Sunday, 6=Saturday)
		assert_eq!(m.summer_time, 1); // BST in effect, no change within the hour

		let (a, b) = m.pack();
		assert_eq!(a.reverse_bits(), 0x8000101C4C8D67E0);
		assert_eq!(b.reverse_bits(), 0x80600000000000E0);
	}
}
