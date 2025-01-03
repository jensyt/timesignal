//! Support for transmitting the DCF77 time signal.
//!
//! See [DCF77 documentation](https://en.wikipedia.org/wiki/DCF77#Time_code_details) for details.
//!
//! # Examples
//!
//! ```
//! // Construct a DCF77 object to generate messages
//! let d = DCF77::new(None).unwrap();
//!
//! // Get a message for the current time
//! let m = d.get_message(&mut crate::time::currenttime().unwrap());
//! match m {
//! 	Ok(mut m) => {
//! 		// Convert real time (nanoseconds) to sample time (48 kHz)
//! 		m.delay = (m.delay * 48) / 1000000;
//!
//! 		// Make a writer that converts the message into wire format at 48 kHz
//! 		let mut writer = make_writer();
//! 		// Create a buffer with enough space to hold 15s of the encoded message
//! 		let mut buf = Vec::<f32>::with_capacity(800000);
//! 		unsafe {
//! 			buf.set_len(800000);
//! 		}
//! 		let buf = buf.as_mut_slice();
//!
//! 		// Write the 60s message in four 15s chunks
//! 		for _ in 0..4 {
//! 			// Write the message to the buffer
//! 			writer(&mut m, buf);
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

use std::{error, f32::consts::PI, fmt};
use crate::{time::{nextleapsecond, Seconds, TimeSpec}, tz::{self, Timezone}, Message};

/// Pseudorandom chip sequence for phase modulated signal.
///
/// Described in detail [here](https://en.wikipedia.org/wiki/DCF77#Phase_modulation). For ease of
/// use, this chip sequence is stored with one bit per byte, where each byte has a value of either
/// zero or one.
///
/// # Examples
/// ```
/// let bit = 1;
/// for chip in PM_CHIP_SEQUENCE {
/// 	let _phase = PI / 180. * if bit ^ chip == 1 {
/// 					-15.6
/// 				} else {
/// 					15.6
/// 				};
///
/// 	// Use _phase to modulate carrier
/// }
/// ```
const PM_CHIP_SEQUENCE: &[u8; 512] = include_bytes!("../assets/dcf77_chip_sequence.bin");

/// The error type for constructing DCF77 messages.
pub enum Error {
	/// The input time is before the Unix epoch (Jan 1, 1970) and not supported. The unsupported time
	/// is provided in the payload.
	UnsupportedTime(i64),
	/// Error parsing the default timezone. The underlying error is provided in the payload.
	TimezoneError(tz::Error)
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Error::UnsupportedTime(x) => write!(f, "Unsupported time: {}", x),
			Error::TimezoneError(x) => write!(f, "Timezone error: {}", x)
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
		match self {
			Error::UnsupportedTime(_) => None,
			Error::TimezoneError(x) => Some(x)
		}
	}
}

/// An unpacked / uncompressed DCF77 message.
///
/// This type contains all of the components of the encoded DCF77 message, but in an unpacked
/// format that is easier to inspect. See [`MessageUncompressed::pack`] for details on getting and
/// using the packed message, which can be transmitted to a watch.
///
/// # Examples
///
/// ```
/// // Berlin (CET/CEST) timezone, UTC+1 (standard time) / UTC+2 (daylight savings time)
/// let timezone = crate::tz::parse_file("/usr/share/zoneinfo/Europe/Berlin").ok();
///
/// // Sunday, May 26, 2024. 18:58:25 UTC+2 / 16:58:25 UTC.
/// let m = MessageUncompressed::new(1716742705, &timezone).unwrap();
/// assert_eq!(m.timezone, 2);   // Currently DST, no leap second or DST change in next hour
/// assert_eq!(m.min_ones, 8);   // Minute 58
/// assert_eq!(m.min_tens, 5);
/// assert_eq!(m.hour_ones, 8);  // Hour 18
/// assert_eq!(m.hour_tens, 1);
/// assert_eq!(m.day_ones, 6);   // Day 26
/// assert_eq!(m.day_tens, 2);
/// assert_eq!(m.dow, 7);        // Sunday
/// assert_eq!(m.month_ones, 5); // Month 5 (May)
/// assert_eq!(m.month_tens, 0);
/// assert_eq!(m.year_ones, 4);  // Year [20]24
/// assert_eq!(m.year_tens, 2);
///
/// let (am, pm) = m.pack();
/// assert_eq!(am, 0x090BE631B120000);
/// assert_eq!(pm, 0x090BE631B1203FF);
/// ```
struct MessageUncompressed {
	/// Timezone and announcement bits, from MSB to LSB:
	/// - Bits 4-7: unused
	/// - Bit 3: DST change happening within the next hour
	/// - Bit 2: DST (CEST) in effect
	/// - Bit 1: Standard time (CET) in effect
	/// - Bit 0: Leap second happening within the next hour
	timezone: u8,
	/// Minutes one digit, ranged [0, 9].
	min_ones: u8,
	/// Minutes tens digit, ranged [0, 5].
	min_tens: u8,
	/// Hours ones digit, ranged [0, 9].
	hour_ones: u8,
	/// Hours tens digit, ranged [0, 2].
	hour_tens: u8,
	/// Day of month ones digit, ranged [0, 9].
	day_ones: u8,
	/// Day of month tens digit, ranged [0, 3].
	day_tens: u8,
	/// Day of week, ranged [1, 7].
	dow: u8,
	/// Month ones digit, ranged [0, 9].
	month_ones: u8,
	/// Month tens digit, ranged [0, 1].
	month_tens: u8,
	/// Year ones digit, ranged [0, 9].
	year_ones: u8,
	/// Year tens digit, ranged [0, 9].
	year_tens: u8
}

impl MessageUncompressed {
	/// Create a new DCF77 message.
	///
	/// Input `time` should be greater than or equal to zero. `timezone` is used to set DST and UTC
	/// offset configurations for `time`.
	///
	/// # Errors
	///
	/// Returns [`Error::UnsupportedTime`] if `time < 0`.
	fn new(time: i64, timezone: &Timezone) -> Result<MessageUncompressed, Error> {
		let date = timezone.date(time).ok_or(Error::UnsupportedTime(time))?;

		// Announcement bits are based on the prior minute
		let tminus60 = time - 60;
		let dstchange = (timezone.info(tminus60).isdst != timezone.info(time + 3540).isdst) as u8;
		let leap = match nextleapsecond(tminus60)
						 .map(|(t, _)| t - tminus60)
						 .filter(|&t| 0 < t && t <= 3600)
		{
			Some(_) => 0x8,
			None    => 0x0
		};

		Ok(MessageUncompressed {
			timezone: if date.info.isdst { 0x2 } else { 0x4 } | dstchange | leap,
			min_ones: date.tm.min % 10,
			min_tens: date.tm.min / 10,
			hour_ones: date.tm.hour % 10,
			hour_tens: date.tm.hour / 10,
			day_ones: date.tm.day % 10,
			day_tens: date.tm.day / 10,
			dow: if date.tm.wday > 0 { date.tm.wday } else { 7 },
			month_ones: date.tm.mon % 10,
			month_tens: date.tm.mon / 10,
			year_ones: date.tm.year % 10,
			year_tens: (date.tm.year / 10) % 10
		})
	}

	/// Pack the message into the bit format used to transmit.
	///
	/// Returns a tuple of two values:
	/// - The amplitude modulated message, where the LSB is the first bit to transmit. The MSB 5 bits
	///   are unused and not to be transmitted.
	/// - The phase modulated message, where the LSB is the first bit to transmit. The MSB 4 bits are
	///   unused and not to be transmitted.
	fn pack(&self) -> (u64, u64) {
		// DCF77 uses even parity bits over the minute, hour, and date.
		let min =  (self.min_ones & 0xf)
				| ((self.min_tens & 0x7) << 4);
		let min_parity = (min.count_ones() & 0x1) as u8;

		let hour =  (self.hour_ones & 0xf)
				 | ((self.hour_tens & 0x3) << 4);
		let hour_parity = (hour.count_ones() & 0x1) as u8;

		let date =  (self.day_ones   as u32 & 0xf)
				 | ((self.day_tens   as u32 & 0x3) << 4)
				 | ((self.dow        as u32 & 0x7) << 6)
				 | ((self.month_ones as u32 & 0xf) << 9)
				 | ((self.month_tens as u32 & 0x1) << 13)
				 | ((self.year_ones  as u32 & 0xf) << 14)
				 | ((self.year_tens  as u32 & 0xf) << 18);
		let date_parity = (date.count_ones() & 0x1) as u8;

		// Bit 20 always set to 1, indicates the start of encoded time
		let mut r: u64 = 0x100000;
		r |= (self.timezone as u64 & 0xf     ) << 16;
		r |= (min           as u64 & 0x7f    ) << 21;
		r |= (min_parity    as u64 & 0x1     ) << 28;
		r |= (hour          as u64 & 0x3f    ) << 29;
		r |= (hour_parity   as u64 & 0x1     ) << 35;
		r |= (date          as u64 & 0x7fffff) << 36;
		r |= (date_parity   as u64 & 0x1     ) << 58;

		// Phase modulated signal has first 10 bits set to 1
		(r, r | 0x3ff)
	}
}

/// DCF77 message generator.
///
/// Messages returned from [`DCF77::get_message`] should be used with the writer returned by
/// [`make_writer`].
///
/// # Examples
///
/// ```
/// // Construct a DCF77 object to generate messages
/// let d = DCF77::new(None).expect("Error getting Berlin timezone data");
///
/// // Get a message for the current time
/// let m = d.get_message(&mut crate::time::currenttime().unwrap());
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
pub struct DCF77 {
	berlin_tz: Timezone
}

/// Construct a new DCF77 object.
///
/// This is a convenience function, see [`DCF77::new`] for details.
#[inline(always)]
pub fn new(timezone: Option<Timezone>) -> Result<DCF77, Error> {
	DCF77::new(timezone)
}

impl DCF77 {
	/// Construct a new DCF77 object.
	///
	/// If the input `timezone` is `None`, this function defaults to reading
	/// `/usr/share/zoneinfo/Europe/Berlin` for timezone information.
	///
	/// # Errors
	///
	/// Returns [`Error::TimezoneError`] if there was an error reading
	/// `/usr/share/zoneinfo/Europe/Berlin`.
	///
	/// # Examples
	///
	/// ```
	/// let d = DCF77::new(None);
	/// match d {
	/// 	Ok(_d) => {
	/// 		// Create & use messages
	/// 	},
	/// 	Err(_) => {
	/// 		// Known valid offset (UTC+1 / UTC+2) that cannot fail
	/// 		let _d = DCF77::new(
	/// 			crate::tz::parse_tzstring(b"CET-1CEST,M3.5.0,M10.5.0/3").ok()
	/// 		).unwrap();
	/// 		// Create & use messages
	/// 	}
	/// }
	/// ```
	pub fn new(timezone: Option<Timezone>) -> Result<DCF77, Error> {
		match timezone {
			Some(t) => Ok(DCF77 { berlin_tz: t }),
			None => tz::parse_file("/usr/share/zoneinfo/Europe/Berlin")
						.map(|t| DCF77 { berlin_tz: t })
						.map_err(|e| Error::TimezoneError(e))
		}
	}

	/// Get a message for the given time.
	///
	/// This function returns a message for the minute after `time`, i.e. the message represents the
	/// instant at the **end** of the transmission.
	///
	/// All fields of the returned message are used:
	/// - [`Message::packed`]: the amplitude modulated message, LSB first.
	/// - [`Message::packed_alt`]: the phase modulated message, LSB first.
	/// - [`Message::delay`]: the current time within the minute, in nanoseconds.
	/// - [`Message::leap`]: true if a leap second should be inserted at the end of this message.
	///
	/// This function adjusts `time` to the next timestamp for which a message should be generated,
	/// which is exactly the beginning of the next minute.
	///
	/// # Errors
	///
	/// Returns [`Error::UnsupportedTime`] if the minute **after** `time` is less than zero.
	///
	/// # Examples
	///
	/// ```
	/// let dcf77 = DCF77::new(None).unwrap();
	/// // Sun, May 26, 2024. 16:57:25 UTC.
	/// let mut time = TimeSpec {
	/// 	sec: 1716742645,
	/// 	nsec: 123456789
	/// };
	///
	/// let message = dcf77.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:58:00 UTC.
	/// assert_eq!(time.sec, 1716742680);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed, 0x090BE631B120000);
	/// assert_eq!(message.packed_alt, 0x090BE631B1203FF);
	/// assert_eq!(message.delay, 25123456789);
	/// assert_eq!(message.leap, false);
	///
	/// let message = dcf77.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:59:00 UTC.
	/// assert_eq!(time.sec, 1716742740);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed, 0x90BE630B320000);
	/// assert_eq!(message.packed_alt, 0x90BE630B3203FF);
	/// assert_eq!(message.delay, 0);
	/// assert_eq!(message.leap, false);
	/// ```
	pub fn get_message(&self, time: &mut TimeSpec) -> Result<Message, Error> {
		// Find the next minute (exactly)
		let time_in_min = time.sec % 60;
		let sec = time.sec - time_in_min + 60;

		// Compute the message
		let message = MessageUncompressed::new(sec, &self.berlin_tz)?;
		let (am, fm) = message.pack();

		// Calculate where we are within the minute (in nanoseconds)
		let ns = time_in_min * 1000000000 + time.nsec;

		// Calculate if this is a minute with leap second
		let leap = nextleapsecond(sec).filter(|(t, _)| *t == sec).is_some();

		// Increment the clock
		*time += Seconds(60 - time_in_min);
		time.nsec = 0;

		Ok(Message::new_with_alt(am, fm, ns, leap))
	}
}

/// State machine for transmitting messages.
#[derive(Clone, Copy)]
enum WriterState {
	/// Transmitting start of message indicator.
	Start,
	/// Transmitting a message bit. The payload indicates which bit (`u8`, 0-indexed starting with the
	/// LSB), the value of that bit for both amplitude and phase modulated messages (both `bool`).
	Bit(u8, bool, bool),
	/// Transmitting a leap second, always a zero bit.
	Leap,
	/// Transmitting a special minute marker. No amplitude modulation, but treated as a zero bit for
	/// phase modulation.
	Marker
}

impl WriterState {
	/// Advance the state machine to the next state.
	///
	/// The state machine advances as follows:
	/// - `Start` => `Bit(0, _, _)`
	/// - `Bit(n, _, _)` => `Bit(n + 1, _, _)`
	/// - `Bit(58, _, _)` => `Leap` if `message.leap` else `Marker`
	/// - `Leap` => `Marker`
	/// - `Marker` => `Start`
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance(&mut self, message: &mut Message) {
		*self = match *self {
			WriterState::Start => WriterState::Bit(0, message.packed & 1 > 0, message.packed_alt & 1 > 0),
			WriterState::Bit(bit, _, _) => {
				message.packed >>= 1;
				message.packed_alt >>= 1;
				if bit < 58 {
					WriterState::Bit(bit + 1, message.packed & 1 > 0, message.packed_alt & 1 > 0)
				} else if message.leap {
					WriterState::Leap
				} else {
					WriterState::Marker
				}
			},
			WriterState::Leap => WriterState::Marker,
			WriterState::Marker => WriterState::Start
		}
	}

	/// Advance the state machine to a given bit.
	///
	/// If `bit > 58`, automatically advances to `Leap` or `Marker` states as appropriate.
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance_to(&mut self, message: &mut Message, bit: u8) {
		*self = if bit < 59 {
			message.packed >>= bit;
			message.packed_alt >>= bit;
			WriterState::Bit(bit, message.packed & 1 > 0, message.packed_alt & 1 > 0)
		} else if message.leap {
			WriterState::Leap
		} else {
			WriterState::Marker
		}
	}
}

/// Make a writer to transmit DCF77 messages sampled at 48 kHz.
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
/// increments are 1/48,000 of a second or 20.833 microseconds. This also means that values
/// returned from [`DCF77::get_message`] in `Message::delay` must be converted from nanoseconds
/// to samples, e.g. with `(message.delay * 48) / 1000000`.
///
/// *Note: this writer actually writes messages with a 15.5 kHz carrier, so the true 77.5 kHz
/// carrier signal is the fifth harmonic of the output. This is because a 77.5 kHz signal cannot be
/// adequately sampled at 48 kHz.*
///
/// # Examples
///
/// ```
/// // Construct a DCF77 object to generate messages
/// let d = DCF77::new(None).expect("Error reading Berlin timezone");
///
/// // Get a message for the current time
/// let mut m = d.get_message(&mut crate::time::currenttime().unwrap()).expect("Time must be >=0");
/// // Convert from absolute time to sample time
/// m.delay = (m.delay * 48) / 1000000;
/// // Make a writer that converts the message into wire format at 48 kHz
/// let mut writer = make_writer();
/// // Create a buffer to write 21.33ms of signal at a time
/// let mut buf = Vec::<f32>::with_capacity(1024);
/// unsafe {
/// 	buf.set_len(1024);
/// }
/// let buf = buf.as_mut_slice();
///
/// loop {
/// 	// Write the message to the buffer
/// 	let (_i, done) = writer(&mut m, buf);
/// 	// Use the results in buf
/// 	if done { break; }
/// };
/// ```
pub fn make_writer() -> impl FnMut(&mut Message, &mut [f32]) -> (usize, bool) {
	let mut i: usize = 0;
	let mut bitstart: usize = 0;
	let mut state = WriterState::Start;
	move |message: &mut Message, data: &mut [f32]| -> (usize, bool) {
		// Move to the right bit position if we're starting mid-message
		if message.delay > 0 {
			let m = message.delay as usize;
			let bit = m / 48000; // 1 bit per second
			bitstart = i + (bit * 48000);
			i += m;
			message.delay = 0;
			state.advance_to(message, bit as u8);
		} else if let WriterState::Start = state {
			state.advance(message);
		}

		// Sample time when phase the modulated signal starts, phase modulated signal ends, and the
		// message ends.
		let timings = |x| (x + 9600, x + 47653, x + 48000); // (200ms, ~993ms, 1000ms)

		let start = i;
		let (mut phase_start, mut phase_end, mut bitend) = timings(bitstart);
		let mut message_completed = false;
		for sample in data.iter_mut() {
			let (timing_on, phase) = match state {
				WriterState::Bit(_, true, pm) => (9600, pm), // 200ms
				WriterState::Bit(_, false, pm) => (4800, pm), // 100ms
				WriterState::Leap  => (4800, false), // 100ms
				_ => (0, false),
			};

			// Calculate amplitude modulation
			let power = if i < bitstart + timing_on {
				0.15
			} else {
				1.0
			};

			// Calculate phase modulation
			let phase_i = if i >= phase_start && i <= phase_end {
				// Each chip spans 120 cycles of the 77.5 kHz carrier
				let chip_i = (i - phase_start) * 77500 / (120 * 48000);
				let chip = PM_CHIP_SEQUENCE.get(chip_i).copied().unwrap_or(0) > 0;
				PI / 180. * if phase ^ chip {
					-15.6
				} else {
					15.6
				}
			} else {
				0.
			};

			let pos = (i % 48000) as f32 / 48000.;
			*sample = power * f32::sin(PI * 2. * 77500. / 5. * pos + phase_i);
			i += 1;

			if i >= bitend {
				bitstart = i;
				(phase_start, phase_end, bitend) = timings(bitstart);
				state.advance(message);
				if let WriterState::Start = state {
					message_completed = true;
					break;
				}
			}
		}

		(i - start, message_completed)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn get_timezone() -> Timezone {
		crate::tz::parse_file("/usr/share/zoneinfo/Europe/Berlin").unwrap()
	}

	#[test]
	fn message_test() {
		let timezone = get_timezone();
		let m = MessageUncompressed::new(1716742705, &timezone).unwrap();
		assert_eq!(m.timezone, 2);
		assert_eq!(m.min_ones, 8);
		assert_eq!(m.min_tens, 5);
		assert_eq!(m.hour_ones, 8);
		assert_eq!(m.hour_tens, 1);
		assert_eq!(m.day_ones, 6);
		assert_eq!(m.day_tens, 2);
		assert_eq!(m.dow, 7);
		assert_eq!(m.month_ones, 5);
		assert_eq!(m.month_tens, 0);
		assert_eq!(m.year_ones, 4);
		assert_eq!(m.year_tens, 2);

		let (am, pm) = m.pack();
		assert_eq!(am, 0x090BE631B120000);
		assert_eq!(pm, 0x090BE631B1203FF);

		let m = MessageUncompressed::new(1711845583, &timezone).unwrap();
		assert_eq!(m.timezone, 5);
		assert_eq!(m.min_ones, 9);
		assert_eq!(m.min_tens, 3);
		assert_eq!(m.hour_ones, 1);
		assert_eq!(m.hour_tens, 0);
		assert_eq!(m.day_ones, 1);
		assert_eq!(m.day_tens, 3);
		assert_eq!(m.dow, 7);
		assert_eq!(m.month_ones, 3);
		assert_eq!(m.month_tens, 0);
		assert_eq!(m.year_ones, 4);
		assert_eq!(m.year_tens, 2);

		let (am, pm) = m.pack();
		assert_eq!(am, 0x907F1827350000);
		assert_eq!(pm, 0x907F18273503FF);

		let m = MessageUncompressed::new(741483270, &timezone).unwrap();
		assert_eq!(m.timezone, 10);
		assert_eq!(m.min_ones, 4);
		assert_eq!(m.min_tens, 3);
		assert_eq!(m.hour_ones, 1);
		assert_eq!(m.hour_tens, 0);
		assert_eq!(m.day_ones, 1);
		assert_eq!(m.day_tens, 0);
		assert_eq!(m.dow, 4);
		assert_eq!(m.month_ones, 7);
		assert_eq!(m.month_tens, 0);
		assert_eq!(m.year_ones, 3);
		assert_eq!(m.year_tens, 9);

		let (am, pm) = m.pack();
		assert_eq!(am, 0x64CF018369A0000);
		assert_eq!(pm, 0x64CF018369A03FF);
	}

	#[test]
	fn timing_test() {
		let dcf77 = DCF77::new(None).unwrap();
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let message = dcf77.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742680);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed, 0x090BE631B120000);
		assert_eq!(message.packed_alt, 0x090BE631B1203FF);
		assert_eq!(message.delay, 25123456789);
		assert_eq!(message.leap, false);

		let message = dcf77.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742740);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed, 0x90BE630B320000);
		assert_eq!(message.packed_alt, 0x90BE630B3203FF);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);

		time.sec = 741484740;
		let message = dcf77.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484800);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed, 0x64CF018401A0000);
		assert_eq!(message.packed_alt, 0x64CF018401A03FF);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, true);

		let message = dcf77.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484860);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed, 0x64CF01850320000);
		assert_eq!(message.packed_alt, 0x64CF018503203FF);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);
	}

	fn get_message(j: &DCF77, time: &mut TimeSpec) -> Message {
		let mut message = j.get_message(time).unwrap();
		message.delay = (message.delay * 48) / 1000000;
		message
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
		assert!((p - 0.095).abs() < 0.01, "Low signal expected power of 0.095, saw {}", p)
	}

	fn check_is_zero(buffer: &[f32], bound: usize) {
		check_is_low(&buffer[bound..bound + 4800]);
		check_is_high(&buffer[bound + 4800..bound + 48000]);
	}

	fn check_is_one(buffer: &[f32], bound: usize) {
		check_is_low(&buffer[bound..bound + 9600]);
		check_is_high(&buffer[bound + 9600..bound + 48000]);
	}

	fn check_no_phase(buffer: &[f32], offset: usize) {
		for (i, &v) in buffer.iter().enumerate() {
			// Skip values near extremes as they don't solve well
			if v > 0.9 || v < -0.9 {
				continue;
			}
			let p = 77500. / 5. / 48000. * ((offset + i) % 48000) as f32;
			let mut x = 0.;
			// Solve 3 iterations of Newton's method to find the phase offset
			for _ in 0..3 {
				let f = 0.15 * f32::sin(PI * 2. * (p + x)) - v;
				let df = 0.15 * PI * 2. * f32::cos(PI * 2. * (p + x));
				x -= f / df;
			}

			assert!(x > -0.005 && x < 0.005, "Failed -0.005 < {} < 0.005 for value {}", x, v);
		}
	}

	fn check_is_phase(buffer: &[f32], offset: usize, bitval: bool) {
		for (i, &v) in buffer.iter().enumerate() {
			// Skip values near extremes as they don't solve well
			if v > 0.9 || v < -0.9 {
				continue;
			}
			let p = 77500. / 5. / 48000. * ((offset + i) % 48000) as f32;
			let mut x = 0.;
			// Solve 3 iterations of Newton's method to find the phase offset
			for _ in 0..3 {
				let f = f32::sin(PI * 2. * (p + x)) - v;
				let df = PI * 2. * f32::cos(PI * 2. * (p + x));
				x -= f / df;
			}

			if bitval {
				assert!(x > -0.048 && x < -0.038, "Failed -0.048 < {} < -0.038 for value {}", x, v);
			} else {
				assert!(x > 0.038 && x < 0.048, "Failed 0.038 < {} < 0.048 for value {}", x, v);
			}
		}
	}

	#[test]
	fn transmit_test() {
		let mut writer = make_writer();
		let dcf77 = DCF77::new(None).unwrap();
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let mut buf = Vec::<f32>::with_capacity(2900000);
		unsafe {
			buf.set_len(2900000);
		}
		let buf = buf.as_mut_slice();

		let mut message = get_message(&dcf77, &mut time);
		let offset = message.delay as usize;
		assert_eq!(writer(&mut message, buf).0, 1674075);
		check_is_low(&buf[0..3674]);
		check_is_high(&buf[3674..42075]);
		let mut bound = 42075;
		let mut packed = 0x090BE631B120000_u64 >> 26;
		for _ in 26..59 {
			let bit = (packed & 1) > 0;
			if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};
			bound += 48000;

			packed >>= 1;
		}
		check_is_high(&buf[bound..bound+48000]);

		check_no_phase(&buf[0..10], offset);
		check_no_phase(&buf[3650..3660], offset + 3650);
		let bound_start = 3680;
		for i in 0..512 {
			let chip = PM_CHIP_SEQUENCE.get(i).copied().unwrap_or(0) > 0;
			bound = bound_start + i * 120 * 48000 / 77500;
			check_is_phase(&buf[bound..bound+10], offset + bound, !chip);
		}
		packed = 0x090BE631B1203FF_u64 >> 26;
		bound = 42080;
		for i in 26..60 {
			let bit = (packed & 1) > 0;
			if i < 59 {
				check_no_phase(&buf[bound..bound+10], offset + bound);
			}
			for i in 0..512 {
				let chip = PM_CHIP_SEQUENCE.get(i).copied().unwrap_or(0) > 0;
				let b = bound + 9600 + i * 120 * 48000 / 77500;
				check_is_phase(&buf[b..b+10], offset + b, bit ^ chip);
			}
			bound += 48000;

			packed >>= 1;
		}

		message = dcf77.get_message(&mut time).unwrap();
		assert_eq!(writer(&mut message, buf).0, 2880000);
		let mut bound = 0;
		let mut packed = 0x90BE630B320000_u64;
		for _ in 0..59 {
			let bit = (packed & 1) > 0;
			if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};
			bound += 48000;

			packed >>= 1;
		}
		check_is_high(&buf[bound..bound+48000]);

		packed = 0x90BE630B3203FF_u64;
		bound = 5;
		for i in 0..60 {
			let bit = (packed & 1) > 0;
			if i < 59 {
				check_no_phase(&buf[bound..bound+10], bound);
			}
			for i in 0..512 {
				let chip = PM_CHIP_SEQUENCE.get(i).copied().unwrap_or(0) > 0;
				let b = bound + 9600 + i * 120 * 48000 / 77500;
				check_is_phase(&buf[b..b+10], b, bit ^ chip);
			}
			bound += 48000;

			packed >>= 1;
		}
	}

	#[test]
	fn module_doctest() {
		// Construct a DCF77 object to generate messages
		let d = DCF77::new(None).unwrap();

		// Get a message for the current time
		let m = d.get_message(&mut crate::time::currenttime().unwrap());
		match m {
			Ok(mut m) => {
				// Convert real time (nanoseconds) to sample time (48 kHz)
				m.delay = (m.delay * 48) / 1000000;
				// Make a writer that converts the message into wire format at 48 kHz
				let mut writer = make_writer();
				// Create a buffer with enough space to hold 15s of the encoded message
				let mut buf = Vec::<f32>::with_capacity(800000);
				unsafe {
					buf.set_len(800000);
				}
				let buf = buf.as_mut_slice();

				// Write the 60s message in four 15s chunks
				for _ in 0..4 {
					// Write the message to the buffer
					writer(&mut m, buf);

					// Use the results in buf
				}
			},
			Err(e) => {
				// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
				eprintln!("{}", e);
			}
		}


		// Documentation for PM_CHIP_SEQUENCE
		let bit = 1;
		for chip in PM_CHIP_SEQUENCE {
			let _phase = PI / 180. * if bit ^ chip == 1 {
							-15.6
						} else {
							15.6
						};

			// Use _phase to modulate carrier
		}


		// Documentation for DCF77::new
		let d = DCF77::new(None);
		match d {
			Ok(_d) => {
				// Create & use messages
			},
			Err(_) => {
				// Known valid offset (UTC+1 / UTC+2) that cannot fail
				let _d = DCF77::new(
					crate::tz::parse_tzstring(b"CET-1CEST,M3.5.0,M10.5.0/3").ok()
				).unwrap();
				// Create & use messages
			}
		}


		// Documentation for make_writer
		// Construct a DCF77 object to generate messages
		let d = DCF77::new(None).expect("Error reading Berlin timezone");

		// Get a message for the current time
		let mut m = d.get_message(&mut crate::time::currenttime().unwrap()).expect("Time must be >=0");
		// Convert from absolute time to sample time
		m.delay = (m.delay * 48) / 1000000;
		// Make a writer that converts the message into wire format at 48 kHz
		let mut writer = make_writer();
		// Create a buffer to write 21.33ms of signal at a time
		let mut buf = Vec::<f32>::with_capacity(1024);
		unsafe {
			buf.set_len(1024);
		}
		let buf = buf.as_mut_slice();

		loop {
			// Write the message to the buffer
			let (_i, done) = writer(&mut m, buf);

			// Use the results in buf

			if done { break; }
		};
	}
}
