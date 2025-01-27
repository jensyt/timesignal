//! Support for setting Junghans Mega watches.
//!
//! This module provides the necessary functions to encode the time in Junghans's proprietary
//! format and generate the signal to set a compatible watch.
//!
//! # Examples
//!
//! ```
//! # use signals::junghans::{Junghans, make_writer};
//! # use signals::MessageGenerator;
//! // Construct a Junghans object to generate messages
//!	let j = Junghans::new(
//!				// Timezone is used to configure the watch's local time
//!				time::tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
//!			).expect("Invalid timezone offset");
//!
//!	// Get a message for the current time
//!	let m = j.get_message(&mut time::now().unwrap());
//!	match m {
//!		Ok(m) => {
//!			// Make a writer that converts the message into wire format at 48 kHz
//!			let mut writer = make_writer::<48000>();
//! 		// Convert real time (nanoseconds) to sample time (48 kHz)
//!			let mut s = m.sample();
//!			// Create a buffer with enough space to hold the entire 15s encoded message
//!			let mut buf = Vec::<f32>::with_capacity(800000);
//!			unsafe {
//!				buf.set_len(800000);
//!			}
//!			let buf = buf.as_mut_slice();
//!			// Write the message to the buffer
//!			writer(&mut s, buf);
//!
//!			// Use the results in buf
//!		},
//!		Err(e) => {
//!			// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
//!			eprintln!("{}", e);
//!		}
//!	}
//! ```
//!
//! # Message Format
//!
//! Like other time signals, the time is represented in binary-coded decimal. It represents UTC,
//! and like [WWVB] it is transmitted most significant bit first. Unlike public time signals, the
//! Junghans format does not encode a minute; rather, it encodes a specific second. The second
//! being transmitted is for the moment after the last bit is finished transmitting, conceptually
//! similar to how [DCF77] transmits the following minute. Since the Junghans signal uses variable
//! width encoding (more details below), the second encoded is typically 15 seconds +/- a few
//! hundred milliseconds after the start of the transmission, e.g. for a transmission starting at
//! 14:25:30 and ending at 14:25:45, the encoded time transmitted is 14:25:45.
//!
//! | Bit | Weight | Meaning                      | Bit | Weight | Meaning                                     |
//! | --: | :----: | ---------------------------- | --: | :----: | ------------------------------------------- |
//! | 0   | 8      | UTC second, 1's digit        | 30  | 8      | UTC year, 1's digit                         |
//! | 1   | 4      | UTC second, 1's digit        | 31  | 4      | UTC year, 1's digit                         |
//! | 2   | 2      | UTC second, 1's digit        | 32  | 2      | UTC year, 1's digit                         |
//! | 3   | 1      | UTC second, 1's digit        | 33  | 1      | UTC year, 1's digit                         |
//! | 4   | 4      | UTC second, 10's digit       | 34  | 8      | UTC year, 10's digit                        |
//! | 5   | 2      | UTC second, 10's digit       | 35  | 4      | UTC year, 10's digit                        |
//! | 6   | 1      | UTC second, 10's digit       | 36  | 2      | UTC year, 10's digit                        |
//! | 7   | 8      | UTC minute, 1's digit        | 37  | 1      | UTC year, 10's digit                        |
//! | 8   | 4      | UTC minute, 1's digit        | 38  | 8      | Timezone offset configuration, lower 4 bits |
//! | 9   | 2      | UTC minute, 1's digit        | 39  | 4      | Timezone offset configuration, lower 4 bits |
//! | 10  | 1      | UTC minute, 1's digit        | 40  | 2      | Timezone offset configuration, lower 4 bits |
//! | 11  | 4      | UTC minute, 10's digit       | 41  | 1      | Timezone offset configuration, lower 4 bits |
//! | 12  | 2      | UTC minute, 10's digit       | 42  | Leap   | UTC leap year (0 = no, 1 = yes)             |
//! | 13  | 1      | UTC minute, 10's digit       | 43  | +/-    | Timezone offset sign (0 = +, 1 = -)         |
//! | 14  | 8      | UTC hour, 1's digit          | 44  | 32     | Timezone offset configuration, upper 2 bits |
//! | 15  | 4      | UTC hour, 1's digit          | 45  | 16     | Timezone offset configuration, upper 2 bits |
//! | 16  | 2      | UTC hour, 1's digit          | 46  | Test   | Used for testing, set to 0 for normal use   |
//! | 17  | 1      | UTC hour, 1's digit          | 47  | Test   | Used for testing, set to 0 for normal use   |
//! | 18  | 2      | UTC hour, 10's digit         | 48  | STD    | Local time is STD or DST (0 = DST, 1 = STD) |
//! | 19  | 1      | UTC hour, 10's digit         | 49  | Test   | Used for testing, set to 0 for normal use   |
//! | 20  | 8      | UTC day of year, 1's digit   | 50  | 8      | CRC checksum, lower 4 bits                  |
//! | 21  | 4      | UTC day of year, 1's digit   | 51  | 4      | CRC checksum, lower 4 bits                  |
//! | 22  | 2      | UTC day of year, 1's digit   | 52  | 2      | CRC checksum, lower 4 bits                  |
//! | 23  | 1      | UTC day of year, 1's digit   | 53  | 1      | CRC checksum, lower 4 bits                  |
//! | 24  | 8      | UTC day of year, 10's digit  | 54  | 128    | CRC checksum, upper 4 bits                  |
//! | 25  | 4      | UTC day of year, 10's digit  | 55  | 64     | CRC checksum, upper 4 bits                  |
//! | 26  | 2      | UTC day of year, 10's digit  | 56  | 32     | CRC checksum, upper 4 bits                  |
//! | 27  | 1      | UTC day of year, 10's digit  | 57  | 16     | CRC checksum, upper 4 bits                  |
//! | 28  | 2      | UTC day of year, 100's digit | 58  | 1      | End of message, always set to 1             |
//! | 29  | 1      | UTC day of year, 100's digit |
//!
//! For timezone offset configuration details, see [`TIMEZONE_OFFSET`]. For checksum details, see
//! [`CHECKSUM_TABLE`].
//!
//! It does not appear that Junghans's proprietary format handles leap seconds.
//!
//! [WWVB]: https://en.wikipedia.org/wiki/WWVB
//! [DCF77]: https://en.wikipedia.org/wiki/DCF77
//!
//! # Signal Details
//!
//! Messages are transmitted on a 40kHz carrier using amplitude modulation with variable-length
//! bits. Binary 1 bits are transmitted for 300 ms, and binary 0 bits are transmitted for 200 ms.
//! Each bit begins with the carrier amplitude at full power for 30% of the full transmission time
//! (90 ms for 1 bits, 60 ms for 0 bits), followed by a reduction to 10% of full power for the
//! remaining 70% of the full transmission time (210 ms for 1 bits, 140 ms for 0 bits).
//!
//! Given the variable-length representation, the Junghans proprietary format also includes special
//! timing adjustment features to ensure that messages end exactly on the second mark. There are
//! two forms of timing adjustment:
//! 1. Start of message indicator. Before the bits of a message are transmitted, a start of message
//!    indicator is transmitted. This indicator uses the same rules as other bits (full power for
//!    30%, low power for 70%), but its duration depends on whether it is the first message in a
//!    sequence. For the first message, the time is at least 400 ms but padded with however much
//!    time is necessary to end the message exactly on the encoded second. For subsequenct
//!    messages, it is exactly 400 ms.
//! 2. End of message padding bits. After the bits of a message are transmitted, a sequence of
//!    padding bits consisting of zero or more 0 bits and exactly one 1 bit are transmitted, using
//!    the same modulation and timing rules as for normal bits. The number of 0 bits is chosen to
//!    ensure that the **following** message ends exactly on its encoded second.
//!
//! This timing scheme is possible because the message checksum ensures that the number of 1 bits
//! in a message is always odd, which guarantees that the remaining padding time needed is evenly
//! divisible by 200 ms after adding the final 300 ms 1 bit.

use core::f32::consts::PI;
use crate::{Message, MessageError, MessageGenerator, SampledMessage};
#[cfg(debug_assertions)]
use core::fmt;
use time::{Nanoseconds, TimeSpec, Tm, tz::{self, Timezone}};
use crate::sin32;

/// Table of valid timezone offsets.
///
/// Each entry is a 15-minute offset from UTC, starting at UTC-12 and extending to UTC+14. Values
/// in this table correspond to configuration values for Mega watches. A value of `0xff` represents
/// an invalid configuration. Interpreting the value returned requires a separate sign
/// configuration, e.g. value `0x06` can mean either `UTC-5` or `UTC+4.30`.
///
/// Valid configuration values are in the table below. All other offsets will return `0xff`.
///
/// | Offset (hrs.min) | Value |
/// | ---------------- | ----- |
/// | - 12             | 0x14  |
/// | - 11             | 0x13  |
/// | - 10             | 0x12  |
/// | - 09.30          | 0x11  |
/// | - 09             | 0x10  |
/// | - 08             | 0x09  |
/// | - 07             | 0x08  |
/// | - 06             | 0x07  |
/// | - 05             | 0x06  |
/// | - 04             | 0x05  |
/// | - 03.30          | 0x04  |
/// | - 03             | 0x03  |
/// | - 02             | 0x02  |
/// | - 01             | 0x01  |
/// | +/- 00           | 0x00  |
/// | + 01             | 0x01  |
/// | + 02             | 0x02  |
/// | + 03             | 0x03  |
/// | + 03.30          | 0x04  |
/// | + 04             | 0x05  |
/// | + 04.30          | 0x06  |
/// | + 05             | 0x07  |
/// | + 05.30          | 0x08  |
/// | + 05.45          | 0x09  |
/// | + 06             | 0x10  |
/// | + 06.30          | 0x11  |
/// | + 07             | 0x12  |
/// | + 08             | 0x13  |
/// | + 08.30          | 0x14  |
/// | + 08.45          | 0x15  |
/// | + 09             | 0x16  |
/// | + 09.30          | 0x17  |
/// | + 10             | 0x18  |
/// | + 10.30          | 0x19  |
/// | + 11             | 0x20  |
/// | + 11.30          | 0x21  |
/// | + 12             | 0x22  |
/// | + 12.45          | 0x23  |
/// | + 13             | 0x24  |
/// | + 13.45          | 0x25  |
/// | + 14             | 0x26  |
///
/// For more details on the supported timezones, see the [manual].
///
/// [manual]: https://www.junghans.de/media/manuals/en/max_bill_MEGA_Solar.pdf
///
/// # Examples
///
/// ```ignore
/// // UTC-9
/// let mut offset = -9;
/// // Offset such that UTC-12 is zero
/// offset += 12;
/// // Convert to 15 minute chunks
/// offset *= 4;
/// // Get configuration value corresponding to UTC-9
/// assert_eq!(TIMEZONE_OFFSET[offset as usize], 0x10);
/// ```
const TIMEZONE_OFFSET: [u8; 105] = [0x14, 0xff, 0xff, 0xff, 0x13, 0xff, 0xff, 0xff,
									0x12, 0xff, 0x11, 0xff, 0x10, 0xff, 0xff, 0xff,
									0x09, 0xff, 0xff, 0xff, 0x08, 0xff, 0xff, 0xff,
									0x07, 0xff, 0xff, 0xff, 0x06, 0xff, 0xff, 0xff,
									0x05, 0xff, 0x04, 0xff, 0x03, 0xff, 0xff, 0xff,
									0x02, 0xff, 0xff, 0xff, 0x01, 0xff, 0xff, 0xff,
									0x00, 0xff, 0xff, 0xff, 0x01, 0xff, 0xff, 0xff,
									0x02, 0xff, 0xff, 0xff, 0x03, 0xff, 0x04, 0xff,
									0x05, 0xff, 0x06, 0xff, 0x07, 0xff, 0x08, 0x09,
									0x10, 0xff, 0x11, 0xff, 0x12, 0xff, 0xff, 0xff,
									0x13, 0xff, 0x14, 0x15, 0x16, 0xff, 0x17, 0xff,
									0x18, 0xff, 0x19, 0xff, 0x20, 0xff, 0x21, 0xff,
									0x22, 0xff, 0xff, 0x23, 0x24, 0xff, 0xff, 0x25,
									0x26];

/// Precomputed [CRC-8-Maxim] table.
///
/// This table is used to calculate CRC checksums of the message being transmitted. It has
/// precomputed coefficients using the following assumptions:
/// - CRC polynomial: 0x31
/// - Input reflected
/// - Output reflected
///
/// Multi-byte messages can be checksummed by XOR-ing the coefficient of the previous byte with the
/// value of the next byte, and then using the result as the index for lookup. See the example
/// below.
///
/// See this [table generator] for more details.
///
/// [CRC-8-Maxim]: https://reveng.sourceforge.io/crc-catalogue/all.htm#crc.cat.crc-8-maxim-dow
/// [table generator]: https://www.sunshine2k.de/coding/javascript/crc/crc_js.html
///
/// # Examples
///
/// ```ignore
/// let message = b"test";
/// let checksum = message.iter()
/// 	.copied()
/// 	.reduce(|a, b| CHECKSUM_TABLE[a as usize] ^ b)
/// 	.map(|v| CHECKSUM_TABLE[v as usize]);
/// assert_eq!(checksum, Some(0x4c));
/// ```
const CHECKSUM_TABLE: [u8; 256] = [0x00, 0x5e, 0xbc, 0xe2, 0x61, 0x3f, 0xdd, 0x83,
								   0xc2, 0x9c, 0x7e, 0x20, 0xa3, 0xfd, 0x1f, 0x41,
								   0x9d, 0xc3, 0x21, 0x7f, 0xfc, 0xa2, 0x40, 0x1e,
								   0x5f, 0x01, 0xe3, 0xbd, 0x3e, 0x60, 0x82, 0xdc,
								   0x23, 0x7d, 0x9f, 0xc1, 0x42, 0x1c, 0xfe, 0xa0,
								   0xe1, 0xbf, 0x5d, 0x03, 0x80, 0xde, 0x3c, 0x62,
								   0xbe, 0xe0, 0x02, 0x5c, 0xdf, 0x81, 0x63, 0x3d,
								   0x7c, 0x22, 0xc0, 0x9e, 0x1d, 0x43, 0xa1, 0xff,
								   0x46, 0x18, 0xfa, 0xa4, 0x27, 0x79, 0x9b, 0xc5,
								   0x84, 0xda, 0x38, 0x66, 0xe5, 0xbb, 0x59, 0x07,
								   0xdb, 0x85, 0x67, 0x39, 0xba, 0xe4, 0x06, 0x58,
								   0x19, 0x47, 0xa5, 0xfb, 0x78, 0x26, 0xc4, 0x9a,
								   0x65, 0x3b, 0xd9, 0x87, 0x04, 0x5a, 0xb8, 0xe6,
								   0xa7, 0xf9, 0x1b, 0x45, 0xc6, 0x98, 0x7a, 0x24,
								   0xf8, 0xa6, 0x44, 0x1a, 0x99, 0xc7, 0x25, 0x7b,
								   0x3a, 0x64, 0x86, 0xd8, 0x5b, 0x05, 0xe7, 0xb9,
								   0x8c, 0xd2, 0x30, 0x6e, 0xed, 0xb3, 0x51, 0x0f,
								   0x4e, 0x10, 0xf2, 0xac, 0x2f, 0x71, 0x93, 0xcd,
								   0x11, 0x4f, 0xad, 0xf3, 0x70, 0x2e, 0xcc, 0x92,
								   0xd3, 0x8d, 0x6f, 0x31, 0xb2, 0xec, 0x0e, 0x50,
								   0xaf, 0xf1, 0x13, 0x4d, 0xce, 0x90, 0x72, 0x2c,
								   0x6d, 0x33, 0xd1, 0x8f, 0x0c, 0x52, 0xb0, 0xee,
								   0x32, 0x6c, 0x8e, 0xd0, 0x53, 0x0d, 0xef, 0xb1,
								   0xf0, 0xae, 0x4c, 0x12, 0x91, 0xcf, 0x2d, 0x73,
								   0xca, 0x94, 0x76, 0x28, 0xab, 0xf5, 0x17, 0x49,
								   0x08, 0x56, 0xb4, 0xea, 0x69, 0x37, 0xd5, 0x8b,
								   0x57, 0x09, 0xeb, 0xb5, 0x36, 0x68, 0x8a, 0xd4,
								   0x95, 0xcb, 0x29, 0x77, 0xf4, 0xaa, 0x48, 0x16,
								   0xe9, 0xb7, 0x55, 0x0b, 0x88, 0xd6, 0x34, 0x6a,
								   0x2b, 0x75, 0x97, 0xc9, 0x4a, 0x14, 0xf6, 0xa8,
								   0x74, 0x2a, 0xc8, 0x96, 0x15, 0x4b, 0xa9, 0xf7,
								   0xb6, 0xe8, 0x0a, 0x54, 0xd7, 0x89, 0x6b, 0x35];

/// Construct an 8-bit byte from two 4-bit nibbles.
///
/// This is a helper function for calculating checksums, since the Junghans message format requires
/// repeatedly combining 4-bit values to perform CRC calculations. This function takes the lower
/// four bits from `lower` and `upper` and combines them, with `lower` taking the LSB 4 bits and
/// `upper` taking the MSB 4 bits of the returned value.
///
/// # Examples
///
/// ```ignore
/// assert_eq!(make_checksum_index(0x12, 0xab), 0xb2);
/// ```
#[inline(always)]
fn make_checksum_index(lower: u8, upper: u8) -> u8 {
	(lower & 0xf) | (upper << 4)
}

/// An unpacked / uncompressed Junghans message.
///
/// This type contains all of the components of the encoded Junghans message, but in an unpacked
/// format that is easier to inspect. See [`MessageUncompressed::pack`] for details on getting and
/// using the packed message, which can be transmitted to a watch.
///
/// # Examples
///
/// ```ignore
/// // US Pacific timezone, UTC-8 (standard time) / UTC-7 (daylight savings time)
/// let timezone = time::tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok();
///
/// // Sunday, May 26, 2024. 09:58:25 UTC-7 / 16:58:25 UTC.
/// let m = MessageUncompressed::new(1716742705, &timezone).unwrap();
/// assert_eq!(m.utc_sec_ones, 5);  // Second 25
/// assert_eq!(m.utc_sec_tens, 2);
/// assert_eq!(m.utc_min_ones, 8);  // Minute 58
/// assert_eq!(m.utc_min_tens, 5);
/// assert_eq!(m.utc_hour_ones, 6); // Hour 16
/// assert_eq!(m.utc_hour_tens, 1);
/// assert_eq!(m.utc_yday_ones, 7); // Day 147
/// assert_eq!(m.utc_yday_tens, 4);
/// assert_eq!(m.utc_yday_huns, 1);
/// assert_eq!(m.utc_year_ones, 4); // Year [20]24
/// assert_eq!(m.utc_year_tens, 2);
/// assert_eq!(m.leap, 1);          // Leap year
/// assert_eq!(m.dst, 1);           // DST
/// assert_eq!(m.offset, 8);
/// assert_eq!(m.offset2, 12);
/// assert_eq!(m.dstblock, 0);
/// assert_eq!(m.checksum, 0xA8);
///
/// let (p, d) = m.pack()
/// assert_eq!(p.reverse_bits(), 0x551597450A3022A0)
/// assert_eq!(d, 14500000000);
/// ```
struct MessageUncompressed {
	/// UTC seconds ones digit, ranged [0, 9].
	utc_sec_ones: u8,
	/// UT seconds tens digit, ranged [0, 5].
	utc_sec_tens: u8,
	/// UTC minutes ones digit, ranged [0, 9].
	utc_min_ones: u8,
	/// UTC minutes tens digit, ranged [0, 5].
	utc_min_tens: u8,
	/// UTC hour ones digit, ranged [0, 9].
	utc_hour_ones: u8,
	/// UTC hour tens digit, ranged [0, 2].
	utc_hour_tens: u8,
	/// UTC day of year ones digit, ranged [0, 9].
	utc_yday_ones: u8,
	/// UTC day of year tens digit, ranged [0, 9].
	utc_yday_tens: u8,
	/// UTC day of year hundreds digit, ranged [0, 3].
	utc_yday_huns: u8,
	/// UTC year ones digit, ranged [0, 9].
	utc_year_ones: u8,
	/// UTC year tens digit, ranged [0, 9].
	utc_year_tens: u8,
	/// UTC offset configuration. See [`TIMEZONE_OFFSET`] for more details.
	offset: u8,
	/// Additional configuration. This block contains the following information, from MSB to LSB:
	/// - Bits 4-7: Unused
	/// - Bit 3: 1 if it is a leap year
	/// - Bit 2: 1 if UTC offset is negative
	/// - Bits 0-1: The upper two bits of the UTC offset configuration. See [`TIMEZONE_OFFSET`] for
	///   more details.
	offset2: u8,
	/// Whether local time is standard time (`== 2`) or daylight savings time (`== 0`).
	dstblock: u8,
	/// The message checksum. See [`CHECKSUM_TABLE`] for more details.
	checksum: u8,
}

impl MessageUncompressed {
	/// Create a new Junghans message.
	///
	/// Input `time` should be greater than or equal to zero. `timezone` is used to set DST and UTC
	/// offset configurations for `time`.
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTime`] if `time < 0`. This function intentionally does not
	/// return [`MessageError::UnsupportedTimezoneOffset`], and instead defaults to UTC (zero offset)
	/// if the timezone's offset cannot be represented in the Junghans format.
	fn new(time: i64, timezone: &Timezone) -> Result<MessageUncompressed, MessageError> {
		let utc = Tm::new(time).ok_or(MessageError::UnsupportedTime(time))?;
		let local = timezone.info(time);

		let offset = (local.utoff / 900) + 48;
		let offset = TIMEZONE_OFFSET.get(offset as usize).copied().unwrap_or(0);

		let leap = utc.isleapyear();

		let mut s = MessageUncompressed {
			utc_sec_ones: utc.sec % 10,
			utc_sec_tens: utc.sec / 10,
			utc_min_ones: utc.min % 10,
			utc_min_tens: utc.min / 10,
			utc_hour_ones: utc.hour % 10,
			utc_hour_tens: utc.hour / 10,
			utc_yday_ones: (utc.yday % 10) as u8,
			utc_yday_tens: ((utc.yday / 10) % 10) as u8,
			utc_yday_huns: (utc.yday / 100) as u8,
			utc_year_ones: (utc.year % 10) as u8,
			utc_year_tens: ((utc.year / 10) % 10) as u8,
			offset,
			offset2: (offset >> 4 & 0xf)
				   | ((leap as u8) << 3 & 0x8)
				   | (((local.utoff < 0) as u8) << 2 & 0x4),
			dstblock: ((!local.isdst) as u8) << 1,
			checksum: 0,
		};

		// Calculate CRC-8 checksum
		s.checksum = CHECKSUM_TABLE[
						(CHECKSUM_TABLE[
							(CHECKSUM_TABLE[
								(CHECKSUM_TABLE[
									(CHECKSUM_TABLE[
										(CHECKSUM_TABLE[
											(CHECKSUM_TABLE[
												make_checksum_index(s.utc_sec_ones, s.utc_sec_tens) as usize
											] ^ make_checksum_index(s.utc_min_ones, s.utc_min_tens)) as usize
										] ^ make_checksum_index(s.utc_hour_ones, s.utc_hour_tens)) as usize
									] ^ make_checksum_index(s.utc_yday_ones, s.utc_yday_tens)) as usize
								] ^ make_checksum_index(s.utc_yday_huns, s.utc_year_ones)) as usize
							] ^ make_checksum_index(s.utc_year_tens, s.offset)) as usize
						] ^ make_checksum_index(s.offset2, s.dstblock)) as usize
					];

		Ok(s)
	}

	/// Pack the message into the bit format used to transmit.
	///
	/// Returns a tuple of two values:
	/// - The message itself, where the LSB is the first bit to transmit. The MSB 5 bits are unused
	///   and not to be transmitted.
	/// - The computed duration of the message without padding zero bits.
	fn pack(&self) -> (u64, i64) {
		// Fields in Junghans's format are transmitted MSB first, like WWVB. To avoid reversing the bits
		// on each field, we pack them in MSB first and then reverse the entire return value to meet the
		// function's documentation that the LSB is the first bit to transmit.
		let mut r: u64 = ((self.utc_sec_ones as u64) & 0xf) << 60;
		r |= ((self.utc_sec_tens as u64) & 0x7) << 57;
		r |= ((self.utc_min_ones as u64) & 0xf) << 53;
		r |= ((self.utc_min_tens as u64) & 0x7) << 50;
		r |= ((self.utc_hour_ones as u64) & 0xf) << 46;
		r |= ((self.utc_hour_tens as u64) & 0x3) << 44;
		r |= ((self.utc_yday_ones as u64) & 0xf) << 40;
		r |= ((self.utc_yday_tens as u64) & 0xf) << 36;
		r |= ((self.utc_yday_huns as u64) & 0x3) << 34;
		r |= ((self.utc_year_ones as u64) & 0xf) << 30;
		r |= ((self.utc_year_tens as u64) & 0xf) << 26;
		r |= ((self.offset as u64) & 0xf) << 22;
		r |= ((self.offset2 as u64) & 0xf) << 18;
		r |= ((self.dstblock as u64) & 0xf) << 14;
		r |= ((self.checksum as u64) & 0xf) << 10;
		r |= ((self.checksum as u64) & 0xf0) << 2;
		r |= 0x20;

		// Duration is message start (400ms) + 300ms for each 1 bit + 200ms for each 0 bit, excluding
		// the five unused bits.
		let ones = r.count_ones() as i64;
		let duration = 400000000 + (ones * 300000000) + ((59 - ones) * 200000000);

		(r.reverse_bits(), duration)
	}
}

#[cfg(debug_assertions)]
#[cfg_attr(docsrs, doc(cfg(debug_assertions)))]
impl fmt::Debug for MessageUncompressed {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f,
			"{}{}:{}{}:{}{} day_{}{}{} year_{}{} offset_{} dst_{} isleap_{} checksum_{:#02x}",
			self.utc_hour_tens,
			self.utc_hour_ones,
			self.utc_min_tens,
			self.utc_min_ones,
			self.utc_sec_tens,
			self.utc_sec_ones,
			self.utc_yday_huns,
			self.utc_yday_tens,
			self.utc_yday_ones,
			self.utc_year_tens,
			self.utc_year_ones,
			self.offset,
			self.dstblock == 0,
			self.offset & 0x8 > 0,
			self.checksum
		)
	}
}

/// Junghans message generator.
///
/// Messages returned from [`Junghans::get_message`] should be used with the writer returned by
/// [`make_writer`].
///
/// # Examples
///
/// ```
/// # use signals::junghans::Junghans;
/// # use signals::MessageGenerator;
/// // Construct a Junghans object to generate messages
///	let j = Junghans::new(
///				// Timezone is used to configure the watch's local time
///				time::tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
///			).expect("Invalid timezone offset");
///
///	// Get a message for the current time
///	let m = j.get_message(&mut time::now().unwrap());
///	match m {
///		Ok(_m) => {
///			// Use the message
///		},
///		Err(e) => {
///			// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
///			eprintln!("{}", e);
///		}
///	}
/// ```
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Junghans {
	/// The local timezone to configure.
	local_tz: Timezone,
}

/// Construct a new Junghans object.
///
/// This is a convenience function, see [`Junghans::new`] for details.
#[inline(always)]
pub fn new(local_tz: Option<Timezone>) -> Result<Junghans, MessageError> {
	Junghans::new(local_tz)
}

impl Junghans {
	/// Construct a new Junghans object.
	///
	/// This function checks if the supplied timezone can be properly represented in the Junghans
	/// format. See [`TIMEZONE_OFFSET`] for more details on valid configurations.
	///
	/// If the input `local_tz` is `None`, this function defaults to `UTC0` or reading
	/// `/etc/localtime` (feature `std`) for timezone information.
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTimezoneOffset`] if the timezone offset cannot be
	/// represented in Junghans's format, or [`MessageError::TimezoneError`] if there was an error
	/// reading `/etc/localtime`.
	///
	/// # Examples
	///
	/// ```
	/// # use signals::junghans::Junghans;
	/// let j = Junghans::new(
	/// 	time::tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
	/// );
	/// match j {
	/// 	Ok(_j) => {
	/// 		// Create & use messages
	/// 	},
	/// 	Err(_) => {
	/// 		// Known valid offset (UTC-8 / UTC-7) that cannot fail
	/// 		let _j = Junghans::new(
	/// 			time::tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").ok()
	/// 		).unwrap();
	/// 		// Create & use messages
	/// 	}
	/// }
	/// ```
	pub fn new(local_tz: Option<Timezone>) -> Result<Junghans, MessageError> {
		let local_tz = match local_tz {
			Some(t) => t,
			#[cfg(all(not(target_arch = "wasm32"), feature = "std"))]
			None => tz::parse_file("/etc/localtime")
						.map_err(|e| MessageError::TimezoneError(e))?,
			#[cfg(any(target_arch = "wasm32", not(feature = "std")))]
			None => tz::parse_tzstring(b"UTC0")
						.map_err(|e| MessageError::TimezoneError(e))?
		};

		for offset in local_tz.offsets() {
			let o = (offset / 900) + 48;
			if o < 0 || o > 104 || TIMEZONE_OFFSET[o as usize] == 0xff {
				return Err(MessageError::UnsupportedTimezoneOffset(offset));
			}
		}
		Ok(Junghans { local_tz })
	}
}

impl MessageGenerator for Junghans {
	/// Get a message for the given time.
	///
	/// Since the Junghans format encodes the time at the **end** of the message, this function
	/// actually returns a message for `time` + approximately 15 seconds. This is similar to how
	/// [DCF77] transmits a message for the *following* minute, and in contrast to [WWVB] which
	/// transmits a message for the *current* minute.
	///
	/// Only some fields of the returned message are used:
	/// - [`Message::packed`]: the message, LSB first.
	/// - [`Message::delay`]: the amount of padding time (in nanoseconds) to add after the message is
	///   transmitted.
	/// - [`Message::packed_alt`] and [`Message::leap`] are unused.
	///
	/// This function adjusts `time` to the next timestamp for which a message should be generated,
	/// which is approximately 15 seconds +/- several hundred milliseconds after `time`. The exact
	/// time depends on the message, since Junghans's format uses variable width encoding and padding
	/// bits.
	///
	/// [DCF77]: https://en.wikipedia.org/wiki/DCF77#Time_code_interpretation
	/// [WWVB]: https://en.wikipedia.org/wiki/WWVB#Amplitude-modulated_time_code
	///
	/// # Errors
	///
	/// Returns [`MessageError::UnsupportedTime`] if `time.sec + 15 < 0`.
	///
	/// # Examples
	///
	/// ```
	/// # use signals::junghans::Junghans;
	/// # use signals::MessageGenerator;
	/// # use time::TimeSpec;
	/// let j = Junghans::new(
	/// 	time::tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").ok()
	/// ).unwrap();
	/// // Sun, May 26, 2024. 16:58:10 UTC.
	/// let mut time = TimeSpec {
	/// 	sec: 1716742690,
	/// 	nsec: 123456789,
	/// };
	///
	/// let message = j.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:58:25 UTC.
	/// assert_eq!(message.packed.reverse_bits(), 0x551597450A3022A0);
	/// assert_eq!(message.delay, 376543211);
	/// assert_eq!(time.sec, 1716742705);
	/// assert_eq!(time.nsec, 0);
	///
	/// let message = j.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:58:40 UTC.
	/// assert_eq!(message.packed.reverse_bits(), 0x091597450A302520);
	/// assert_eq!(message.delay, 700000000);
	/// assert_eq!(time.sec, 1716742720);
	/// assert_eq!(time.nsec, 0);
	/// ```
	fn get_message(&self, time: &mut TimeSpec) -> Result<Message, MessageError> {
		let mut total_time: i64 = 15000000000;
		let mut sec = time.sec + 15;

		loop {
			let message = MessageUncompressed::new(sec, &self.local_tz)?;
			let (packed, duration) = message.pack();
			let remainder = total_time - duration - time.nsec;

			// Add seconds as needed to ensure there is enough buffer time to land exactly on the second
			// mark.
			if remainder < 200000000 {
				total_time += 1000000000;
				sec += 1;
			} else {
				*time += Nanoseconds(duration + remainder);
				break Ok(Message::new(packed, remainder));
			}
		}
	}
}

/// State machine for transmitting messages.
///
/// As with the writer returned by [`make_writer`], this state machine operates in sample space
/// rather than absolute time, meaning all time increments are 1/48,000 of a second or 20.833
/// microseconds.
#[derive(Clone, Copy, PartialEq)]
enum WriterState {
	/// Transmitting start of message indicator. The payload indicates whether the message is the
	/// first in the sequence (`true`) or not (`false`).
	Start(bool),
	/// Transmitting a message bit. The payload indicates which bit (`u8`, 0-indexed starting with the
	/// LSB) and the value of that bit (`bool`).
	Bit(u8, bool),
	/// Transmitting end of message padding bits.
	End,
}

impl WriterState {
	/// Advance the state machine to the next state.
	///
	/// The state machine advances as follows:
	/// - `Start(true)` => `Bit(0, _)`
	/// - `Bit(n, _)` => `Bit(n + 1, _)`
	/// - `Bit(58, _)` => `End`
	/// - `End` => `End`, until `message.delay` time has passed
	/// - `End` => `Start(false)`
	///
	/// The input `timing_total` is used to determine when `message.delay` time has passed, and should
	/// be the number of samples since the last time this function was called. It is only used in
	/// [`WriterState::End`] state.
	///
	/// The state machine also modifies `message` directly, consuming it as progress is made.
	fn advance(&mut self, message: &mut Message, timing_total: u64) {
		*self = match *self {
			WriterState::Start(_) => WriterState::Bit(0, message.packed & 1 > 0),
			WriterState::Bit(bit, _) => {
				message.packed >>= 1;
				if bit < 58 {
					WriterState::Bit(bit + 1, message.packed & 1 > 0)
				} else {
					WriterState::End
				}
			}
			WriterState::End => {
				message.delay -= timing_total as i64;
				if message.delay <= 0 {
					WriterState::Start(false)
				} else {
					WriterState::End
				}
			}
		}
	}
}

/// Make a writer to transmit Junghans messages sampled at `S` Hz.
///
/// Returns a closure with state initialized to begin transmitting a sequence of messages. The
/// closure takes two inputs:
/// 1. The message to transmit. This value is consumed during transmission.
/// 2. The buffer to write the transmitted values into (ranging [-1, 1]).
///
/// The closure returns a tuple with two values:
/// 1. The number of samples written. This is typically the number of samples in the input buffer,
///    but can be less if the message is transmitted completely.
/// 2. A boolean indicating whether the message has been transmitted completely. Message completion
///    means that all message bits have been sent, not including any end of message padding bits
///    since those require knowledge of the next message to be transmitted.
///
/// The writer maintains state, so subsequent calls to the closure will continue writing the
/// message until it is completely written. After message completion, another message can be
/// transmitted simply by calling with a new message.
///
/// The returned closure operates in sample space rather than absolute time, meaning all time
/// increments are `1/S` seconds.
///
/// *Note: this writer actually writes messages with a 13.33 kHz carrier, so the true 40 kHz
/// carrier signal is the third harmonic of the output. This is because a 40 kHz signal cannot be
/// adequately sampled at common audio frequencies.*
///
/// # Examples
///
/// ```
/// # use signals::junghans::{Junghans, make_writer};
/// # use signals::MessageGenerator;
/// // Construct a Junghans object to generate messages
/// let j = Junghans::new(
/// 			time::tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
/// 		).expect("Invalid timezone offset");
///
/// // Get a message for the current time
/// let m = j.get_message(&mut time::now().unwrap()).expect("Time must be >=0");
/// // Convert from absolute time to sample time
/// let mut s = m.sample::<48000>();
///
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
///
/// 	// Use the results in buf
///
/// 	if done { break; }
/// };
/// ```
pub fn make_writer<const S: u64>() -> impl FnMut(&mut SampledMessage<S>, &mut [f32]) -> (usize, bool) {
	let mut i: u64 = 0;
	let mut bitstart: u64 = 0;
	let mut state = WriterState::Start(true);
	move |message: &mut SampledMessage<S>, data: &mut [f32]| -> (usize, bool) {
		let message = &mut message.0;
		let start = i;
		let mut message_completed = false;
		for sample in data.iter_mut() {
			let (timing_on, timing_total) = match state {
				WriterState::Start(first) => {
					if first {
						((S*12/100) + message.delay as u64, (S*4/10) + message.delay as u64) // (>=120ms, >=400ms)
					} else {
						(S*12/100, S*4/10) // (120ms, 400ms)
					}
				}
				WriterState::Bit(_, val) => {
					if val {
						(S*9/100, S*3/10) // (90ms, 300ms)
					} else {
						(S*6/100, S*2/10) // (60ms, 200ms)
					}
				}
				WriterState::End => {
					if message.delay > (S*3/10) as i64 {
						(S*6/100, S*2/10) // (60ms, 200ms)
					} else {
						(S*9/100, S*3/10) // (90ms, 300ms)
					}
				}
			};

			let power = if i < bitstart + timing_on { 1.0 } else { 0.1 };

			let pos = (i % S) as f32 / S as f32;
			*sample = power * sin32(PI * 2. * 40000. / 3. * pos);
			i += 1;

			if i >= bitstart + timing_total {
				bitstart = i;
				let oldstate = state;
				state.advance(message, timing_total);
				if oldstate != WriterState::End && state == WriterState::End {
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
	use std::{eprintln, vec::Vec};
	use super::*;

	fn get_timezone() -> Timezone {
		tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap()
	}

	#[test]
	fn timezone_test() {
		assert_eq!(Junghans::new(tz::parse_tzstring("ABC9:20".as_bytes()).ok()),
				   Err(MessageError::UnsupportedTimezoneOffset(-33600)));
	}

	#[test]
	fn message_test() {
		let timezone = get_timezone();
		let m = MessageUncompressed::new(1716742705, &timezone).unwrap();
		assert_eq!(m.utc_sec_ones, 5);
		assert_eq!(m.utc_sec_tens, 2);
		assert_eq!(m.utc_min_ones, 8);
		assert_eq!(m.utc_min_tens, 5);
		assert_eq!(m.utc_hour_ones, 6);
		assert_eq!(m.utc_hour_tens, 1);
		assert_eq!(m.utc_yday_ones, 7);
		assert_eq!(m.utc_yday_tens, 4);
		assert_eq!(m.utc_yday_huns, 1);
		assert_eq!(m.utc_year_ones, 4);
		assert_eq!(m.utc_year_tens, 2);
		assert_eq!(m.offset, 8);
		assert_eq!(m.offset2, 12);
		assert_eq!(m.dstblock, 0);
		assert_eq!(m.checksum, 0xA8);

		let (p, d) = m.pack();
		assert_eq!(p.reverse_bits(), 0x551597450A3022A0);
		assert_eq!(d, 14500000000);
	}

	#[test]
	fn timing_test() {
		let j = Junghans::new(Some(get_timezone())).unwrap();
		let mut time = TimeSpec {
			sec: 1716742690,
			nsec: 123456789,
		};

		let mut message = j.get_message(&mut time).unwrap();
		assert_eq!(message.packed.reverse_bits(), 0x551597450A3022A0);
		assert_eq!(message.delay, 376543211);
		assert_eq!(time.sec, 1716742705);
		assert_eq!(time.nsec, 0);

		message = j.get_message(&mut time).unwrap();
		assert_eq!(message.packed.reverse_bits(), 0x091597450A302520);
		assert_eq!(message.delay, 700000000);
		assert_eq!(time.sec, 1716742720);
		assert_eq!(time.nsec, 0);

		message = j.get_message(&mut time).unwrap();
		assert_eq!(message.packed.reverse_bits(), 0x6B1597450A3030E0);
		assert_eq!(message.delay, 1300000000);
		assert_eq!(time.sec, 1716742736);
		assert_eq!(time.nsec, 0);
	}

	fn get_message(j: &Junghans, time: &mut TimeSpec) -> SampledMessage<48000> {
		j.get_message(time).unwrap().sample()
	}

	fn calculate_power(buffer: &[f32]) -> f32 {
		if buffer.len() == 0 {
			0.
		} else {
			buffer.iter().copied().reduce(|acc, x| acc + x.abs()).unwrap() / (buffer.len() as f32)
		}
	}

	fn check_is_high(buffer: &[f32]) {
		assert!((calculate_power(buffer) - 0.63).abs() < 0.01)
	}

	fn check_is_low(buffer: &[f32]) {
		assert!((calculate_power(buffer) - 0.063).abs() < 0.01)
	}

	fn check_is_zero(buffer: &[f32], bound: usize) -> usize {
		check_is_high(&buffer[bound..bound + 2880]);
		check_is_low(&buffer[bound + 2880..bound + 9600]);
		bound + 9600
	}

	fn check_is_one(buffer: &[f32], bound: usize) -> usize {
		check_is_high(&buffer[bound..bound + 4320]);
		check_is_low(&buffer[bound + 4320..bound + 14400]);
		bound + 14400
	}

	#[test]
	fn transmit_test() {
		let mut writer = make_writer();
		let j = Junghans::new(Some(get_timezone())).unwrap();
		let mut time = TimeSpec {
			sec: 1716742690,
			nsec: 123456789,
		};

		let mut buf = Vec::<f32>::with_capacity(800000);
		unsafe {
			buf.set_len(800000);
		}
		let buf = buf.as_mut_slice();

		let mut message = get_message(&j, &mut time);
		assert_eq!(writer(&mut message, buf), (714074, true));
		let mut bound = message.0.delay as usize + 5760;
		check_is_high(&buf[0..bound]);
		check_is_low(&buf[bound..bound + 13440]);
		bound += 13440;
		let mut packed = 0x551597450A3022A0_u64.reverse_bits();
		for _ in 1..59 {
			let bit = (packed & 1) > 0;
			bound = if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};

			packed >>= 1;
		}

		message = get_message(&j, &mut time);
		assert_eq!(writer(&mut message, buf), (720000, true));
		bound = 0;
		packed = 0x4;
		for _ in 0..3 {
			let bit = (packed & 1) > 0;
			bound = if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};

			packed >>= 1;
		}
		check_is_high(&buf[bound..bound + 5760]);
		check_is_low(&buf[bound + 5760..bound + 19200]);
		bound += 19200;
		packed = 0x091597450A302520_u64.reverse_bits();
		for _ in 0..59 {
			let bit = (packed & 1) > 0;
			bound = if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};

			packed >>= 1;
		}

		message = get_message(&j, &mut time);
		assert_eq!(writer(&mut message, buf),(768000, true));
		bound = 0;
		packed = 0x20;
		for _ in 0..6 {
			let bit = (packed & 1) > 0;
			bound = if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};

			packed >>= 1;
		}
		check_is_high(&buf[bound..bound + 5760]);
		check_is_low(&buf[bound + 5760..bound + 19200]);
		bound += 19200;
		packed = 0x6B1597450A3030E0_u64.reverse_bits();
		for _ in 0..59 {
			let bit = (packed & 1) > 0;
			bound = if bit {
				check_is_one(buf, bound)
			} else {
				check_is_zero(buf, bound)
			};

			packed >>= 1;
		}
	}

	#[test]
	fn module_doctest() {
		// Construct a Junghans object to generate messages
		let j = Junghans::new(
					// Timezone is used to configure the watch's local time
					tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
				).expect("Invalid timezone offset");

		// Get a message for the current time
		let m = j.get_message(&mut time::now().unwrap());
		match m {
			Ok(m) => {
				// Make a writer that converts the message into wire format at 48 kHz
				let mut writer = make_writer::<48000>();
				// Convert real time (nanoseconds) to sample time (48 kHz)
				let mut s = m.sample();
				// Create a buffer with enough space to hold the entire 15s encoded message
				let mut buf = Vec::<f32>::with_capacity(800000);
				unsafe {
					buf.set_len(800000);
				}
				let buf = buf.as_mut_slice();
				// Write the message to the buffer
				writer(&mut s, buf);

				// Use the results in buf
			},
			Err(e) => {
				// Errors only occur if the input time is before the Unix epoch (Jan 1, 1970)
				eprintln!("{}", e);
			}
		}

		// Documentation for TIMEZONE_OFFSET
		// UTC-9
		let mut offset = -9;
		// Offset such that UTC-12 is zero
		offset += 12;
		// Convert to 15 minute chunks
		offset *= 4;
		// Get configuration value corresponding to UTC-9
		assert_eq!(TIMEZONE_OFFSET[offset as usize], 0x10);

		// Documentation for CHECKSUM_TABLE
		let message = b"test";
		let checksum = message.iter()
			.copied()
			.reduce(|a, b| CHECKSUM_TABLE[a as usize] ^ b)
			.map(|v| CHECKSUM_TABLE[v as usize]);
		assert_eq!(checksum, Some(0x4c));

		// Documentation for make_checksum_index
		assert_eq!(make_checksum_index(0x12, 0xab), 0xb2);

		// Documentation for Junghans::new
		let j = Junghans::new(
			tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
		);
		match j {
			Ok(_j) => {
				// Create & use messages
			},
			Err(_) => {
				// Known valid offset (UTC-8 / UTC-7) that cannot fail
				let _j = Junghans::new(
					tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").ok()
				).unwrap();
				// Create & use messages
			}
		}

		// Documentation for make_writer
		// Construct a Junghans object to generate messages
		let j = Junghans::new(
					tz::parse_file("/usr/share/zoneinfo/America/Los_Angeles").ok()
				).expect("Invalid timezone offset");

		// Get a message for the current time
		let m = j.get_message(&mut time::now().unwrap()).expect("Time must be >=0");
		// Convert from absolute time to sample time
		let mut s = m.sample();
		// Make a writer that converts the message into wire format at 48 kHz
		let mut writer = make_writer::<48000>();
		// Create a buffer to write 21.33ms of signal at a time
		let mut buf = Vec::<f32>::with_capacity(1024);
		unsafe {
			buf.set_len(1024);
		}
		let buf = buf.as_mut_slice();

		loop {
			// Write the message to the buffer
			let (_i, done) = writer(&mut s, buf);

			// Use the results in buf

			if done { break; }
		};
	}
}
