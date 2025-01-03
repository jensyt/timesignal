//! Support for transmitting the WWVB time signal.
//!
//! See [WWVB documentation](https://en.wikipedia.org/wiki/WWVB) for details. This module fully
//! supports WWVB's amplitude modulated time code, but only has partial support for WWVB's phase
//! modulated time code. Unsupported features include:
//! - **6-minute time frames**. 1-minute frames are transmitted instead.
//! - **Full-year DST in the `dst_next` field**. Time and current DST information can be
//!   transmitted in full-year DST situations successfully, but the `dst_next` field will be
//!   incorrectly set to `0x23` (DST transition occurs at a different time).
//! - **Negative leap seconds**. All leap seconds to date have been positive.
//! - **Message frames**. These are special, non-time messages that are not intended use of this
//!   module.
//!
//! # Examples
//! ```
//! // Construct a WWVB object to generate messages
//! let d = WWVB::new(None).unwrap();
//!
//! // Get a message for the current time
//! let m = d.get_message(&mut crate::time::currenttime().unwrap());
//! match m {
//! 	Ok(mut m) => {
//! 		// Convert real time (nanoseconds) to sample time (48 kHz)
//! 		m.delay = (m.delay * 48) / 1000000;
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

use crate::time::{minute_of_century_from_timestamp, nextleapsecond, wday_from_ymd, Seconds, TimeSpec, Tm};
use crate::tz::{self, Timezone, TzDateRule};
use crate::Message;
use std::f32::consts::PI;
use std::{fmt, error};

/// All known UT1-UTC offsets.
///
/// Values are pre-encoded for transmission, where the MSB four bits indicate the sign (`0xA_` is
/// positive, `0x4_` is negative), and the LSB four bits indicate the magnitude (`0x_5` is `0.5s`).
/// Magnitudes can range `[0, 9]` => `[0.0s, 0.9s]`. Full example: `0x43 => -0.3s`.
const DUT1: [(i64, u8); 112] = [
	(677376000,  0xA2), (682819200,  0xA1), (687657600,  0xA0), (690681600,  0x41),
	(705196800,  0x45), (715478400,  0xA3), (719712000,  0xA2), (722736000,  0xA1),
	(726969600,  0xA0), (736646400,  0x43), (741484800,  0xA6), (749952000,  0xA4),
	(753580800,  0xA3), (757209600,  0xA2), (763862400,  0xA0), (766886400,  0x41),
	(773020800,  0xA8), (793497600,  0xA3), (795312000,  0xA2), (797731200,  0xA1),
	(801619200,  0xA0), (805593600,  0x41), (810432000,  0x42), (814665600,  0x43),
	(817689600,  0x44), (820454400,  0xA5), (824947200,  0xA4), (829180800,  0xA3),
	(832204800,  0xA2), (839462400,  0xA1), (844300800,  0xA0), (849744000,  0x41),
	(855187200,  0x42), (858816000,  0x43), (863049600,  0x44), (867283200,  0x45),
	(867715200,  0xA5), (874540800,  0xA4), (878169600,  0xA3), (882403200,  0xA2),
	(887846400,  0xA1), (890870400,  0xA0), (894499200,  0x41), (902966400,  0x42),
	(912038400,  0x43), (915148800,  0xA7), (920505600,  0xA6), (927763200,  0xA5),
	(939859200,  0xA4), (947116800,  0xA3), (955584000,  0xA2), (971913600,  0xA1),
	(983404800,  0xA0), (1002153600, 0x41), (1013644800, 0x42), (1035417600, 0x43),
	(1049328000, 0x44), (1083196800, 0x45), (1111017600, 0x46), (1136073600, 0xA3),
	(1146096000, 0xA2), (1159401600, 0xA1), (1166745600, 0xA0), (1173916800, 0x41),
	(1181779200, 0x42), (1196294400, 0x43), (1205366400, 0x44), (1218067200, 0x45),
	(1227139200, 0x46), (1236816000, 0xA3), (1244678400, 0xA2), (1257984000, 0xA1),
	(1268265600, 0xA0), (1275523200, 0x41), (1294272000, 0x42), (1305158400, 0x43),
	(1320364800, 0x44), (1328745600, 0x45), (1336608000, 0x46), (1341100800, 0xA4),
	(1351123200, 0xA3), (1359590400, 0xA2), (1365638400, 0xA1), (1377129600, 0xA0),
	(1384992000, 0x41), (1392854400, 0x42), (1399507200, 0x43), (1411603200, 0x44),
	(1419465600, 0x45), (1426723200, 0x46), (1432771200, 0x47), (1435708800, 0xA3),
	(1442448000, 0xA2), (1448496000, 0xA1), (1454198400, 0xA0), (1458777600, 0x41),
	(1463616000, 0x42), (1472688000, 0x43), (1479340800, 0x44), (1483228800, 0xA6),
	(1485388800, 0xA5), (1490832000, 0xA4), (1498694400, 0xA3), (1512000000, 0xA2),
	(1521072000, 0xA1), (1537488000, 0xA0), (1547683200, 0x41), (1556755200, 0x42),
	(1626480000, 0x41), (1658966400, 0xA0), (1725494400, 0xA1), (1735171200, 0xA0)
];

/// Encoded DST and leap second indicators for phase modulated signal.
///
/// The table is split into two halves of four values. The first half indicates no leap second at
/// the end of this month. The second half indicates a positive leap second at the end of this
/// month.
///
/// The four values within each half correspond to:
/// 1. DST not in effect and not changing in the next 24 hours.
/// 2. DST in effect, but changing to standard time in the next 24 hours.
/// 3. DST not in effect, but changing to DST in the next 24 hours.
/// 4. DST in effect and not changing in the next 24 hours.
///
/// # Examples
/// ```
/// // Wed, Jul 04 2012 17:30:18 UTC
/// let time = 1341423018;
/// // US western time zone
/// let timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
///
/// // Calendar date/time for current time
/// let utc = Tm::new(time).expect("Time must be >= 0");
///
/// // Start of current & next UTC days (Jul 4, 2012 00:00:00 UTC and Jul 5, 2012 00:00:00 UTC)
/// let start_of_utc_day = time - utc.hour as i64 * 3600 - utc.min as i64 * 60 - utc.sec as i64;
/// let next_utc_day = start_of_utc_day + 86400;  // 24 hours
/// let tzinfo_1 = timezone.info(start_of_utc_day);
/// let tzinfo_2 = timezone.info(next_utc_day);
///
/// // Whether the next leap second is within the next 28 days (~ 1 month)
/// let leapsecond = match nextleapsecond(time)
/// 			 			.map(|(t, _)| t - time)
/// 						.filter(|&t| 0 < t && t <= 2419200) // 28 days
/// {
/// 	Some(_) => 0x1,
/// 	None    => 0x0
/// };
///
/// // DST config (0x3 => DST in effect, not changing in next 24 hours)
/// let dst = ((tzinfo_2.isdst as u8) << 1) | tzinfo_1.isdst as u8;
/// let dstleap = DST_LEAP_ENCODING.get((dst + leapsecond * 4) as usize)
/// 								.copied()
/// 								.unwrap_or(0x10);
///
/// // Encoded DST/leap config => DST in effect, not changing in next 24 hours, no leap second this
/// // month.
/// assert_eq!(dstleap, 0x03);
/// ```
const DST_LEAP_ENCODING: [u8; 8] = [0x10, 0x25, 0x26, 0x03,
									0x31, 0x34, 0x32, 0x37];

/// Encoded `dst_next` values for standard->DST transitions.
///
/// This 8x3 table represents the 8 Sundays starting with the first Sunday in March, and three
/// transition times per Sunday (1am, 2am, 3am).
///
/// # Examples
/// ```
/// timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0/3,M11.1.0").unwrap();
/// // 2rd Sunday of March; 3am
/// assert_eq!(next_dst(2024, false, &timezone), 0x20);
/// ```
const NEXT_DST_SPRING: [u8; 24] = [0x31, 0x2A, 0x04,  // 1st Sunday of March; 1am, 2am, 3am
								   0x26, 0x1B, 0x20,  // 2nd Sunday of March; 1am, 2am, 3am
								   0x25, 0x0E, 0x34,  // 3rd Sunday of March; 1am, 2am, 3am
								   0x15, 0x01, 0x2C,  // 4th Sunday of March; 1am, 2am, 3am
								   0x3E, 0x02, 0x38,  // 4th Sunday since M1; 1am, 2am, 3am
								   0x16, 0x08, 0x10,  // 5th Sunday since M1; 1am, 2am, 3am
								   0x37, 0x0D, 0x32,  // 6th Sunday since M1; 1am, 2am, 3am
								   0x3D, 0x29, 0x1C]; // 7th Sunday since M1; 1am, 2am, 3am

/// Encoded `dst_next` values for DST->standard transitions.
///
/// This 8x3 table represents the 8 Sundays starting with the fourth Sunday before the first Sunday
/// in November, and three transition times per Sunday (1am, 2am, 3am).
///
/// # Examples
/// ```
/// timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
/// // 1st Sunday of November, 2am
/// assert_eq!(next_dst(2024, true, &timezone), 0x1B);
/// ```
const NEXT_DST_FALL: [u8; 24] = [0x37, 0x0D, 0x32,  // 4th Sunday before N1; 1am, 2am, 3am
								 0x15, 0x01, 0x2C,  // 3rd Sunday before N1; 1am, 2am, 3am
								 0x31, 0x2A, 0x04,  // 2nd Sunday before N1; 1am, 2am, 3am
								 0x16, 0x08, 0x10,  // 1st Sunday before N1; 1am, 2am, 3am
								 0x26, 0x1B, 0x20,  // 1st Sunday of November; 1am, 2am, 3am
								 0x3E, 0x02, 0x38,  // 2nd Sunday of November; 1am, 2am, 3am
								 0x25, 0x0E, 0x34,  // 3rd Sunday of November; 1am, 2am, 3am
								 0x3D, 0x29, 0x1C]; // 4th Sunday of November; 1am, 2am, 3am

/// The error type for constructing WWVB messages.
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

impl error::Error for Error {}

/// Get the codeword associated with next scheduled DST transition.
///
/// This function supports all [Enhanced WWVB] DST transition codes defined in Table 8, except when
/// DST is in effect for the full year (0x2F).
///
/// Unfortunately, there are many ways for DST transition times to be defined, making it impossible
/// to support all possible definitions that resolve to one of the table entries. This function
/// assumes the use of [`TzDateRule::M`] defitions, which are common for US timezones. Other rule
/// types will return 0x23 ("DST transition occurs at a different time"). If no timezone rule is
/// defined, this function will return 0x07 ("No DST period scheduled this year"), which may be
/// incorrect if `timezone` has transition times but no rule.
///
/// [Enhanced WWVB]:
/// https://www.nist.gov/system/files/documents/2017/05/09/NIST-Enhanced-WWVB-Broadcast-Format-1_01-2013-11-06.pdf
///
/// # Examples
/// ```
/// let mut timezone = tz::parse_tzstring(b"PST8").unwrap();
/// assert_eq!(next_dst(2024, false, &timezone), 0x07);
///
/// // Current US west coast rule (on 2024-12-28)
/// timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
/// assert_eq!(next_dst(2024, false, &timezone), 0x1B);
/// assert_eq!(next_dst(2024, true, &timezone), 0x1B);
/// ```
fn next_dst(year: u16, isdst: bool, timezone: &Timezone) -> u8 {
	// Get the DST rule if it exists
	let dst = match timezone.spec().and_then(|v| v.dst.map(|(_, dst)| dst)) {
		Some(dst) => dst,
		None => { return 0x07 } // No DST
	};

	if isdst {
		let index = match dst.fromdst {
			// Check for valid configurations
			(TzDateRule::M(11, w @ (1..5), 0), t @ (3600 | 7200 | 10800)) => {
				// One of the four Sundays in November
				9 +
				t as usize / 3600 - 1 +
				w as usize * 3
			}
			(TzDateRule::M(11, 5, 0), t @ (3600 | 7200 | 10800)) => {
				// 5 Sundays in November if it starts Sat-Sun
				let wday = wday_from_ymd(year, 11, 1);
				if wday == 0 || wday == 6 {
					// 5th Sunday of November is unsupported
					usize::MAX
				} else {
					// 4th Sunday of November
					21 + (t as usize / 3600 - 1)
				}
			}
			(TzDateRule::M(10, w, 0), t @ (3600 | 7200 | 10800)) => {
				// 5 Sundays in October if it starts Fri-Sun
				let wday = wday_from_ymd(year, 10, 1);
				((t as usize / 3600 - 1) +
				 (w as usize) * 3).wrapping_sub(
				 if wday == 0 || wday > 4 { 6 } else { 3 }
				)
			}
			_ => usize::MAX // Invalid index
		};
		NEXT_DST_FALL.get(index).copied().unwrap_or(0x23)
	} else {
		let index = match dst.todst {
			// Check for valid configurations
			(TzDateRule::M(3, w @ (1..5), 0), t @ (3600 | 7200 | 10800)) => {
				// One of the four Sundays in March
				(t as usize / 3600 - 1) +
				(w as usize - 1) * 3
			}
			(TzDateRule::M(3, 5, 0), t @ (3600 | 7200 | 10800)) => {
				// 5 Sundays in March if it starts Fri-Sun
				let wday = wday_from_ymd(year, 3, 1);
				(t as usize / 3600 - 1) +
				if wday == 0 || wday > 4 { 12 } else { 9 }
			}
			(TzDateRule::M(4, w, 0), t @ (3600 | 7200 | 10800)) => {
				// 5 Sundays in March if it starts Fri-Sun
				let wday = wday_from_ymd(year, 3, 1);
				(t as usize / 3600 - 1) +
				(w as usize) * 3 +
				if wday == 0 || wday > 4 { 12 } else { 9 }
			}
			_ => usize::MAX // Invalid index
		};
		NEXT_DST_SPRING.get(index).copied().unwrap_or(0x23)
	}
}

/// An unpacked / uncompressed WWVB message.
///
/// This type contains all of the components of the encoded WWVB message, but in an unpacked
/// format that is easier to inspect. See [`MessageUncompressed::pack`] for details on getting and
/// using the packed message, which can be transmitted to a watch.
///
/// # Examples
/// ```
/// // US Pacific timezone, UTC-8 (standard time) / UTC-7 (daylight savings time)
/// let timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
///
/// // Wednesday, July 4, 2012. 10:30:18 UTC-7 / 17:30:18 UTC.
/// let m = MessageUncompressed::new(1341423018, &timezone).unwrap();
/// assert_eq!(m.utc_min_ones, 0);            // Minute 30
/// assert_eq!(m.utc_min_tens, 3);
/// assert_eq!(m.utc_hour_ones, 7);           // Hour 17
/// assert_eq!(m.utc_hour_tens, 1);
/// assert_eq!(m.utc_yday_ones, 6);           // Day 186
/// assert_eq!(m.utc_yday_tens, 8);
/// assert_eq!(m.utc_yday_huns, 1);
/// assert_eq!(m.utc_year_ones, 2);           // Year [20]12
/// assert_eq!(m.utc_year_tens, 1);
/// assert_eq!(m.dut1, 0xA4);                 // DUT1 0.4s
/// assert_eq!(m.leapyear, 0x1);              // Leap year
/// assert_eq!(m.leapsecond, 0x0);            // No leap second this month
/// assert_eq!(m.dst, 0x3);                   // DST in effect and not changing in next 24 hours
/// assert_eq!(m.minute_of_century, 6578970); // Minute 6578970 of century (since Jan 1, 2000)
/// assert_eq!(m.next_dst, 0x1B);             // Next DST change is 1st Sunday of Nov, 2am
///
/// let (a, p) = m.pack();
/// assert_eq!(a.reverse_bits(), 0x3004E1418A408960);
/// assert_eq!(p.reverse_bits(), 0x3B4483218C341B60);
/// ```
struct MessageUncompressed {
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
	/// DUT1 (UT1-UTC) encoded value. See [`DUT1`] for more details.
	dut1: u8,
	/// Whether it is a leap year (`1`) or not (`0`).
	leapyear: u8,
	/// Whether there is an upcoming leap second at the end of the month (`1`) or not (`0`).
	leapsecond: u8,
	/// DST configuration, from MSB to LSB:
	/// - Bits 2-7: Unused
	/// - Bit 1: DST in effect at *next* UTC 00:00:00.
	/// - Bit 0: DST in effect at *previous* UTC 00:00:00.
	dst: u8,
	/// Minutes since the last beginning of century, e.g. January 1, 2000; 00:00:00 UTC.
	minute_of_century: u32,
	/// Next DST encoded value. See [`next_dst`] for details.
	next_dst: u8
}

impl MessageUncompressed {
	/// Create a new WWVB message.
	///
	/// Input `time` should be greater than or equal to zero. `timezone` is used to set DST
	/// configuration for `time`.
	///
	/// See [module documentation](crate::wwvb) for limitations on phase modulated signals.
	///
	/// # Errors
	///
	/// Returns [`Error::UnsupportedTime`] if `time < 0`.
	fn new(time: i64, timezone: &Timezone) -> Result<MessageUncompressed, Error> {
		let utc = Tm::new(time).ok_or(Error::UnsupportedTime(time))?;
		let start_of_utc_day = time - utc.hour as i64 * 3600 - utc.min as i64 * 60 - utc.sec as i64;
		let next_utc_day = start_of_utc_day + 86400;  // 24 hours
		let dst_today = timezone.info(start_of_utc_day).isdst;
		let dst_tomorrow = timezone.info(next_utc_day).isdst;

		let leapsecond = match nextleapsecond(time)
						 .map(|(t, _)| t - time)
						 .filter(|&t| 0 < t && t <= 2419200) // 28 days
		{
			Some(_) => 0x1,
			None    => 0x0
		};

		let t = match DUT1.binary_search_by_key(&time, |&(t, _)| t) {
			Ok(t) => t,
			Err(t) => t.wrapping_sub(1),
		};
		let dut1 = DUT1.get(t).map(|&(_, d)| d).unwrap_or(0xA0);

		Ok(MessageUncompressed {
			utc_min_ones: utc.min % 10,
			utc_min_tens: utc.min / 10,
			utc_hour_ones: utc.hour % 10,
			utc_hour_tens: utc.hour / 10,
			utc_yday_ones: (utc.yday % 10) as u8,
			utc_yday_tens: ((utc.yday / 10) % 10) as u8,
			utc_yday_huns: (utc.yday / 100) as u8,
			utc_year_ones: (utc.year % 10) as u8,
			utc_year_tens: ((utc.year / 10) % 10) as u8,
			dut1,
			leapyear: utc.isleapyear() as u8,
			leapsecond,
			dst: ((dst_tomorrow as u8) << 1) | dst_today as u8,
			minute_of_century: minute_of_century_from_timestamp(time),
			next_dst: next_dst(utc.year(), dst_tomorrow, timezone)
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
		let mut a: u64 = ((self.utc_min_tens as u64) & 0x7) << 60;
		a |= ((self.utc_min_ones as u64) & 0xf) << 55;
		a |= ((self.utc_hour_tens as u64) & 0x3) << 50;
		a |= ((self.utc_hour_ones as u64) & 0xf) << 45;
		a |= ((self.utc_yday_huns as u64) & 0x3) << 40;
		a |= ((self.utc_yday_tens as u64) & 0xf) << 35;
		a |= ((self.utc_yday_ones as u64) & 0xf) << 30;
		a |= ((self.dut1 as u64)) << 20;
		a |= ((self.utc_year_tens as u64) & 0xf) << 15;
		a |= ((self.utc_year_ones as u64) & 0xf) << 10;
		a |= ((self.leapyear as u64) & 0x1) << 8;
		a |= ((self.leapsecond as u64) & 0x1) << 7;
		a |= ((self.dst as u64) & 0x3) << 5;

		let mut p: u64 = 0x3B40000000000000;
		// Parity for bits 25, 22, 20, 19, 16, 15, 14, 13, 12, 8, 7, 5, 4, 3, 1
		p |= ((self.minute_of_century & 0x259F1BA).count_ones() as u64 & 0x1) << 50;
		// Parity for bits 24, 21, 19, 18, 15, 14, 13, 12, 11, 7, 6, 4, 3, 2, 0
		p |= ((self.minute_of_century & 0x12CF8DD).count_ones() as u64 & 0x1) << 49;
		// Parity for bits 25, 23, 22, 19, 18, 17, 16, 15, 11, 10, 8, 7, 6, 4, 2
		p |= ((self.minute_of_century & 0x2CF8DD4).count_ones() as u64 & 0x1) << 48;
		// Parity for bits 24, 22, 21, 18, 17, 16, 15, 14, 10, 9, 7, 6, 5, 3, 1
		p |= ((self.minute_of_century & 0x167C6EA).count_ones() as u64 & 0x1) << 47;
		// Parity for bits 23, 21, 20, 17, 16, 15, 14, 13, 9, 8, 6, 5, 4, 2, 0
		p |= ((self.minute_of_century & 0xB3E375).count_ones() as u64 & 0x1) << 46;
		// Time[25] goes to bit 45
		p |= ((self.minute_of_century & 0x2000000) as u64) << 20;
		// Time[0] goes to bit 44
		p |= ((self.minute_of_century & 0x1) as u64) << 44;
		// Time[24:16] goes to bit 43:35
		p |= ((self.minute_of_century & 0x1FF0000) as u64) << 19;
		// Time[15:7] goes to bit 33:25
		p |= ((self.minute_of_century & 0xFF80) as u64) << 18;
		// Time[6:0] goes to bit 23:17
		p |= ((self.minute_of_century & 0x7F) as u64) << 17;
		p |= (DST_LEAP_ENCODING.get((self.dst + self.leapsecond * 4) as usize)
								.copied()
								.unwrap_or(0x10) as u64) << 11;
		p |= ((self.next_dst as u64) & 0x3f) << 5;

		(a.reverse_bits(), p.reverse_bits())
	}
}


/// WWVB message generator.
///
/// Messages returned from [`WWVB::get_message`] should be used with the writer returned by
/// [`make_writer`].
///
/// # Examples
///
/// ```
/// // Construct a WWVB object to generate messages
/// let d = WWVB::new(None).expect("Error getting NYC timezone data");
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
pub struct WWVB {
	ny_tz: Timezone
}

/// Construct a new WWVB object.
///
/// This is a convenience function, see [`WWVB::new`] for details.
#[inline(always)]
pub fn new(timezone: Option<Timezone>) -> Result<WWVB, Error> {
	WWVB::new(timezone)
}

impl WWVB {
	/// Construct a new WWVB object.
	///
	/// If the input `timezone` is `None`, this function defaults to reading
	/// `/usr/share/zoneinfo/America/New_York` for timezone information.
	///
	/// # Errors
	///
	/// Returns [`Error::TimezoneError`] if there was an error reading
	/// `/usr/share/zoneinfo/America/New_York`.
	///
	/// # Examples
	///
	/// ```
	/// let d = WWVB::new(None);
	/// match d {
	/// 	Ok(_d) => {
	/// 		// Create & use messages
	/// 	},
	/// 	Err(_) => {
	/// 		// Known valid offset (UTC-5 / UTC-4) that cannot fail
	/// 		let _d = WWVB::new(
	/// 			crate::tz::parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").ok()
	/// 		).unwrap();
	/// 		// Create & use messages
	/// 	}
	/// }
	/// ```
	pub fn new(timezone: Option<Timezone>) -> Result<WWVB, Error> {
		match timezone {
			Some(t) => Ok(WWVB { ny_tz: t }),
			None => tz::parse_file("/usr/share/zoneinfo/America/New_York")
						.map(|t| WWVB { ny_tz: t })
						.map_err(|e| Error::TimezoneError(e))
		}
	}

	/// Get a message for the given time.
	///
	/// This function returns a message for the minute that started on or before `time`, i.e. the
	/// message represents the instant at the **beginning** of the transmission.
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
	/// Returns [`Error::UnsupportedTime`] if the minute that includes `time` is less than zero.
	///
	/// # Examples
	///
	/// ```
	/// let wwvb = WWVB::new(None).unwrap();
	/// // Sun, May 26, 2024. 16:57:25 UTC.
	/// let mut time = TimeSpec {
	/// 	sec: 1716742645,
	/// 	nsec: 123456789
	/// };
	///
	/// let message = wwvb.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:58:00 UTC.
	/// assert_eq!(time.sec, 1716742680);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x5384C121CA011160);
	/// assert_eq!(message.packed_alt.reverse_bits(), 0x3B40161B56F21B60);
	/// assert_eq!(message.delay, 25123456789);
	/// assert_eq!(message.leap, false);
	///
	/// let message = wwvb.get_message(&mut time).unwrap();
	/// // Sun, May 26, 2024. 16:59:00 UTC.
	/// assert_eq!(time.sec, 1716742740);
	/// assert_eq!(time.nsec, 0);
	/// assert_eq!(message.packed.reverse_bits(), 0x5404C121CA011160);
	/// assert_eq!(message.packed_alt.reverse_bits(), 0x3B46C61B56F41B60);
	/// assert_eq!(message.delay, 0);
	/// assert_eq!(message.leap, false);
	/// ```
	pub fn get_message(&self, time: &mut TimeSpec) -> Result<Message, Error> {
		// Find the start of this minute (exactly)
		let time_in_min = time.sec % 60;
		let sec = time.sec - time_in_min;

		// Compute the message
		let message = MessageUncompressed::new(sec, &self.ny_tz)?;
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
	/// LSB), the value of that bit for both amplitude modulated ([`AMBit`]) and phase modulated
	/// (`bool`) messages.
	Bit(u8, AMBit, bool),
	/// Transmitting a leap second, marker (amplitude modulation) and zero bit (phase modulation).
	Leap
}

impl WriterState {
	/// Advance the state machine to the next state.
	///
	/// The state machine advances as follows:
	/// - `Start` => `Bit(0, AMBit::Marker, _)`
	/// - `Bit(n, _, _)` => `Bit(n + 1, AMBit::Marker, _)` if `n % 10 == 8` else
	///   `Bit(n + 1, AMBit::Value(_), _)`
	/// - `Bit(59, _, _)` => `Leap` if `message.leap` else `Start`
	/// - `Leap` => `Start`
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance(&mut self, message: &mut Message) {
		*self = match *self {
			WriterState::Start => WriterState::Bit(0, AMBit::Marker, message.packed_alt & 1 > 0),
			WriterState::Bit(bit, _, _) => {
				message.packed >>= 1;
				message.packed_alt >>= 1;
				if bit < 59 {
					if bit % 10 == 8 {
						WriterState::Bit(bit + 1, AMBit::Marker, message.packed_alt & 1 > 0)
					} else {
						WriterState::Bit(bit + 1,
							AMBit::Value(message.packed & 1 > 0),
							message.packed_alt & 1 > 0)
					}
				} else if message.leap {
					WriterState::Leap
				} else {
					WriterState::Start
				}
			},
			WriterState::Leap => WriterState::Start
		}
	}

	/// Advance the state machine to a given bit.
	///
	/// If `bit > 59`, automatically advances to `Leap` or `Start` states as appropriate.
	///
	/// The state machine modifies `message` directly, consuming it as progress is made.
	fn advance_to(&mut self, message: &mut Message, bit: u8) {
		*self = if bit < 60 {
			message.packed >>= bit;
			message.packed_alt >>= bit;
			if bit % 10 == 9 {
				WriterState::Bit(bit, AMBit::Marker, message.packed_alt & 1 > 0)
			} else {
				WriterState::Bit(bit, AMBit::Value(message.packed & 1 > 0), message.packed_alt & 1 > 0)
			}
		} else if message.leap {
			WriterState::Leap
		} else {
			WriterState::Start
		}
	}
}

/// Make a writer to transmit WWVB messages sampled at 48 kHz.
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
/// returned from [`WWVB::get_message`] in `Message::delay` must be converted from nanoseconds
/// to samples, e.g. with `(message.delay * 48) / 1000000`.
///
/// *Note: this writer actually writes messages with a 20 kHz carrier, so the true 60 kHz carrier
/// signal is the third harmonic of the output. This is because a 60 kHz signal cannot be
/// adequately sampled at 48 kHz.*
///
/// # Examples
///
/// ```
/// // Construct a WWVB object to generate messages
/// let d = WWVB::new(None).expect("Error reading New York timezone");
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

		// Sample time when phase the modulated signal starts and the message ends.
		let timings = |x| (x + 4800, x + 48000); // (100ms, 1000ms)

		let start = i;
		let (mut phase_start, mut bitend) = timings(bitstart);
		let mut message_completed = false;
		for sample in data.iter_mut() {
			let (timing_on, phase) = match state {
				WriterState::Bit(_, AMBit::Marker, pm) => (38400, pm), // 800ms
				WriterState::Bit(_, AMBit::Value(true), pm) => (24000, pm), // 500ms
				WriterState::Bit(_, AMBit::Value(false), pm) => (9600, pm), // 200ms
				WriterState::Leap  => (38400, false), // 800ms
				_ => (0, false),
			};

			// Calculate amplitude modulation
			let power = if i < bitstart + timing_on {
				0.14
			} else {
				1.0
			};

			// Calculate phase modulation
			let phase_sign = if phase && i >= phase_start {
				-1.0
			} else {
				1.0
			};

			let pos = (i % 48000) as f32 / 48000.;
			*sample = power * phase_sign * f32::sin(PI * 2. * 60000. / 3. * pos);
			i += 1;

			if i >= bitend {
				bitstart = i;
				(phase_start, bitend) = timings(bitstart);
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
	use crate::tz;
	use super::*;

	#[test]
	fn next_dst_test() {
		let mut timezone = tz::parse_tzstring(b"PST8").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x07);

		timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x1B); // 2nd Sunday of March, 2am
		assert_eq!(next_dst(2024, true, &timezone), 0x1B); // 1st Sunday of November, 2am

		timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0/1,M11.1.0/1").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x26); // 2nd Sunday of March, 1am
		assert_eq!(next_dst(2024, true, &timezone), 0x26); // 1st Sunday of November, 1am

		timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0/3,M11.1.0/3").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x20); // 2nd Sunday of March, 3am
		assert_eq!(next_dst(2024, true, &timezone), 0x20); // 1st Sunday of November, 3am

		timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0/4,M11.1.0/3").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x23); // Invalid (4am)
		assert_eq!(next_dst(2024, true, &timezone), 0x20); // 1st Sunday of November, 3am

		timezone = tz::parse_tzstring(b"PST8PDT,M3.5.0,M11.5.0").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x02); // 4th Sunday after M1, 2am
		assert_eq!(next_dst(2023, false, &timezone), 0x01); // 4th Sunday of March, 2am
		assert_eq!(next_dst(2024, true, &timezone), 0x29); // 4th Sunday of November, 2am
		assert_eq!(next_dst(2025, true, &timezone), 0x23); // Invalid (5th Sunday of November)

		timezone = tz::parse_tzstring(b"PST8PDT,M4.4.0,M10.1.0").unwrap();
		assert_eq!(next_dst(2024, false, &timezone), 0x23); // Invalid (8th Sunday after M1)
		assert_eq!(next_dst(2023, false, &timezone), 0x29); // 7th Sunday after M1
		assert_eq!(next_dst(2024, true, &timezone), 0x0D); // 4th Sunday before N1
		assert_eq!(next_dst(2027, true, &timezone), 0x23); // Invalid (5th Sunday before N1)

		timezone = tz::parse_tzstring(b"PST8PDT,J10,J200").unwrap();
		assert_eq!(next_dst(2025, true, &timezone), 0x23); // Invalid rule type (J vs. M)
		assert_eq!(next_dst(2025, true, &timezone), 0x23); // Invalid rule type (J vs. M)
	}

	#[test]
	fn message_test() {
		let timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
		// Wed, Jul 04 2012 17:30:18 UTC
		let m = MessageUncompressed::new(1341423018, &timezone).unwrap();
		assert_eq!(m.utc_min_ones, 0);
		assert_eq!(m.utc_min_tens, 3);
		assert_eq!(m.utc_hour_ones, 7);
		assert_eq!(m.utc_hour_tens, 1);
		assert_eq!(m.utc_yday_ones, 6);
		assert_eq!(m.utc_yday_tens, 8);
		assert_eq!(m.utc_yday_huns, 1);
		assert_eq!(m.utc_year_ones, 2);
		assert_eq!(m.utc_year_tens, 1);
		assert_eq!(m.dut1, 0xA4);
		assert_eq!(m.leapyear, 0x1);
		assert_eq!(m.leapsecond, 0x0);
		assert_eq!(m.dst, 0x3);
		assert_eq!(m.minute_of_century, 6578970);
		assert_eq!(m.next_dst, 0x1B);

		let (a, p) = m.pack();
		assert_eq!(a.reverse_bits(), 0x3004E1418A408960);
		assert_eq!(p.reverse_bits(), 0x3B4483218C341B60);
	}

	#[test]
	fn timing_test() {
		let wwvb = WWVB::new(None).unwrap();
		// Sun, May 26, 2024. 16:57:25 UTC.
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let message = wwvb.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742680);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x5384C121CA011160);
		assert_eq!(message.packed_alt.reverse_bits(), 0x3B40161B56F21B60);
		assert_eq!(message.delay, 25123456789);
		assert_eq!(message.leap, false);

		let message = wwvb.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 1716742740);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x5404C121CA011160);
		assert_eq!(message.packed_alt.reverse_bits(), 0x3B46C61B56F41B60);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);

		time.sec = 741484800;
		let message = wwvb.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484860);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x000001408A648C60);
		assert_eq!(message.packed_alt.reverse_bits(), 0x3B41677160401B60);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, true);

		let message = wwvb.get_message(&mut time).unwrap();
		assert_eq!(time.sec, 741484920);
		assert_eq!(time.nsec, 0);
		assert_eq!(message.packed.reverse_bits(), 0x008001408A648C60);
		assert_eq!(message.packed_alt.reverse_bits(), 0x3B43377160421B60);
		assert_eq!(message.delay, 0);
		assert_eq!(message.leap, false);
	}

	fn get_message(j: &WWVB, time: &mut TimeSpec) -> Message {
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
		check_is_low(&buffer[bound..bound + 9600]);
		check_is_high(&buffer[bound + 9600..bound + 48000]);
	}

	fn check_is_one(buffer: &[f32], bound: usize) {
		check_is_low(&buffer[bound..bound + 24000]);
		check_is_high(&buffer[bound + 24000..bound + 48000]);
	}

	fn check_is_marker(buffer: &[f32], bound: usize) {
		check_is_low(&buffer[bound..bound + 38400]);
		check_is_high(&buffer[bound + 38400..bound + 48000]);
	}

	fn check_no_phase(buffer: &[f32], offset: usize) {
		for (i, &v) in buffer.iter().enumerate() {
			let p = 60000. / 3. / 48000. * ((offset + i) % 48000) as f32;
			let f = 0.14 * f32::sin(PI * 2. * p) - v;
			assert!(f > -0.01 && f < 0.01, "Failed -0.01 < {} < 0.01 for value {}", f, v);
		}
	}

	fn check_is_phase(buffer: &[f32], offset: usize, bitval: bool) {
		for (i, &v) in buffer.iter().enumerate() {
			let p = 60000. / 3. / 48000. * ((offset + i) % 48000) as f32;
			let f = if bitval {
				f32::sin(PI * 2. * p) + v
			} else {
				f32::sin(PI * 2. * p) - v
			};
			assert!(f > -0.01 && f < 0.01, "Failed -0.01 < {} < 0.01 for value {}", f, v);
		}
	}

	#[test]
	fn transmit_test() {
		let mut writer = make_writer();
		let wwvb = WWVB::new(None).unwrap();
		let mut time = TimeSpec {
			sec: 1716742645,
			nsec: 123456789
		};

		let mut buf = Vec::<f32>::with_capacity(2900000);
		unsafe {
			buf.set_len(2900000);
		}
		let buf = buf.as_mut_slice();

		let mut message = get_message(&wwvb, &mut time);
		assert_eq!(message.packed.reverse_bits(), 0x5384C121CA011160);
		let offset = message.delay as usize;
		assert_eq!(writer(&mut message, buf).0, 1674075);
		check_is_low(&buf[0..3674]);
		check_is_high(&buf[3674..42075]);
		let mut bound = 42075;
		let mut packed = 0x5384C121CA011160_u64.reverse_bits() >> 26;
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

		check_no_phase(&buf[0..10], offset);
		check_no_phase(&buf[3650..3660], offset + 3650);
		check_is_phase(&buf[3680..3690], offset + 3680, false);
		packed = 0x3B40161B56F21B60_u64.reverse_bits() >> 26;
		bound = 42080;
		for i in 26..60 {
			let bit = (packed & 1) > 0;
			if i < 59 {
				check_no_phase(&buf[bound..bound+10], offset + bound);
			}
			let b = bound + 43200;
			check_is_phase(&buf[b..b+10], offset + b, bit);
			bound += 48000;

			packed >>= 1;
		}

		message = wwvb.get_message(&mut time).unwrap();
		assert_eq!(writer(&mut message, buf).0, 2880000);
		let mut packed = 0x5404C121CA011160_u64.reverse_bits() >> 1;
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

		packed = 0x3B46C61B56F41B60_u64.reverse_bits();
		bound = 5;
		for i in 0..60 {
			let bit = (packed & 1) > 0;
			if i < 59 {
				check_no_phase(&buf[bound..bound+10], bound);
			}
			let b = bound + 43200;
			check_is_phase(&buf[b..b+10], b, bit);
			bound += 48000;

			packed >>= 1;
		}
	}

	#[test]
	fn module_doctest() {
		// Construct a WWVB object to generate messages
		let d = WWVB::new(None).unwrap();

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

		// Documentation for DST_LEAP_ENCODING
		// Wed, Jul 04 2012 17:30:18 UTC
		let time = 1341423018;
		// US western time zone
		let timezone = tz::parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();

		// Calendar date/time for current time
		let utc = Tm::new(time).expect("Time must be >= 0");

		// Start of current & next UTC days (Jul 4, 2012 00:00:00 UTC and Jul 5, 2012 00:00:00 UTC)
		let start_of_utc_day = time - utc.hour as i64 * 3600 - utc.min as i64 * 60 - utc.sec as i64;
		let next_utc_day = start_of_utc_day + 86400;  // 24 hours
		let tzinfo_1 = timezone.info(start_of_utc_day);
		let tzinfo_2 = timezone.info(next_utc_day);

		// Whether the next leap second is within the next 28 days (~ 1 month)
		let leapsecond = match nextleapsecond(time)
					 			.map(|(t, _)| t - time)
								.filter(|&t| 0 < t && t <= 2419200) // 28 days
		{
			Some(_) => 0x1,
			None    => 0x0
		};

		// DST config (0x3 => DST in effect, not changing in next 24 hours)
		let dst = ((tzinfo_2.isdst as u8) << 1) | tzinfo_1.isdst as u8;
		let dstleap = DST_LEAP_ENCODING.get((dst + leapsecond * 4) as usize)
										.copied()
										.unwrap_or(0x10);

		// Encoded DST/leap config => DST in effect, not changing in next 24 hours, no leap second this month.
		assert_eq!(dstleap, 0x03);
	}
}