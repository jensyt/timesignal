//! Utilities for dealing with time (UTC and Unix timestamps), unaware of timezone.
//!
//! This module provides utilities to get the current Unix time with nanosecond granularity
//! and various calendar utilities to convert to/from Unix time. Since the calendar functions
//! do not rely on libc's mktime and gmtime functions, they are completely thread safe.
//!
//! # Examples
//!
//! ```
//! # use time::time::Tm;
//! let date = Tm::new(1718617807).unwrap();
//!	assert_eq!(date, Tm {
//!		sec: 7,
//!		min: 50,
//!		hour: 9,
//!		day: 17,
//!		mon: 6,
//!		year: 124,
//!		wday: 1,
//!		yday: 169
//!	});
//! ```

use core::ops::{Add, AddAssign};
#[cfg(feature = "now")]
use core::mem::MaybeUninit;
#[cfg(feature = "now")]
use libc::{timespec, clock_gettime, CLOCK_REALTIME};

/// A list of all leap seconds currently set and approved by IERS.
///
/// This list contains the timestamp at which the leap second occurs, and the number of cumulative
/// leap seconds in effect at that timestamp. Note that the leap second technically occurs in the
/// second **before** the value here. See [Wikipedia] for more details.
///
/// [Wikipedia]: https://en.wikipedia.org/wiki/Leap_second
const LEAPSECONDS: [(i64, u8); 28] = [(63072000,   10), (78796800,   11), (94694400,   12), (126230400,  13),
									  (157766400,  14), (189302400,  15), (220924800,  16), (252460800,  17),
									  (283996800,  18), (315532800,  19), (362793600,  20), (394329600,  21),
									  (425865600,  22), (489024000,  23), (567993600,  24), (631152000,  25),
									  (662688000,  26), (709948800,  27), (741484800,  28), (773020800,  29),
									  (820454400,  30), (867715200,  31), (915148800,  32), (1136073600, 33),
									  (1230768000, 34), (1341100800, 35), (1435708800, 36), (1483228800, 37)];

/// Get the next leap second after `time`.
///
/// For times after `1483228800`, this function returns `None`. Otherwise, it returns the leap
/// second equal to or greater than `time`.
///
/// # Examples
///
/// ```
/// # use time::time::nextleapsecond;
/// assert_eq!(nextleapsecond(525323527), Some((567993600,  24)));
/// ```
pub fn nextleapsecond(time: i64) -> Option<(i64, u8)> {
	let mut last = None;
	for t in LEAPSECONDS.iter().rev() {
		if t.0 < time { break }
		last = Some(*t);
	}
	last
}

/// Helper type to support math on [`TimeSpec`]s. Represents seconds.
///
/// # Examples
///
/// ```
/// # use time::time::{Seconds, TimeSpec};
/// // Jan 1, 2025. 12:00:00.123456789 UTC.
/// let c = TimeSpec { sec: 1735732800, nsec: 123456789 };
/// assert_eq!(c + Seconds(10), TimeSpec { sec: c.sec + 10, nsec: c.nsec });
/// ```
#[repr(transparent)]
pub struct Seconds(pub i64);

/// Helper type to support math on [`TimeSpec`]s. Represents nanoseconds.
///
/// Adding nanoseconds to a [`TimeSpec`] will roll over seconds if needed, see the examples.
///
/// # Examples
///
/// ```
/// # use time::time::{Nanoseconds, TimeSpec};
/// // Jan 1, 2025. 12:00:00.123456789 UTC.
/// let mut c = TimeSpec { sec: 1735732800, nsec: 123456789 };
/// assert_eq!(c + Nanoseconds(10), TimeSpec { sec: c.sec, nsec: 123456799});
/// c.nsec = 999999999;
/// assert_eq!(c + Nanoseconds(10), TimeSpec { sec: c.sec + 1, nsec: 9});
/// ```
#[repr(transparent)]
pub struct Nanoseconds(pub i64);

/// Unix time with nanosecond granularity.
///
/// Supports simple addition / addition-assignment with [`Seconds`] and [`Nanoseconds`].
/// Subtraction is supported by adding negative values.
///
/// # Examples
///
/// ```
/// # use time::time::{Seconds, Nanoseconds, TimeSpec};
/// // Jan 1, 2025. 12:00:00.999999999 UTC.
/// let mut c = TimeSpec { sec: 1735732800, nsec: 999999999 };
/// assert_eq!(c + Seconds(10) + Nanoseconds(10), TimeSpec { sec: c.sec + 11, nsec: 9});
/// ```
///
/// Subtracting by adding a negative value:
/// ```
/// # use time::time::{Seconds, Nanoseconds, TimeSpec};
/// # let mut c = TimeSpec { sec: 1735732800, nsec: 999999999 };
/// assert_eq!(c + Seconds(-10), TimeSpec { sec: c.sec - 10, nsec: 999999999 });
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TimeSpec {
	/// Seconds since the Unix epoch
	pub sec: i64,
	/// Nanoseconds since the beginning of `sec`, ranging [0-999999999]
	pub nsec: i64
}

#[cfg_attr(docsrs, doc(cfg(feature = "now")))]
#[cfg(feature = "now")]
impl From<timespec> for TimeSpec {
	/// Convert from `libc::timespec` to [`TimeSpec`] for better math ergonomics
	fn from(value: timespec) -> Self {
		TimeSpec {
			sec: value.tv_sec,
			nsec: value.tv_nsec
		}
	}
}

impl Add<Seconds> for TimeSpec {
	type Output = Self;

	/// Add `rhs` seconds to `self`.
	fn add(mut self, rhs: Seconds) -> Self::Output {
		self.sec += rhs.0;
		self
	}
}

impl AddAssign<Seconds> for TimeSpec {
	/// Add `rhs` seconds to `self`.
	fn add_assign(&mut self, rhs: Seconds) {
		*self = *self + rhs;
	}
}

impl Add<Nanoseconds> for TimeSpec {
	type Output = Self;

	/// Add `rhs` nanoseconds to `self`, rolling over seconds as needed to ensure `nsec` stays in
	/// the range of [0-999999999].
	fn add(mut self, rhs: Nanoseconds) -> Self::Output {
		self.nsec += rhs.0;
		let sec = self.nsec / 1000000000;
		self.sec += sec;
		self.nsec %= 1000000000;
		if self.nsec < 0 {
			self.nsec += 1000000000;
		}
		self
	}
}

impl AddAssign<Nanoseconds> for TimeSpec {
	/// Add `rhs` nanoseconds to `self`, rolling over seconds as needed to ensure `nsec` stays in
	/// the range of [0-999999999].
	fn add_assign(&mut self, rhs: Nanoseconds) {
		*self = *self + rhs;
	}
}

impl Add for TimeSpec {
	type Output = Self;

	/// Add `rhs` to `self`, rolling over seconds as needed to ensure `nsec` stays in the range of
	/// [0-999999999].
	fn add(self, rhs: TimeSpec) -> Self::Output {
		self + Seconds(rhs.sec) + Nanoseconds(rhs.nsec)
	}
}

/// Get the current time as a Unix timestamp with nanosecond granularity.
///
/// This function will return `None` if `libc::clock_gettime` fails.
///
/// This function is thread safe.
///
/// # Examples
///
/// ```
/// # use time::time::now;
/// let c = now().expect("Failed to get current time");
/// assert!(c.sec > 0);
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "now")))]
#[cfg(feature = "now")]
pub fn now() -> Option<TimeSpec> {
	let mut time = MaybeUninit::<timespec>::uninit();
	// Safety:
	// - clock_gettime does not read time, only writes
	// - if clock_gettime returns zero, time is successfully initialized
	unsafe {
		match clock_gettime(CLOCK_REALTIME, time.as_mut_ptr()) {
			0 => Some(time.assume_init().into()),
			_ => None
		}
	}
}

/// Check whether a given `year` is a leap year.
///
/// Year must be the absolute Gregorian calendar year (i.e. 2024), not the abbreviated format year
/// as in [`Tm::year`][Tm#structfield.year] (i.e. 124). Note: the function [`Tm::year()`] converts
/// the abbreviated year to absolute Gregorian calendar year and can be used, but in that case you
/// can also use [`Tm::isleapyear()`].
///
/// # Examples
///
/// ```
/// # use time::time::isleapyear;
/// assert_eq!(isleapyear(1900), false);
/// assert_eq!(isleapyear(2000), true);
/// assert_eq!(isleapyear(2020), true);
/// assert_eq!(isleapyear(2023), false);
/// assert_eq!(isleapyear(2024), true);
/// ```
#[inline(always)]
pub fn isleapyear(year: u16) -> bool {
	let l = if year%100 != 0 { 3 } else { 15 };
	(year & l) == 0
}

/// Seconds per minute.
const SECONDS_PER_MINUTE: i64 = 60;
/// Seconds per hour.
const SECONDS_PER_HOUR: i64 = SECONDS_PER_MINUTE * 60;
/// Seconds per day.
const SECONDS_PER_DAY: i64 = SECONDS_PER_HOUR * 24;
/// Days per non-leap year.
const DAYS_PER_NON_LEAP_YEAR: i64 = 365;
/// Days per leap year.
const DAYS_PER_LEAP_YEAR: i64 = DAYS_PER_NON_LEAP_YEAR + 1;
/// Leap years occur every 4 years...
const YEARS_PER_LEAP_YEAR_1: i64 = 4;
/// ... except every 100, unless it's the end of the era.
const YEARS_PER_LEAP_YEAR_2: i64 = 100;
/// Number of years per era.
const YEARS_PER_ERA: i64 = 400;
/// Number of days every 4 years.
const DAYS_PER_LEAP_YEAR_1: i64 = YEARS_PER_LEAP_YEAR_1 * DAYS_PER_NON_LEAP_YEAR;
/// Number of days every 100 years.
const DAYS_PER_LEAP_YEAR_2: i64 = YEARS_PER_LEAP_YEAR_2 * DAYS_PER_NON_LEAP_YEAR
                                + YEARS_PER_LEAP_YEAR_2 / YEARS_PER_LEAP_YEAR_1 - 1;
/// Number of days every era (400 years), excluding the last leap day.
const DAYS_PER_LEAP_YEAR_3: i64 = YEARS_PER_ERA * DAYS_PER_NON_LEAP_YEAR
                                + (YEARS_PER_ERA / YEARS_PER_LEAP_YEAR_2)
                                * (YEARS_PER_LEAP_YEAR_2 / YEARS_PER_LEAP_YEAR_1 - 1);
/// Number of days per "standard" century, i.e. not the first year of an era
const DAYS_PER_CENTURY: i64 = YEARS_PER_LEAP_YEAR_2 * DAYS_PER_NON_LEAP_YEAR
							+ (YEARS_PER_LEAP_YEAR_2 / YEARS_PER_LEAP_YEAR_1 - 1);
/// Number of days every era (400 years).
const DAYS_PER_ERA: i64 = DAYS_PER_LEAP_YEAR_3 + 1;
/// Days from January 1 to February 28, inclusive.
const DAYS_FROM_JAN_TO_FEB: i64 = 31 + 28;
/// Days from March 1 to December 31, inclusive.
const DAYS_FROM_MAR_TO_DEC: i64 = DAYS_PER_NON_LEAP_YEAR - DAYS_FROM_JAN_TO_FEB;
/// Days per week.
const DAYS_PER_WEEK: i64 = 7;
/// Days from March 1, 0000 to January 1, 1970.
const DAYS_FROM_JAN_1970_TO_MARCH_0000: i64 = (1970 / YEARS_PER_ERA) * DAYS_PER_ERA
                                            + (1970 % YEARS_PER_ERA) * DAYS_PER_NON_LEAP_YEAR
                                            + (1970 % YEARS_PER_ERA) / YEARS_PER_LEAP_YEAR_1
                                            - (1970 % YEARS_PER_ERA) / YEARS_PER_LEAP_YEAR_2
                                            - DAYS_FROM_JAN_TO_FEB;
/// Years to add to [`Tm::year`][Tm#structfield.year] to get absolute Gregorian calendar year.
pub const YEAR_ADJUST: i64 = 1900;

/// Gregorian calendar date, equivalent to [`libc::tm`] with some small incompatibilities.
///
/// Key differences:
/// - `mon` is [0, 11] in [`libc::tm`] but [1, 12] in [`Tm`].
/// - `yday` is [0, 365] in [`libc::tm`] but [1, 366] in [`Tm`].
///
/// # Examples
///
/// ```
/// # use time::time::Tm;
/// let date = Tm::new(1718617807).unwrap();
/// assert_eq!(date, Tm {
/// 	sec: 7,
/// 	min: 50,
/// 	hour: 9,
/// 	day: 17,
/// 	mon: 6,
/// 	year: 124,
/// 	wday: 1,
/// 	yday: 169
/// });
/// ```
#[derive(Clone, Copy)]
#[derive(Debug, PartialEq)]
pub struct Tm {
	/// Seconds, ranged [0, 59]
	pub sec: u8,
	/// Minutes, ranged [0, 59]
	pub min: u8,
	/// Hours, ranged [0, 23]
	pub hour: u8,
	/// Day of the month, ranged [1, 31]
	pub day: u8,
	/// Month of the year, ranged [1, 12]
	pub mon: u8,
	/// Years since 1900, ranged [0, 255] => [1900, 2155]
	pub year: u8,
	/// Day of the week, ranged [0, 6] => [Sunday, Saturday]
	pub wday: u8,
	/// Day of the year, ranged [1, 366]
	pub yday: u16
}

impl Tm {
	/// Convert a Unix timestamp into a calendar date.
	///
	/// This function only supports timestamps on or after the Unix epoch (Jan 1, 1970), i.e.
	/// `unixtimestamp >= 0`. Negative inputs result in `None`.
	pub fn new(unixtimestamp: i64) -> Option<Tm> {
		// The short explanation of this algorithm is that the Gregorian calendar repeats every 400
		// years, with internal repetition every 100 years and again every 4 years (this is how leap
		// years work). Since leap days get added at the end of February if it's a leap year, we rotate
		// the calendar to be Mar-Feb instead of Jan-Dec, which puts the leap day as the last day of the
		// rotated year. With this rotation and working in 400-year chunks, it's fairly straightforward
		// to convert a timestamp to a given date. Finally, you need to "un-rotate" the year back to the
		// real Jan-Dec year. The advantage of this algorithm is that it's branchless on modern CPUs.
		//
		// More details at the links below:
		// http://howardhinnant.github.io/date_algorithms.html#civil_from_days
		// https://github.com/lattera/glibc/blob/master/time/offtime.c#L29
		if unixtimestamp < 0 { return None }
		let days = unixtimestamp / SECONDS_PER_DAY;
		let rem = unixtimestamp % SECONDS_PER_DAY;
		let hr = rem / SECONDS_PER_HOUR;
		let remrem = rem % SECONDS_PER_HOUR;
		let z = days + DAYS_FROM_JAN_1970_TO_MARCH_0000;
		let era = z / DAYS_PER_ERA;
		let doe = z % DAYS_PER_ERA;
		let yoe = (doe
			       - doe / DAYS_PER_LEAP_YEAR_1
			       + doe / DAYS_PER_LEAP_YEAR_2
			       - doe / DAYS_PER_LEAP_YEAR_3
			      ) / DAYS_PER_NON_LEAP_YEAR;
		let y = yoe + era * YEARS_PER_ERA - YEAR_ADJUST;
		let leap = yoe / YEARS_PER_LEAP_YEAR_1 - yoe / YEARS_PER_LEAP_YEAR_2;
		let pyoe = if yoe == 0 { -4 } else { yoe-1 };
		let leapadj = leap - pyoe / YEARS_PER_LEAP_YEAR_1 + pyoe / YEARS_PER_LEAP_YEAR_2;
		let doy = doe - (DAYS_PER_NON_LEAP_YEAR * yoe + leap);
		// Linear equation that calculates the month from a set day of year
		let mp = (5 * doy + 2) / 153;
		// Linear equation that calculates the day of month from a day of year and month number
		let d = doy - (153 * mp + 2) / 5 + 1;
		// Convert from Mar-Feb year to Jan-Dec year
		let rotate = |l, r| if mp < 10 { l } else { r };
		let m = rotate(mp + 3, mp - 9);
		let y = rotate(y, y + 1);
		let yadj = rotate(0, if leapadj == 0 { DAYS_PER_NON_LEAP_YEAR } else { DAYS_PER_LEAP_YEAR });

		Some(Tm {
			sec: (remrem % SECONDS_PER_MINUTE) as u8,
			min: (remrem / SECONDS_PER_MINUTE) as u8,
			hour: hr as u8,
			day: d as u8,
			mon: m as u8,
			year: y as u8,
			wday: ((days + 4) % DAYS_PER_WEEK) as u8, // Jan 1, 1970 was a Thursday
			yday: (doy + leapadj + DAYS_FROM_JAN_TO_FEB - yadj + 1) as u16
		})
	}

	/// Get the absolute Gregorian calendar year.
	#[inline(always)]
	pub fn year(&self) -> u16 {
		self.year as u16 + YEAR_ADJUST as u16
	}

	/// Check whether `self` is a leap year.
	#[inline(always)]
	pub fn isleapyear(&self) -> bool {
		isleapyear(self.year())
	}
}

/// Get the Unix timestamp for 00:00:00 UTC on a given year and day of year.
///
/// `y` must be the absolute Gregorian calendar year, and `doy` the zero-indexed day of year
/// starting at January 1. If `leap == true`, then `doy = 59` means February 29, otherwise it means
/// March 1.
///
/// # Examples
///
/// ```
/// # use time::time::timestamp_from_yd;
/// assert_eq!(timestamp_from_yd(2024, 58, true), 1709078400);  // Feb 28, 2024
/// assert_eq!(timestamp_from_yd(2024, 59, true), 1709164800);  // Feb 29, 2024
/// assert_eq!(timestamp_from_yd(2024, 60, true), 1709251200);  // Mar  1, 2024
/// assert_eq!(timestamp_from_yd(2024, 58, false), 1709078400); // Feb 28, 2024
/// assert_eq!(timestamp_from_yd(2024, 59, false), 1709251200); // Mar  1, 2024
/// ```
pub fn timestamp_from_yd(y: u16, doy: u16, leap: bool) -> i64 {
	// Similar to Tm::new, this algorithm rotates the year to Mar-Feb and takes advantage of the
	// 400 year cycle in the Gregorian calendar.
	//
	// More details:
	// http://howardhinnant.github.io/date_algorithms.html#days_from_civil
	let y = y as i64;
	let doy = doy as i64;
	let cmp = if leap { DAYS_FROM_JAN_TO_FEB + 1 } else { DAYS_FROM_JAN_TO_FEB };
	let (y, doy) = if doy < cmp {
		(y - 1, doy + DAYS_FROM_MAR_TO_DEC)
	} else {
		(y, doy - cmp)
	};
	let era = y / YEARS_PER_ERA;
	let yoe = y - era * YEARS_PER_ERA;
	let doe = yoe * DAYS_PER_NON_LEAP_YEAR
			+ yoe / YEARS_PER_LEAP_YEAR_1
			- yoe / YEARS_PER_LEAP_YEAR_2
			+ doy;
	SECONDS_PER_DAY * (era * DAYS_PER_ERA + doe - DAYS_FROM_JAN_1970_TO_MARCH_0000)
}

/// Get the Unix timestamp for 00:00:00 UTC on a given year, month, and day.
///
/// `y` must be the absolute Gregorian calendar year, `m` the 1-indexed month starting at January,
/// and `d` the day of the month.
///
/// # Examples
///
/// ```
/// # use time::time::timestamp_from_ymd;
/// assert_eq!(timestamp_from_ymd(2024, 2, 28), 1709078400);
/// assert_eq!(timestamp_from_ymd(2024, 2, 29), 1709164800);
/// assert_eq!(timestamp_from_ymd(2024, 3, 1), 1709251200);
/// ```
pub fn timestamp_from_ymd(y: u16, m: u8, d: u8) -> i64 {
	// Algorithm is similar to timestamp_from_yd, more details:
	// http://howardhinnant.github.io/date_algorithms.html#days_from_civil
	let y = if m < 3 { y as i64 - 1 } else { y as i64 };
	let era = y / YEARS_PER_ERA;
	let yoe = y - era * YEARS_PER_ERA;
	let m2 = if m > 2 { m as i64 - 3 } else { m as i64 + 9 };
	let doy = (153 * m2 + 2) / 5 + d as i64 - 1;
	let doe = yoe * DAYS_PER_NON_LEAP_YEAR
			+ yoe / YEARS_PER_LEAP_YEAR_1
			- yoe / YEARS_PER_LEAP_YEAR_2
			+ doy;
	SECONDS_PER_DAY * (era * DAYS_PER_ERA + doe - DAYS_FROM_JAN_1970_TO_MARCH_0000)
}

/// Get the weekday (0-6 => Sunday-Saturday) for a given year, month, and day.
///
/// `y` must be the absolute Gregorian calendar year, `m` the 1-indexed month starting at January,
/// and `d` the day of the month.
///
/// # Examples
///
/// ```
/// # use time::time::wday_from_ymd;
/// assert_eq!(wday_from_ymd(2024, 1, 1), 1);   // Monday
/// assert_eq!(wday_from_ymd(2024, 2, 28), 3);  // Wednesday
/// assert_eq!(wday_from_ymd(2024, 2, 29), 4);  // Thursday
/// assert_eq!(wday_from_ymd(2024, 3, 1), 5);   // Friday
/// assert_eq!(wday_from_ymd(2024, 10, 27), 0); // Sunday
/// ```
pub fn wday_from_ymd(y: u16, m: u8, d: u8) -> u8 {
	// Algorithm is similar to timestamp_from_yd, with some minor differences, e.g. the linear
	// equation for calculating the number of days prior to month m uses the Jan-Dec year instead
	// of the Mar-Feb year.
	//
	// More details: https://arxiv.org/pdf/2102.06959
	let factor = if m < 3 {
		3 * m.wrapping_sub(1) as i64
	} else {
		(153 * m as i64 - 447) / 5
	};
	let y = if m < 3 { y.wrapping_sub(1) as i64 } else { y as i64 };
	((
		y
		+ y / YEARS_PER_LEAP_YEAR_1
		- y / YEARS_PER_LEAP_YEAR_2
		+ y / YEARS_PER_ERA
		+ factor
		+ d as i64
	) % 7) as u8
}

/// The number of days in a given month.
///
/// `y` must be the absolute Gregorian calendar year, and `m` the 1-indexed month starting at
/// January.
pub fn days_per_month(y: u16, m: u8) -> u8 {
	// Details: https://www.youtube.com/watch?v=J9KijLyP-yg&t=1470s
	if m == 2 {
		if isleapyear(y) { 29 } else { 28 }
	} else {
		30 | (m ^ (m >> 3))
	}
}

/// Get the absolute Gregorian calendar year from a given Unix timestamp.
pub fn y_from_timestamp(unixtimestamp: i64) -> u16 {
	// Algorithm works the same as Tm::new
	let days = unixtimestamp / SECONDS_PER_DAY;
	let z = days + DAYS_FROM_JAN_1970_TO_MARCH_0000;
	let era = z / DAYS_PER_ERA;
	let doe = z % DAYS_PER_ERA;
	let yoe = (doe
		       - doe / DAYS_PER_LEAP_YEAR_1
		       + doe / DAYS_PER_LEAP_YEAR_2
		       - doe / DAYS_PER_LEAP_YEAR_3
		      ) / DAYS_PER_NON_LEAP_YEAR;
	let y = yoe + era * YEARS_PER_ERA;
	let leap = yoe / YEARS_PER_LEAP_YEAR_1 - yoe / YEARS_PER_LEAP_YEAR_2;
	let doy = doe - (DAYS_PER_NON_LEAP_YEAR * yoe + leap);
	if doy >= DAYS_FROM_MAR_TO_DEC { (y + 1) as u16 } else { y as u16 }
}

/// Get the minute of the era for a given Unix timestamp.
pub fn minute_of_century_from_timestamp(unixtimestamp: i64) -> u32 {
	// Algorithm works the same as Tm::new
	let days = unixtimestamp / SECONDS_PER_DAY;
	let rem = unixtimestamp % SECONDS_PER_DAY;
	let z = days + DAYS_FROM_JAN_1970_TO_MARCH_0000;
	let doe = z % DAYS_PER_ERA;
	let doc = doe % DAYS_PER_CENTURY;

	// Convert from Mar-Feb year to Jan-Dec year. Three cases:
	// 1. Everything except last January/February of the century:
	//   a. If first century of the era, add 60 days (leap year)
	//   b. Every other century of the era, add 59 days (non-leap year)
	// 2. Last January/February of the century: wrap to the next century
	let doc_adj = if doc < DAYS_PER_CENTURY - DAYS_FROM_JAN_TO_FEB {
		let first_century = (doe < DAYS_PER_CENTURY) as i64;
		doc + DAYS_FROM_JAN_TO_FEB + first_century
	} else {
		doc - DAYS_PER_CENTURY + DAYS_FROM_JAN_TO_FEB
	};

	// Conversion to u32 is safe because the max value is 52596000
	(doc_adj * (SECONDS_PER_DAY / SECONDS_PER_MINUTE) + rem / SECONDS_PER_MINUTE) as u32
}

#[cfg(test)]
mod tests {
	use super::*;
	use core::mem::MaybeUninit;
	use libc::{time_t, tm};

	// Get the libc version of UTC calendar time
	fn utc_time(time: time_t) -> tm {
		unsafe {
			let mut utc = MaybeUninit::<tm>::uninit();
			libc::gmtime_r(&time, utc.as_mut_ptr());
			utc.assume_init()
		}
	}

	fn compare_dates(time: i64) {
		let d1 = utc_time(time);
		let d2 = Tm::new(time).unwrap();
		assert_eq!(d1.tm_sec, d2.sec as i32, "time: {}, sec: {} vs. {}", time, d1.tm_sec, d2.sec);
		assert_eq!(d1.tm_min, d2.min as i32, "time: {}, min: {} vs. {}", time, d1.tm_min, d2.min);
		assert_eq!(d1.tm_hour, d2.hour as i32, "time: {}, hour: {} vs. {}", time, d1.tm_hour, d2.hour);
		assert_eq!(d1.tm_mday, d2.day as i32, "time: {}, mday: {} vs. {}", time, d1.tm_mday, d2.day);
		assert_eq!(d1.tm_mon + 1, d2.mon as i32, "time: {}, mon: {} vs. {}", time, d1.tm_mon + 1, d2.mon);
		assert_eq!(d1.tm_year, d2.year as i32, "time: {}, year: {} vs. {}", time, d1.tm_year, d2.year as i32);
		assert_eq!(d1.tm_wday, d2.wday as i32, "time: {}, wday: {} vs. {}", time, d1.tm_wday, d2.wday);
		assert_eq!(d1.tm_yday + 1, d2.yday as i32, "time: {}, yday: {} vs. {}", time, d1.tm_yday + 1, d2.yday);
	}

	#[test]
	fn date_test() {
		assert!(Tm::new(-94694400).is_none());
		compare_dates(5097600);
		compare_dates(17185926);
		compare_dates(31449600);
		compare_dates(94694400);
		compare_dates(1718617807);
		compare_dates(1655459407);
		compare_dates(1844848207);
		compare_dates(961235407);
		compare_dates(929613007);

		// Make sure extreme inputs cannot panic
		Tm::new(i64::MAX);
		Tm::new(i64::MIN);
	}

	#[test]
	fn isleapyear_test() {
		assert_eq!(isleapyear(1900), false);
		assert_eq!(isleapyear(2000), true);
		assert_eq!(isleapyear(2020), true);
		assert_eq!(isleapyear(2023), false);
		assert_eq!(isleapyear(2024), true);

		// Make sur extreme inputs cannot panic
		isleapyear(0);
		isleapyear(u16::MAX);
	}

	#[test]
	fn timestamp_from_yd_test() {
		assert_eq!(timestamp_from_yd(2024, 0, true), 1704067200);
		assert_eq!(timestamp_from_yd(2024, 0, false), 1704067200);
		assert_eq!(timestamp_from_yd(2024, 58, true), 1709078400);
		assert_eq!(timestamp_from_yd(2024, 59, true), 1709164800);
		assert_eq!(timestamp_from_yd(2024, 60, true), 1709251200);
		assert_eq!(timestamp_from_yd(2024, 58, false), 1709078400);
		assert_eq!(timestamp_from_yd(2024, 59, false), 1709251200);
		assert_eq!(timestamp_from_yd(2024, 300, true), 1729987200);
		assert_eq!(timestamp_from_yd(2024, 300, false), 1730073600);

		// Make sure extreme inputs cannot panic
		timestamp_from_yd(0, 0, false);
		timestamp_from_yd(u16::MAX, u16::MAX, false);
		timestamp_from_yd(0, 0, true);
		timestamp_from_yd(u16::MAX, u16::MAX, true);
	}

	#[test]
	fn timestamp_from_ymd_test() {
		assert_eq!(timestamp_from_ymd(2024, 1, 1), 1704067200);
		assert_eq!(timestamp_from_ymd(2024, 2, 28), 1709078400);
		assert_eq!(timestamp_from_ymd(2024, 2, 29), 1709164800);
		assert_eq!(timestamp_from_ymd(2024, 3, 1), 1709251200);
		assert_eq!(timestamp_from_ymd(2024, 10, 27), 1729987200);

		// Make sure extreme inputs cannot panic
		timestamp_from_ymd(0, 0, 0);
		timestamp_from_ymd(u16::MAX, u8::MAX, u8::MAX);
	}

	#[test]
	fn wday_from_ymd_test() {
		assert_eq!(wday_from_ymd(2024, 1, 1), 1);
		assert_eq!(wday_from_ymd(2024, 2, 28), 3);
		assert_eq!(wday_from_ymd(2024, 2, 29), 4);
		assert_eq!(wday_from_ymd(2024, 3, 1), 5);
		assert_eq!(wday_from_ymd(2024, 10, 27), 0);

		// Make sure extreme inputs cannot panic
		let x = wday_from_ymd(0, 0, 0);
		assert!(x < 7);
		let x = wday_from_ymd(u16::MAX, u8::MAX, u8::MAX);
		assert!(x < 7);
	}

	#[test]
	fn days_per_month_test() {
		assert_eq!(days_per_month(2024, 1), 31);
		assert_eq!(days_per_month(2024, 2), 29);
		assert_eq!(days_per_month(2023, 2), 28);
		assert_eq!(days_per_month(2024, 3), 31);
		assert_eq!(days_per_month(2024, 4), 30);
		assert_eq!(days_per_month(2024, 5), 31);
		assert_eq!(days_per_month(2024, 6), 30);
		assert_eq!(days_per_month(2024, 7), 31);
		assert_eq!(days_per_month(2024, 8), 31);
		assert_eq!(days_per_month(2024, 9), 30);
		assert_eq!(days_per_month(2024, 10), 31);
		assert_eq!(days_per_month(2024, 11), 30);
		assert_eq!(days_per_month(2024, 12), 31);

		// Make sure extreme inputs cannot panic
		days_per_month(0, 0);
		days_per_month(u16::MAX, u8::MAX);
	}

	#[test]
	fn y_from_timestamp_test() {
		assert_eq!(y_from_timestamp(1704067199), 2023);
		assert_eq!(y_from_timestamp(1704067200), 2024);
		assert_eq!(y_from_timestamp(1709164800), 2024);
		assert_eq!(y_from_timestamp(1709251199), 2024);
		assert_eq!(y_from_timestamp(1709251200), 2024);
		assert_eq!(y_from_timestamp(1729987200), 2024);

		// Make sure extreme inputs cannot panic
		y_from_timestamp(i64::MIN);
		y_from_timestamp(i64::MAX);
	}

	#[test]
	fn minute_of_century_from_timestamp_test() {
		assert_eq!(minute_of_century_from_timestamp(946684740), 52594559);
		assert_eq!(minute_of_century_from_timestamp(946684800), 0);
		assert_eq!(minute_of_century_from_timestamp(1469741399), 8717609);

		// Make sure extreme inputs cannot panic
		minute_of_century_from_timestamp(i64::MIN);
		minute_of_century_from_timestamp(i64::MAX);
	}

	// #[bench]
	// fn date_bench(b: &mut test::Bencher) {
	// 	let mut i = 1655459407;
	// 	b.iter(|| { i += 1; date(i).unwrap() })
	// }

	// #[bench]
	// fn libc_bench(b: &mut test::Bencher) {
	// 	let mut i = 1655459407;
	// 	b.iter(|| { i += 1; utc_time(i) })
	// }
}
