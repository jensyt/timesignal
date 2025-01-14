//! Support for parsing and using compiled timezone files (TZif files) and TZ strings.
//!
//! This module supports a subset of Olson timezone database features: UTC offsets and daylight
//! savings time changes, specified either directly in TZif binary data or via a TZ string (which
//! may be present in the compiled TZif file or supplied directly). This module supports versions
//! 1-4 of the TZif specification for this subset of features, and most extended POSIX features
//! for TZ strings.
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
//! Support for TZif files requires the `alloc` feature. TZ strings do not require any extra
//! features. The helper function [`parse_file`] requires the `std` feature.
//!
//! # Examples
//!
//! ```
//! # use time::{time::Tm, tz::{parse_tzstring, TzInfo, TmWithTzInfo}};
//! # #[cfg(feature = "std")] use time::tz::parse_file;
//! # #[cfg(feature = "std")]
//! // Parsing a file
//! let timezone1 = parse_file("/usr/share/zoneinfo/America/Los_Angeles").unwrap();
//!
//! // Parsing a TZ string
//! let timezone2 = parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
//!
//! # #[cfg(feature = "std")] {
//! // Getting info for a given unix timestamp
//! let info = timezone1.info(1723433665);
//! assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
//! # }
//!
//! // Getting the date for a given unix timestamp
//! let date = timezone2.date(1723433665);
//! assert_eq!(date, Some(TmWithTzInfo {
//! 	tm: Tm { sec: 25, min: 34, hour: 23, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
//! 	info: TzInfo { utoff: -14400, isdst: true }
//! }));
//! ```

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec::Vec};
use crate::time::Tm;

pub mod tzstring;
pub use tzstring::*;

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub mod tzfile;
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub use tzfile::*;

/// Get a given index, if valid, or return [`Default::default()`].
#[inline(always)]
fn get_or_default(bytes: &[u8], index: usize) -> u8 {
	bytes.get(index).copied().unwrap_or_default()
}

/// Timezone information at a moment in time.
///
/// This type provides the UTC offset and whether standard time or daylight savings time is in
/// effect on the associated date (which is not itself stored in this type). UTC offsets are added
/// to UTC to determine the local time. For example, New York during standard time has a UTC offset
/// of `-5 hours` (or `-18000 seconds`), so `16:00 UTC` becomes `11:00 EST`.
///
/// The default value for this type is `{ utoff: 0, isdst: false }`.
#[derive(Clone, Copy, Default, Debug, PartialEq)]
pub struct TzInfo {
	/// The UTC offset in seconds
	pub utoff: i32,
	/// Whether standard time (`false`) or daylight savings time (`true`) is in effect
	pub isdst: bool
}

/// Calendar time with associated timezone information.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TmWithTzInfo {
	/// The calendar time (in local timezone)
	pub tm: Tm,
	/// The timezone information for that time
	pub info: TzInfo
}

/// Timezone configuration.
///
/// This type allows you to convert UTC timestamps to calendar dates in the local timezone,
/// accounting for optional daylight savings time rules. It supports both fixed transition times
/// (as defined in TZif files) and computing transition times using (optional) TZ strings.
///
/// # Examples
///
/// ```
/// # use time::{time::Tm, tz::{parse_tzstring, TzInfo, TmWithTzInfo}};
/// // Parsing a TZ string
/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
///
/// // Getting info for a given unix timestamp
/// let info = timezone.info(1723433665);
/// assert_eq!(info, TzInfo { utoff: -25200, isdst: true });
///
/// // Getting the date for a given unix timestamp
/// let date = timezone.date(1723433665);
/// assert_eq!(date, Some(TmWithTzInfo {
/// 	tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
/// 	info: TzInfo { utoff: -25200, isdst: true }
/// }));
/// ```
#[derive(Debug, PartialEq)]
pub struct Timezone {
	/// Precomputed transition times and corresponding timezone info
	#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
	#[cfg(feature = "alloc")]
	times: Box<[(i64, TzInfo)]>,
	/// TZ spec for computing additional transition times
	spec: Option<TzSpec>
}

impl Timezone {
	/// Get timezone info for a given moment in time.
	///
	/// This function first checks for precomputed transition times, falling back to a TZ rule only
	/// if there are no precomputed transition times or `time` is greater than or equal to the last
	/// precomputed transition time. If `time` is before the first precomputed transition time, this
	/// function assumes the timezone matches the first precomputed transition time. This is
	/// consistent with most timezone implementations.
	///
	/// Finally, if there are no precomputed transition times and no TZ rule, this function always
	/// returns the default [`TzInfo`]: `{ utoff: 0, isdst: false }`.
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::{parse_tzstring, TzInfo};
	/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(timezone.info(1723433665), TzInfo { utoff: -25200, isdst: true });
	/// ```
	#[cfg(feature = "alloc")]
	pub fn info(&self, time: i64) -> TzInfo {
		// Check precomputed transition times
		let t = match self.times.binary_search_by_key(&time, |&(t, _)| t) {
			// Exact match, use it unless it points to the last time (which is not intended for use)
			Ok(t) => if t < self.times.len() - 1 { t } else { t + 1 },
			// Inexact match, use the previous
			Err(t) => if t < self.times.len() { t.saturating_sub(1) } else { t },
		};
		// Get the associated timezone info, or compute it if needed & possible
		self.times.get(t).map(|&(_, v)| v).unwrap_or_else(|| {
			match self.spec {
				Some(spec) => spec.info(time),
				None => TzInfo::default()
			}
		})
	}

	/// Get timezone info for a given moment in time.
	///
	/// If there is no TZ rule, this function always returns the default [`TzInfo`]:
	/// `{ utoff: 0, isdst: false }`.
	///
	/// # Examples
	///
	/// ```
	/// # use time::tz::{parse_tzstring, TzInfo};
	/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(timezone.info(1723433665), TzInfo { utoff: -25200, isdst: true });
	/// ```
	#[cfg(not(feature = "alloc"))]
	pub fn info(&self, time: i64) -> TzInfo {
		match self.spec {
			Some(spec) => spec.info(time),
			None => TzInfo::default()
		}
	}

	/// Get calendar date info for a given `time` in the specified timezone.
	///
	/// For invalid times (`time < 0`), this function returns `None`.
	///
	/// # Examples
	///
	/// ```
	/// # use time::{time::Tm, tz::{parse_tzstring, TzInfo, TmWithTzInfo}};
	/// let timezone = parse_tzstring(b"PST8PDT,M3.2.0,M11.1.0").unwrap();
	/// assert_eq!(timezone.date(1723433665), Some(TmWithTzInfo {
	/// 	tm: Tm { sec: 25, min: 34, hour: 20, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
	/// 	info: TzInfo { utoff: -25200, isdst: true }
	/// }));
	/// ```
	pub fn date(&self, time: i64) -> Option<TmWithTzInfo> {
		let info = self.info(time);

		let Some(t) = time.checked_add(info.utoff as i64) else {
			return None;
		};

		if let Some(tm) = Tm::new(t) {
			Some(TmWithTzInfo { tm, info })
		} else {
			None
		}
	}

	/// Get the set of unique UTC offsets (in seconds) in this timezone.
	///
	/// While it may seem like there can only be two offsets (standard and daylight savings time),
	/// it's possible for precomputed transition times to span over changes in DST rules. This may
	/// be rare, but do not assume there are only two possible offset values.
	#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
	#[cfg(feature = "alloc")]
	pub fn offsets(&self) -> Vec<i32> {
		let mut r: Vec<i32> = Vec::with_capacity(8);
		// Closure to append only unique values
		let mut append = |v| {
			if !r.contains(&v) {
				r.push(v);
			}
		};

		// Append precomputed transition times
		for v in self.times.iter() {
			append(v.1.utoff);
		}

		// Append optional TZ spec times
		if let Some(spec) = self.spec {
			append(spec.utoff);
			if let Some((dst, _)) = spec.dst {
				append(dst);
			}
		}

		r
	}

	/// Get the [`TzSpec`] for this timezone, if specified.
	///
	/// Note that when set, this value is technically only valid for future dates/times, and may be
	/// invalid for prior dates if timezone or DST rules have changed in the past. For example, the US
	/// changed DST rules in 2007 from `M4.1.0,M10.5.0` to `M3.2.0,M11.1.0`. If using the currently
	/// valid `TzSpec`, any transition times computed before 2007 would be incorrect.
	pub fn spec(&self) -> Option<TzSpec> {
		self.spec
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[cfg(not(feature = "alloc"))]
	#[test]
	fn timezone_info() {
		let mut tz = Timezone {
			spec: None
		};
		assert_eq!(tz.info(1704672000), TzInfo { utoff: 0, isdst: false });

		tz.spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(tz.info(1704672000), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710053999), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710054000), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613600), TzInfo { utoff: -18000, isdst: false });
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn timezone_info() {
		let mut tz = Timezone {
			times: Box::default(),
			spec: None
		};
		assert_eq!(tz.info(1704672000), TzInfo { utoff: 0, isdst: false });

		tz.spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(tz.info(1704672000), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710053999), TzInfo { utoff: -18000, isdst: false });
		assert_eq!(tz.info(1710054000), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613600), TzInfo { utoff: -18000, isdst: false });

		tz.times = Box::new([(1710054000, TzInfo { utoff: -20000, isdst: false }),
		 					 (1720054000, TzInfo { utoff: -10000, isdst: true }),
							 (1730054000, TzInfo { utoff: -5000, isdst: false })]);
		assert_eq!(tz.info(1704672000), TzInfo { utoff: -20000, isdst: false });
		assert_eq!(tz.info(1710053999), TzInfo { utoff: -20000, isdst: false });
		assert_eq!(tz.info(1720054001), TzInfo { utoff: -10000, isdst: true });
		assert_eq!(tz.info(1730613599), TzInfo { utoff: -14400, isdst: true });
		assert_eq!(tz.info(1730613600), TzInfo { utoff: -18000, isdst: false });
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn timezone_offsets() {
		let mut tz = Timezone {
			times: Box::default(),
			spec: None
		};

		assert_eq!(tz.offsets(), alloc::vec!());

		tz.spec = TzSpec::parse(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
		assert_eq!(tz.offsets(), alloc::vec![-18000, -14400]);

		tz.times = Box::new([(1710054000, TzInfo { utoff: -20000, isdst: false }),
		 					 (1720054000, TzInfo { utoff: -10000, isdst: true }),
							 (1730054000, TzInfo { utoff: -20000, isdst: false }),
							 (1740054000, TzInfo { utoff: -10000, isdst: true }),
							 (1750054000, TzInfo { utoff: -5000, isdst: false })]);
		assert_eq!(tz.offsets(), alloc::vec![-20000, -10000, -5000, -18000, -14400]);
	}
}
