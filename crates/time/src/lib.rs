//! Utilities for dealing with time.
//!
//! This crate is divided into two halves: [`time`] deals with converting between Unix timestamps
//! and UTC calendar time, with no understanding of timezones; [`tz`] deals with parsing and using
//! timezones, and adds support for converting between Unix timestamps and any arbitrary timezone's
//! calendar time.
//!
//! By default, this crate supports `no_std` for both Unix <-> UTC and Unix <-> timezone
//! conversions, based on [TZ strings] or manual timezone configuration. If [`alloc`] is available
//! and the `alloc` feature is enabled, the [`tz`] module also enables parsing TZif binary data
//! ([`tz::parse_bytes`]). Additionally, if [`std`] is available and the `std` feature is enabled,
//! the [`tz`] module enables a helper function to parse TZif files directly ([`tz::parse_file`]).
//!
//! If the `now` feature is enabled, the [`time`] module enables a helper function to get the
//! current time ([`time::now`]).
//!
//! See the documentation for [`time`] and [`tz`] for more details.
//!
//! [TZ strings]: https://www.gnu.org/software/libc/manual/html_node/TZ-Variable.html
//!
//! # Examples
//!
//! Basic conversion from Unix time to UTC calendar time.
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
//!
//! Conversion from Unix time to US Eastern calendar time.
//! ```
//! # use time::{time::Tm, tz::{parse_tzstring, TzInfo, TmWithTzInfo}};
//! // Parsing a TZ string
//! let timezone = parse_tzstring(b"EST5EDT,M3.2.0,M11.1.0").unwrap();
//!
//! // Getting the date for a given unix timestamp
//! let date = timezone.date(1723433665);
//! assert_eq!(date, Some(TmWithTzInfo {
//! 	tm: Tm { sec: 25, min: 34, hour: 23, day: 11, mon: 8, year: 124, wday: 0, yday: 224 },
//! 	info: TzInfo { utoff: -14400, isdst: true }
//! }));
//! ```

#![no_std]
// only enables the `doc_cfg` feature when
// the `docsrs` configuration attribute is defined
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod time;
pub mod tz;
pub mod parse;

pub use time::*;
pub use parse::*;
