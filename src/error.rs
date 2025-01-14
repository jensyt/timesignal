//! Error types used across modules.
//!
//! This module contains the error types that may be created and used within this crate. See
//! individual error types for documentation.

use std::{error, fmt};
use time::tz;

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
