//! Support for getting current time from an NTP server.
//!
//! This module provides a single public function ([`get_ntp_time`]) to request the current time
//! from an NTP server or pool of servers. It makes five requests and chooses the best response
//! to get a reasonably accurate (within ~30 ms) time signal. If the address provided resolves
//! to multiple IPs, up to five different IPs will be tried, cycling if fewer than five.
//!
//! # Examples
//!
//! ```
//! # use sntp::get_ntp_time;
//! match get_ntp_time("time.google.com") {
//! 	Ok(t) => assert!(t.sec > 0),
//! 	Err(e) => eprintln!("Error querying time.google.com: {e}")
//! }
//! assert!(get_ntp_time("invalid address").is_err());
//! ```

use std::{
	io,
	net::{Ipv4Addr, Ipv6Addr, SocketAddr, ToSocketAddrs, UdpSocket},
	ops::{Add, Div, Sub},
	slice::{from_raw_parts, from_raw_parts_mut},
	time::Duration
};
use time::{now, TimeSpec};

/// Offset to adjust a Unix timestamp (epoch Jan 1, 1970) to NTP time stamp (epoch Jan 1, 1900)
const UNIX_TO_NTP_EPOCH_ADJUST: i64 = (70 * 365 + 17) * 86400; // 17 leap years between 1900-1970

/// An NTP timestamp in seconds since Jan 1, 1900.
///
/// NTP uses a 64-bit fixed point format, with 32 bits before the decimal and 32 bits after. This
/// means the maximum granularity is 233 picoseconds. The timestamp rolls over every 136 years,
/// with the first rollover on February 7, 2036.
///
/// Internally, the value is stored in a system-endian `u64` for simpler math.
#[derive(Clone, Copy)]
struct NtpTimestamp(u64);

impl NtpTimestamp {
	/// Create a new NTP timestamp from components before and after the decimal place.
	///
	/// Note that bits in `frac` are interpreted as `2^(n-31)` where `0 <= n < 32` and `n == 0` is the
	/// least significant digit. Stated differently, the MSB in `frac` is `2^-1` and the LSB is
	/// `2^-31`.
	///
	/// # Examples
	///
	/// ```ignore
	/// assert_eq!(NtpTimestamp::new(0x12345678, 0x98765432).0, 0x1234567898765432);
	/// ```
	fn new(sec: u32, frac: u32) -> Self {
		Self((sec as u64) << 32 | frac as u64)
	}

	/// Convert the timestamp to wire format (big endian).
	///
	/// On big endian systems this is a no-op, returning the inner representation of the timestamp.
	///
	/// # Examples
	///
	/// ```ignore
	/// let wire = NtpTimestamp::new(0x12345678, 0x98765432).to_wire_format();
	/// if cfg!(target_endian = "big") {
	/// 	assert_eq!(wire, 0x1234567898765432);
	/// } else {
	/// 	assert_eq!(wire, 0x3254769878563412);
	/// }
	/// ```
	fn to_wire_format(self) -> u64 {
		u64::to_be(self.0)
	}

	/// Convert the timestamp from wire format (big endian).
	///
	/// On big endian systems this is a no-op, simply wrapping the timestamp as-is.
	///
	/// # Examples
	///
	/// ```ignore
	/// let timestamp = NtpTimestamp::from_wire_format(0x1234567898765432);
	/// if cfg!(target_endian = "big") {
	/// 	assert_eq!(timestamp.0, 0x1234567898765432);
	/// } else {
	/// 	assert_eq!(timestamp.0, 0x3254769878563412);
	/// }
	/// ```
	fn from_wire_format(v: u64) -> Self {
		Self(u64::from_be(v))
	}

	/// Convert a short timestamp from wire format (big endian).
	///
	/// Some timestamps in NTP (e.g. root delay) use a shorter 32-bit timestamp format, with 16 bits
	/// before and 16 bits after the decimal. This function parses those into a 64-bit timestamp,
	/// correctly adjusting for the difference in decimal point.
	///
	/// On big endian systems this is simply a 16-bit shift.
	///
	/// # Examples
	///
	/// ```ignore
	/// let timestamp = NtpTimestamp::from_wire_format_short(0x12345678);
	/// if cfg!(target_endian = "big") {
	/// 	assert_eq!(timestamp.0, 0x0000123456780000);
	/// } else {
	/// 	assert_eq!(timestamp.0, 0x0000785634120000);
	/// }
	/// ```
	fn from_wire_format_short(v: u32) -> Self {
		Self::from_wire_format((v as u64) << 16)
	}
}

impl Sub for NtpTimestamp {
	type Output = NtpTimestampDiff;

	/// Subtract two timestamps, generating an [`NtpTimestampDiff`].
	fn sub(self, rhs: Self) -> Self::Output {
		// Wrapping sub to enable reinterpretation of overflow as negative numbers
		NtpTimestampDiff(self.0.wrapping_sub(rhs.0) as i64)
	}
}

impl Div<u64> for NtpTimestamp {
	type Output = NtpTimestamp;

	/// Divide a timestamp by a fixed constant.
	fn div(self, rhs: u64) -> Self::Output {
		Self(self.0 / rhs)
	}
}

impl From<TimeSpec> for NtpTimestamp {
	/// Convert from a [`TimeSpec`] representing time since the Unix epoch.
	fn from(time: TimeSpec) -> Self {
		let sec = time.sec + UNIX_TO_NTP_EPOCH_ADJUST;
		let frac = (time.nsec << 32) / 1000000000;
		NtpTimestamp::new(sec as u32, frac as u32)
	}
}

/// A difference between two [`NtpTimestamp`]s.
///
/// Similar to [`NtpTimestamp`], this type uses a 64-bit fixed point format, though the value is
/// signed rather than unsigned. As with [`NtpTimestamp`], the maximum granularity is 233
/// picoseconds but the absolute value that can be represented is +-68 years. This means that the
/// maximum allowable difference for successfuly syncing between this system's time and the NTP
/// server is 68 years. Differences above that amount will result in incorrect results.
///
/// Internally, the value is stored in a system-endian `u64` for simpler math.
///
/// # Examples
///
/// ```ignore
/// let t1 = NtpTimestamp::new(0x1, 0x80000000); // 1.500s
/// let t2 = NtpTimestamp::new(0x2, 0x60000000); // 2.375s
/// let d = t2 - t1;
/// assert_eq!(d.0, 0x00000000E0000000u64 as i64); // 0.875s
/// let d = t1 - t2;
/// assert_eq!(d.0, 0xFFFFFFFF20000000u64 as i64); // -0.875s
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct NtpTimestampDiff(i64);

impl NtpTimestampDiff {
	/// Return the whole portion (aka top 32 bits) of this timestamp difference.
	///
	/// This function effectively always rounds values down, e.g. 1.2 -> 1, -1.2 -> -2. This value
	/// must be used in conjunction with [`NtpTimestampDiff::frac`].
	///
	/// # Examples
	///
	/// ```ignore
	/// let t1 = NtpTimestamp::new(0x1, 0x80000000); // 1.500s
	/// let t2 = NtpTimestamp::new(0x2, 0x60000000); // 2.375s
	/// let d = t2 - t1;           // 0.875s
	/// assert_eq!(d.sec(), 0);
	/// let d = t1 - t2;           // -0.875s
	/// assert_eq!(d.sec(), -1);
	/// ```
	fn sec(self) -> i64 {
		self.0 >> 32
	}

	/// Return the fractional portion (aka bottom 32 bits) of this timestamp difference.
	///
	/// This value is always positive, even if the difference is negative, e.g. 1.2 -> 0.2,
	/// -1.2 -> 0.8. This value must be used in conjunction with [`NtpTimestampDiff::sec`].
	///
	/// # Examples
	///
	/// ```ignore
	/// let t1 = NtpTimestamp::new(0x1, 0x80000000); // 1.500s
	/// let t2 = NtpTimestamp::new(0x2, 0x60000000); // 2.375s
	/// let d = t2 - t1;                    // 0.875
	/// assert_eq!(d.frac(), 0xE0000000);   // 0.875
	/// let d = t1 - t2;                    // -0.875
	/// assert_eq!(d.frac(), 0x20000000);   //  0.125
	/// ```
	fn frac(self) -> i64 {
		self.0 & 0xFFFFFFFF
	}

	/// Take the absolute value of `self`.
	fn abs(self) -> Self {
		Self(self.0.abs())
	}
}

impl Sub for NtpTimestampDiff {
	type Output = Self;

	/// Subtract two timestamp differences.
	fn sub(self, rhs: Self) -> Self::Output {
		// Explicit wrapping sub to avoid panic in debug mode. This should not happen during the normal
		// course of SNTP timestamp calculations, since differences tend to be small and the algorithm
		// subtracts samed-signed values which inherently can't underflow. It is possible with invalid
		// NTP packets, though in that case the result is meaningless anyway.
		Self(self.0.wrapping_sub(rhs.0))
	}
}

impl Add<NtpTimestamp> for NtpTimestampDiff {
	type Output = Self;

	/// Add a timestamp and timestamp difference.
	fn add(self, rhs: NtpTimestamp) -> Self::Output {
		// Explicit wrapping add to avoid panic in debug mode. This should not happen during the normal
		// course of SNTP timestamp calculations, since addition is only used for errors which use 32-bit
		// values that will not overflow the 64-bit internal representation.
		Self(self.0.wrapping_add(rhs.0 as i64))
	}
}

impl Div<i64> for NtpTimestampDiff {
	type Output = Self;

	/// Divide a timestamp difference by a fixed constant.
	fn div(self, rhs: i64) -> Self::Output {
		Self(self.0 / rhs)
	}
}

impl From<NtpTimestampDiff> for TimeSpec {
	/// Convert an NTP timestamp difference into a Unix timestamp difference.
	///
	/// The returned value is a difference, not an absolute time since the Unix epoch. It also also
	/// possible for the two components ([`TimeSpec::sec`], [`TimeSpec::nsec`]) to have different
	/// signs.
	///
	/// # Examples
	///
	/// ```ignore
	/// let t1 = NtpTimestamp::new(0x1, 0x80000000); // 1.500s
	/// let t2 = NtpTimestamp::new(0x2, 0x60000000); // 2.375s
	/// let d = t2 - t1;
	/// assert_eq!(TimeSpec::from(d), TimeSpec { sec: 0, nsec: 875000000 });
	/// let d = t1 - t2;
	/// assert_eq!(TimeSpec::from(d), TimeSpec { sec: -1, nsec: 125000000 });
	/// ```
	fn from(time: NtpTimestampDiff) -> Self {
		let sec = time.sec();
		let nsec = (time.frac() * 1000000000) >> 32;
		TimeSpec { sec, nsec }
	}
}

/// An NTP message between client and server.
///
/// By convention, all values stored in this type are aassumed to be in network format (big
/// endian). [`NtpMessage::new`] automatically converts timestamps from system endian to big
/// endian. Reading multi-byte values directly from this type requires calling the appropriate
/// endian conversion function (e.g. [`u64::from_be`]) on the value.
///
/// # Examples
///
/// ```ignore
/// let m = NtpMessage::new(NtpTimestamp::new(0x11223344, 0x55667788));
/// if cfg!(target_endian = "big") {
/// 	assert_eq!(m.tx_time, 0x1122334455667788);
/// } else {
/// 	assert_eq!(m.tx_time, 0x8877665544332211);
/// }
/// assert_eq!(u64::from_be(m.tx_time), 0x1122334455667788);
/// ```
#[repr(C)]
struct NtpMessage {
    /// Version number and mode. The low 3 bits represent the mode (3 for client, 4 for server).
    /// The next 3 bits represent the NTP version (typically 4). The high two bits are an alarm
    /// indicator (unused in this implementation).
    version_mode: u8,
    /// Stratum level of the local clock. 0 means unspecified or invalid, 1 means primary reference
    /// (e.g., atomic clock), 2-15 means secondary reference (via NTP). Unused in this
    /// implementation.
    _stratum: u8,
    /// Maximum interval between successive messages, in log2 seconds. Unused in this
    /// implementation.
    _poll: u8,
    /// Precision of the local clock, in log2 seconds. Unused in this implementation.
    _precision: u8,
    /// Total round-trip delay to the primary reference source, in NTP short format.
    root_delay: u32,
    /// Maximum error due to clock frequency tolerance, in NTP short format.
    root_dispersion: u32,
    /// Reference identifier (ASCII string for stratum 0 or 1, else IP address). Unused in this
    /// implementation.
    _ref_id: u32,
    /// Time when the system clock was last set or corrected, in NTP timestamp format.
    ref_time: u64,
    /// Time at which the request departed the client for the server, in NTP timestamp format.
    origin_time: u64,
    /// Time at which the request arrived at the server, in NTP timestamp format.
    rx_time: u64,
    /// Time at which the reply departed the server for the client, in NTP timestamp format.
    tx_time: u64
}

impl NtpMessage {
	/// Create a new NTP client message.
	///
	/// This function will convert the [`NtpTimestamp`] to wire format.
	fn new(time: NtpTimestamp) -> Self {
		NtpMessage {
			version_mode: 0x23, // 0x4 (version) << 3 | 0x3 (client mode)
			_stratum: 0,
			_poll: 0,
			_precision: 0,
			root_delay: 0,
			root_dispersion: 0,
			_ref_id: 0,
			ref_time: 0,
			origin_time: 0,
			rx_time: 0,
			tx_time: time.to_wire_format()
		}
	}

	/// Get a read-only view of the underlying message buffer.
	///
	/// The returned slice can be written directly to a socket and represents the full message.
	///
	/// # Examples
	///
	/// ```ignore
	/// let msg = NtpMessage::new(...);
	/// socket.send(msg.as_bytes()).unwrap();
	/// ```
	fn as_bytes(&self) -> &[u8] {
		// Safety: with repr(C) and the fields in appropriate order, NtpMessage uses a contiguous 48
		// bytes of memory with no padding. This makes it safe to create a byte slice to the underlying
		// memory.
		unsafe {
			from_raw_parts(self as *const Self as *const u8, size_of::<Self>())
		}
	}

	/// Get a mutable view of the underlying message buffer.
	///
	/// The returned slice can be read directly into from a socket and represents the full message.
	///
	/// # Examples
	///
	/// ```ignore
	/// let mut msg = NtpMessage::new(...);
	/// let bytes = socket.recv(msg.as_bytes_mut()).unwrap();
	/// if bytes != size_of::<NtpMessage>() {
	/// 	// Handle error...
	/// } else {
	/// 	// Use msg...
	/// }
	/// ```
	fn as_bytes_mut(&mut self) -> &mut [u8] {
		// Safety: with repr(C) and the fields in appropriate order, NtpMessage uses a contiguous 48
		// bytes of memory with no padding. This makes it safe to create a byte slice to the underlying
		// memory.
		unsafe {
			from_raw_parts_mut(self as *mut Self as *mut u8, size_of::<Self>())
		}
	}
}

/// An client service to query NTP servers.
///
/// Using this type enables the reuse of sockets (IPv4 and IPv6), but it is **not** thread safe. If
/// using multiple theads, create multiple `NtpService`s.
///
/// # Examples
///
/// ```ignore
/// let mut ntp = NtpService::new();
/// match ntp.query_server("time.google.com") {
/// 	Ok((t, e)) => {
/// 		// Use response
/// 	},
/// 	Err(e) => {
/// 		// Handle errors
/// 	}
/// }
/// ```
struct NtpService {
	/// IPv4 socket, initialized on first use.
	sockv4: Option<UdpSocket>,
	/// IPv6 socket, initialized on first use.
	sockv6: Option<UdpSocket>
}

impl NtpService {
	/// Construct a new `NtpService`.
	fn new() -> Self {
		Self { sockv4: None, sockv6: None }
	}

	/// Get the appropriate socket (IPv4 or IPv6) for the given address.
	///
	/// If the socket is not yet initialized, this function initializes it before returning.
	///
	/// # Errors
	///
	/// This function will return [`io::Error`] if the socket fails to initialize. For sockets already
	/// initialized, this function never returns an error.
	fn get_or_init_socket<T>(socket: &mut Option<UdpSocket>, addr: T) -> Result<&UdpSocket, io::Error>
	where (T, u16): ToSocketAddrs
	{
		if socket.is_none() {
			let s = UdpSocket::bind((addr, 0))?;
			s.set_read_timeout(Some(Duration::from_secs(1)))?;
			s.set_write_timeout(Some(Duration::from_secs(1)))?;
			*socket = Some(s);
		}
		socket.as_ref().ok_or_else(|| unreachable!("Socket should always be set"))
	}

	/// Query an NTP server.
	///
	/// On success, returns a tuple containing the time difference to be added to system time and the
	/// estimated error (+/-).
	///
	/// # Errors
	///
	/// This function will return [`io::Error`] if any error occurs during the request, including
	/// issues initializing the socket, getting the current time, and sending or receiving on the
	/// socket.
	///
	/// # Examples
	///
	/// ```ignore
	/// let mut ntp = NtpService::new();
	/// match ntp.query_server("time.google.com") {
	/// 	Ok((t, e)) => {
	/// 		// Use response
	/// 	},
	/// 	Err(e) => {
	/// 		// Handle errors
	/// 	}
	/// }
	/// ```
	fn query_server(&mut self, addr: &SocketAddr) -> Result<(NtpTimestampDiff, NtpTimestampDiff), io::Error> {
		let socket = if addr.is_ipv4() {
			Self::get_or_init_socket(&mut self.sockv4, Ipv4Addr::UNSPECIFIED)?
		} else {
			Self::get_or_init_socket(&mut self.sockv6, Ipv6Addr::UNSPECIFIED)?
		};

		socket.connect(addr)?;
		let Some(unixtime) = now() else {
			return Err(io::Error::new(io::ErrorKind::Other, "Failed to get current time"));
		};
		let mut msg = NtpMessage::new(unixtime.into());
		socket.send(msg.as_bytes())?;
		let bytes = socket.recv(msg.as_bytes_mut())?;
		if bytes != size_of::<NtpMessage>() {
			return Err(
				io::Error::new(io::ErrorKind::Other, "Invalid message returned from NTP server")
			);
		}
		let Some(unixtime) = now() else {
			return Err(io::Error::new(io::ErrorKind::Other, "Failed to get current time"));
		};
		let t1 = NtpTimestamp::from_wire_format(msg.origin_time);
		let t2 = NtpTimestamp::from_wire_format(msg.rx_time);
		let t3 = NtpTimestamp::from_wire_format(msg.tx_time);
		let t4 = NtpTimestamp::from(unixtime);

		let d =	t4 - t1 - (t3 - t2);
		let t = (t2 - t1 - (t4 - t3)) / 2;
		let e = d
			  + (NtpTimestamp::from_wire_format_short(msg.root_delay) / 2)
			  + NtpTimestamp::from_wire_format_short(msg.root_dispersion);

		Ok((t, e))
	}
}

/// Normalize an address for use by [`ToSocketAddrs::to_socket_addrs`].
///
/// This function adds a default port (123 for NTP) if none is given, and supports domain names and
/// IP addresses (IPv4 and IPv6).
///
/// # Errors
///
/// Returns [`io::Error`] if the `addr` is empty.
///
/// # Examples
///
/// ```ignore
/// assert_eq!(normalize_address("time.google.com").unwrap(), "time.google.com:123");
/// assert_eq!(normalize_address("time.google.com:321").unwrap(), "time.google.com:321");
/// assert_eq!(normalize_address("127.0.0.1").unwrap(), "127.0.0.1:123");
/// assert_eq!(normalize_address("127.0.0.1:321").unwrap(), "127.0.0.1:321");
/// assert_eq!(normalize_address("::1").unwrap(), "[::1]:123");
/// assert_eq!(normalize_address("::1:321").unwrap(), "[::1:321]:123");
/// assert_eq!(normalize_address("[::1]:321").unwrap(), "[::1]:321");
/// assert_eq!(normalize_address("[::1]").unwrap(), "[::1]:123");
/// ```
fn normalize_address(addr: &str) -> Result<String, io::Error> {
	if addr.len() == 0 {
		return Err(io::Error::new(io::ErrorKind::Other, "Empty SNTP server address"));
	}

	match addr.find(':') {
		Some(i) => {
			// Check if this is an IPv6 address by seeing if it contains another ':'
			match addr[i+1..].rfind(':') {
				Some(j) => {
					// A port can be provided after a closing brace ']' for IPv6
					match addr.rfind(']') {
						Some(k) => {
							if i + 1 + j > k {
								// IPv6, port provided
								Ok(String::from(addr))
							} else {
								// IPv6, no port provided but already wrapped in []
								Ok(format!("{}:123", addr))
							}
						}
						// IPv6, no port provided and unwrapped
						None => Ok(format!("[{}]:123", addr))
					}
				}
				// Not IPv6, port provided
				None => Ok(String::from(addr))
			}
		},
		// Not IPv6, no port provided
		None => Ok(format!("{}:123", addr))
	}
}

/// Get the current time according to an NTP server.
///
/// This function makes five requests and chooses the best response to get a reasonably accurate
/// (within ~30 ms) time signal. If the address provided resolves to multiple IPs, up to five
/// different IPs will be tried, cycling if fewer than five.
///
/// # Examples
///
/// ```ignore
/// match get_ntp_time("time.google.com") {
/// 	Ok(t) => assert!(t.sec > 0),
/// 	Err(e) => eprintln!("Error querying time.google.com: {e}")
/// }
/// assert!(get_ntp_time("invalid address").is_err());
/// ```
pub fn get_ntp_time(addr: &str) -> Result<TimeSpec, io::Error> {
	let addrs = normalize_address(addr)?.to_socket_addrs()?;
	let addrs = addrs.as_slice();
	if addrs.len() == 0 {
		return Err(io::Error::new(
					io::ErrorKind::Other,
					"Address did not resolve to any IPs"
				)
		)
	}

	let mut ntp = NtpService::new();
	let mut best: Option<(NtpTimestampDiff, NtpTimestampDiff)> = None;
	let mut it = addrs.iter().cycle();
	for i in 0..5 {
		// Unwrap will not panic because we ensured addrs.len() > 0 and made the iterator cycle.
		let addr = it.next().unwrap();
		match ntp.query_server(addr) {
			Ok((t, e)) => {
				let ea = e.abs();
				match best {
					Some((_, be)) => {
						if ea < be {
							best = Some((t, ea))
						}
					}
					None => best = Some((t, ea))
				}
			},
			Err(e) => {
				// Error out completely if not a single request succeeded
				if i == 4 && best == None {
					return Err(e)
				}
			}
		}
	}
	// Unwrap will not panic because we ensured best is not None above
	let t: TimeSpec = best.unwrap().1.into();
	let Some(unixtime) = now() else {
		return Err(io::Error::new(io::ErrorKind::Other, "Failed to get current time"));
	};

	Ok(unixtime + t)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn ntp_timestamp() {
		let t = NtpTimestamp::new(0x12345678, 0x11223344);
		assert_eq!(t.0, 0x1234567811223344);
		assert_eq!(t.to_wire_format(), 0x4433221178563412);

		let t = NtpTimestamp::from_wire_format(0x1234567811223344);
		assert_eq!(t.0, 0x4433221178563412);
	}

	#[test]
	fn ntp_timestamp_math() {
		let t1 = NtpTimestamp::new(0x12345678, 0x11223344); // 1311768465155175236
		let t2 = NtpTimestamp::new(0x09876543, 0x55555555); //  686628808066159957
		let d = t1 - t2;                                    //  625139657089015279
		assert_eq!(d.0, 0x08ACF134BBCCDDEF);
		assert_eq!(d.sec(), 0x08ACF134);
		assert_eq!(d.frac(), 0xBBCCDDEF);
		let d = d / 2;
		assert_eq!(d.0 as u64, 0x456789A5DE66EF7);
		assert_eq!(d.sec(), 0x456789A);
		assert_eq!(d.frac(), 0x5DE66EF7);

		let d = t2 - t1;                                    // -625139657089015279
		assert_eq!(d.0 as u64, 0xF7530ECB44332211);
		assert_eq!(d.sec(), -0x8ACF135);
		assert_eq!(d.frac(), 0x44332211);
		let d = d / 2;
		assert_eq!(d.0 as u64, 0xFBA98765A2199109);
		assert_eq!(d.sec(), -0x456789B);
		assert_eq!(d.frac(), 0xA2199109);
	}

	#[test]
	fn normalize_address_test() {
		assert_eq!(normalize_address("time.google.com:321").unwrap(), "time.google.com:321");
		assert_eq!(normalize_address("time.google.com").unwrap(), "time.google.com:123");
		assert_eq!(normalize_address("127.0.0.1:321").unwrap(), "127.0.0.1:321");
		assert_eq!(normalize_address("127.0.0.1").unwrap(), "127.0.0.1:123");
		assert_eq!(normalize_address("[::1]:321").unwrap(), "[::1]:321");
		assert_eq!(normalize_address("::1").unwrap(), "[::1]:123");
		assert_eq!(normalize_address("[::1]").unwrap(), "[::1]:123");
		assert_eq!(normalize_address("::1:321").unwrap(), "[::1:321]:123");
	}

	#[test]
	fn module_doctest() {
		// match get_ntp_time("time.google.com") {
		// 	Ok(t) => assert!(t.sec > 0),
		// 	Err(e) => eprintln!("Error querying time.google.com: {e}")
		// }
		assert!(get_ntp_time("invalid address").is_err());


		// Documentation for NtpTimestamp::new
		assert_eq!(NtpTimestamp::new(0x12345678, 0x98765432).0, 0x1234567898765432);

		// Documentation for NtpTimestamp::to_wire_format
		let wire = NtpTimestamp::new(0x12345678, 0x98765432).to_wire_format();
		if cfg!(target_endian = "big") {
			assert_eq!(wire, 0x1234567898765432);
		} else {
			assert_eq!(wire, 0x3254769878563412);
		}

		// Documentation for NtpTimestamp::from_wire_format_short
		let timestamp = NtpTimestamp::from_wire_format_short(0x12345678);
		if cfg!(target_endian = "big") {
			assert_eq!(timestamp.0, 0x0000123456780000);
		} else {
			assert_eq!(timestamp.0, 0x0000785634120000);
		}

		// Documentation for NtpTimestampDiff
		let t1 = NtpTimestamp::new(0x1, 0x80000000); // 1.500s
		let t2 = NtpTimestamp::new(0x2, 0x60000000); // 2.375s
		let d = t2 - t1;
		assert_eq!(d.0, 0x00000000E0000000u64 as i64); //  0.875s
		assert_eq!(d.sec(), 0);
		assert_eq!(d.frac(), 0xE0000000);
		assert_eq!(TimeSpec::from(d), TimeSpec { sec: 0, nsec: 875000000 });
		let d = t1 - t2;
		assert_eq!(d.0, 0xFFFFFFFF20000000u64 as i64); // -0.875s
		assert_eq!(d.sec(), -1);
		assert_eq!(d.frac(), 0x20000000);
		assert_eq!(TimeSpec::from(d), TimeSpec { sec: -1, nsec: 125000000 });

		// Documentation for NtpMessage
		let m = NtpMessage::new(NtpTimestamp::new(0x11223344, 0x55667788));
		if cfg!(target_endian = "big") {
			assert_eq!(m.tx_time, 0x1122334455667788);
		} else {
			assert_eq!(m.tx_time, 0x8877665544332211);
		}
		assert_eq!(u64::from_be(m.tx_time), 0x1122334455667788);
	}
}
