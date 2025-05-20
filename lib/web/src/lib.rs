//! WebAssembly support for generating time signals.
//!
//! This crate exposes a very simple API for generating time signals from WASM host languages. It
//! supports generating time signals for arbitrary times and timezones specified as TZ strings, but
//! does not support reading or parsing TZif files.
//!
//! It manages memory allocation and deallocation, though memory leaks may occur if successful
//! calls to [`make_writer`] are not balanced by calls to [`destroy_writer`].
//!
//! This crate makes liberal use of `unsafe`. Some of this is inevitable since crossing the
//! language boundary to the WASM host language requires passing pointers where the host must
//! maintain invariants. This crate makes every attempt to test and minimize possible defects
//! caused by the internal use of `unsafe`, but can make no guarantees about calling code.
//!
//! While this crate compiles for non-WASM targets, it is only really intended for WASM targets.
//! Build with `cargo build -r -p web --target wasm32-unknown-unknown`.
//!
//! # Examples
//! ```
//! let mut stack_as_u8: [u8; CUSTOM_STACK_SIZE] = [0; CUSTOM_STACK_SIZE];
//! unsafe {
//!		let mut stack_as_f32 = transmute::<_, [f32; CUSTOM_STACK_SIZE / 4]>(stack_as_u8);
//!
//!		let writer = make_writer(SIGNAL_WWVB, 1716742680000, stack_as_u8.as_mut_ptr(), 0);
//!		assert_ne!(writer, 0);
//!
//!		let w = writer as *mut Writer;
//!		assert_eq!((*w).time, TimeSpec { sec: 1716742740, nsec: 0 } );
//!
//!		let status = write_signal(writer, stack_as_f32.as_mut_ptr(), stack_as_f32.len());
//!		assert_ne!(status, 0);
//!
//!		destroy_writer(writer);
//!	}
//! ```
//!
//! For a working javascript example, see `lib/web/html-js/worklet-processor.js`.

// Reduce WASM bundle size by avoiding the standard library.
#![no_std]

// Custom memory allocator for WASM
mod alloc;

use core::{ptr, slice};
use signals::{dcf77, jjy, junghans, wwvb, MessageError, MessageGenerator};
use time::{tz::{self, TzStringError}, TimeSpec};

/// Custom panic handler for WebAssembly that simply halts execution.
#[cfg(all(target_arch="wasm32", not(test)))]
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo<'_>) -> ! {
	core::arch::wasm32::unreachable()
}

/// Transmit a Junghans proprietary signal.
const SIGNAL_JUNGHANS: u8 = 0;
/// Transmit a WWVB signal.
const SIGNAL_WWVB: u8 = 1;
/// Transmit a DCF77 signal.
const SIGNAL_DCF77: u8 = 2;
/// Transmit a JJY signal.
const SIGNAL_JJY: u8 = 3;

/// The size of the custom argument stack in bytes.
///
/// For WASM targets, this is reserved memory in the WASM linear memory starting at __heap_size.
/// For non-WASM targets, this is the minimum size of the pre-allocated buffer to be used in calls
/// to [`make_writer`] and [`write_signal`] to pass arguments and receive errors.
const CUSTOM_STACK_SIZE: usize = 1024;
/// The maximum length of error that will be written to the custom stack
const MAX_ERROR_LEN: usize = 64;

/// WebAssembly wrappers for internal types.
mod wrapper {
	use core::alloc::Layout;
	use crate::alloc::{alloc, dealloc};
	use signals::{MessageError, MessageGenerator, SampledMessage};
	use time::TimeSpec;

	/// A wrapper around a time signal message generator and writer.
	///
	/// `Writer`s must be constructed with [`Writer::new`] because it handles custom memory layout to
	/// efficiently store the message generator and writer in the same allocated block of memory as
	/// this wrapper. Constructing a `Writer` manually will result in a panic on drop.
	///
	/// # Examples
	/// ```
	/// let mut time = TimeSpec { sec: 1716742740, nsec: 0 };
	/// let generator = junghans::new(None).map_err(message_error_to_string).unwrap();
	/// let message = generator.get_message(&mut time).map_err(message_error_to_string).unwrap()
	/// 			  .sample();
	/// let writer = junghans::make_writer::<48000>();
	/// let wrapper = Writer::new(time, message, generator, writer).map(|p| p as usize);
	/// assert!(wrapper.is_ok());
	/// let wrapper = wrapper.unwrap() as *mut Writer;
	/// unsafe { wrapper.drop_in_place(); }
	/// ```
	pub(super) struct Writer {
		/// The **next** timestamp to transmit.
		///
		/// The current timestamp is ended in [`Writer::message`].
		pub(super) time: TimeSpec,
		/// The current message being transmitted.
		///
		/// Note that transmitting the message consumes it.
		pub(super) message: SampledMessage<48000>,
		/// The message generator to create additional messages.
		///
		/// `Writer` takes ownership over the pointed-to value.
		generator: *mut dyn MessageGenerator,
		/// The writer to transmit the message.
		///
		/// `Writer` takes ownership over the pointed-to value.
		writer: *mut dyn FnMut(&mut SampledMessage<48000>, &mut [f32]) -> (usize, bool)
	}

	impl Writer {
		/// Construct a new [`Writer`].
		///
		/// On success, this function returns a *pointer* to `Self` because it allocates on the heap,
		/// like `Box`. The reason it does not use `Box` is to manually manage memory layout, which is
		/// useful because the WASM memory allocator implemented in [`crate::alloc`] is very basic.
		///
		/// The memory layout is very simple, as described below. Note that the layout of `Writer` itself
		/// is illustrative below, since we allow Rust to reorder struct fields as it sees fit.
		///
		/// ```text
		/// -------------- Writer --------------| GeneratorFunc | WriterFunc
		/// time | message | generator | writer |       ^             ^
		///                      |_________|____________|             |
		///                                |__________________________|
		/// ```
		///
		/// There may be padding bytes added between elements within `Writer` and between `Writer`,
		/// `GeneratorFunc`, and `WriterFunc`.
		///
		/// # Errors
		///
		/// Returns a `&'static str` if there is an issue allocating memory.
		pub(super) fn new<GeneratorFunc, WriterFunc>(time: TimeSpec, message: SampledMessage<48000>,
													 generator: GeneratorFunc, writer: WriterFunc)
		-> Result<*mut Self, &'static str>
		where
			GeneratorFunc: MessageGenerator + 'static,
			WriterFunc: FnMut(&mut SampledMessage<48000>, &mut [f32]) -> (usize, bool) + 'static
		{
			// Construct the layout, getting the offsets to write the GeneratorFunc and WriterFunc
			// let (layout, o1, o2) = Layout::new::<Self>()
			// 						.extend(Layout::new::<GeneratorFunc>())
			// 						.and_then(|(l, o1)| {
			// 							l.extend(Layout::new::<WriterFunc>())
			// 								.and_then(|(l, o2)| Ok((l, o1, o2)))
			// 						}).map_err(|_| "Layout error")?;

			// Construct the layout, getting the offsets to write the GeneratorFunc and WriterFunc
			let (layout, o1, o2) = const {
				match Layout::new::<Self>().extend(Layout::new::<GeneratorFunc>()) {
					Ok((layout, o1)) => {
						match layout.extend(Layout::new::<WriterFunc>()) {
							Ok((layout, o2)) => (layout, o1, o2),
							Err(_) => unreachable!()
						}
					}
					Err(_) => unreachable!()
				}
			};

			// Safety: Checks for null pointer returned from [`alloc::alloc`]. Assuming that is not the
			// case, all of the remaining pointer logic (adding, writing) is safe because [`alloc::alloc`]
			// returns a memory block of appropriate size and layout.
			unsafe {
				let t = alloc(layout);
				if t.is_null() {
					return Err("Allocation failed")
				}
				let g = t.add(o1) as *mut GeneratorFunc;
				g.write(generator);
				let w = t.add(o2) as *mut WriterFunc;
				w.write(writer);
				let s = t as *mut Writer;
				// Rust doesn't have placement new, so create a writer and then copy it to the heap.
				s.write(Writer {
					time,
					message,
					generator: g,
					writer: w
				});

				Ok(s)
			}
		}

		/// Write the message to a buffer.
		///
		/// This function will try to fill the buffer, advancing to the next message as needed. On
		/// success, it returns the number of samples written.
		///
		/// # Errors
		///
		/// Returns a [`MessageError`] if an error occurs generating a new message. In this case, the
		/// buffer may be partially written but it is impossible to determine exactly how many samples
		/// were written.
		pub(super) fn write(&mut self, buffer: &mut [f32]) -> Result<usize, MessageError> {
			// Safety: generator and writer are set in Writer::new and never modified, so they are valid
			// pointers. Additionally, since we have a mut reference to self, there can be no aliasing so
			// we can use references.
			let (generator, writer) = unsafe { (&mut *self.generator, &mut *self.writer) };
			let mut len = buffer.len();
			loop {
				let (i, next) = writer(&mut self.message, buffer);
				if next {
					self.message = generator.get_message(&mut self.time)?.sample();
				}

				if i >= len {
					return Ok(buffer.len() + i - len)
				}
				len -= i;
			}
		}
	}

	impl Drop for Writer {
		/// Clean up manually managed memory.
		///
		/// # Panics
		///
		/// This function will panic if the `Writer` was not constructed with [`Writer::new`].
		fn drop(&mut self) {
			// Safety: self.generator and self.writer are set in Writer::new and never modified, so they
			// are valid pointers. Memory dealloced here was allocated by the same allocator with the same
			// layout.
			unsafe {
				self.generator.drop_in_place();
				self.writer.drop_in_place();

				// Ensure we dealloc with the same layout we alloced
				let (layout, _) = Layout::new::<Self>()
									.extend(Layout::for_value(&*self.generator))
									.and_then(|(l, _)| {
										l.extend(Layout::for_value(&*self.writer))
									}).unwrap_unchecked();

				dealloc(self as *mut Self as *mut u8, layout);
			}
		}
	}
}
use wrapper::Writer;

/// Convert a [`MessageError`] into a string for human consumption.
fn message_error_to_string(e: MessageError) -> &'static str {
	match e {
		MessageError::UnsupportedTime(_) => "Unsupported time",
		MessageError::UnsupportedTimezoneOffset(_) => "Unsupported timezone offset",
		MessageError::TimezoneError(_) => unreachable!()
	}
}

/// Macro to implement boilerplate for creating a writer, used by [`make_writer_impl`].
///
/// # Inputs
/// - `$mod`: the time signal module (e.g. [`wwvb`])
/// - `$timezone`: an [`Option<Timezone>`](time::tz::Timezone)
/// - `$time`: a [`mut Timespec`](TimeSpec)
///
/// # Outputs
/// Returns a `Result<usize, &'static str>`, where the `Ok` variant contains a pointer to a
/// `Writer` converted to `usize` for use as a handle by the WASM host.
macro_rules! make_writer_impl_ {
	($mod:ident, $timezone:ident, $time:ident) => ({
		let generator = $mod::new($timezone).map_err(message_error_to_string)?;
		let message = generator.get_message(&mut $time).map_err(message_error_to_string)?.sample();
		let writer = $mod::make_writer::<48000>();
		Writer::new($time, message, generator, writer).map(|p| p as usize)
	})
}

/// Implementation to make a [`Writer`].
///
/// This function parses an optional TZ string to create a time signal generator and writer for
/// the given time. Even though the TZ string is optional, `timezone` must be a valid slice - an
/// empty slice indicates no value.
///
/// # Errors
///
/// Returns `Err(&'static str)` if the TZ string is non-empty but invalid, or if `signal` is not
/// one of the supported signal types.
fn make_writer_impl(signal: u8, mut time: TimeSpec, timezone: &[u8]) -> Result<usize, &'static str> {
	let timezone = match tz::parse_tzstring(timezone) {
		Ok(t) => Some(t),
		Err(e) => {
			match e {
				TzStringError::MissingTzString => None,
				TzStringError::MissingTzDateRule => return Err("Missing timezone date rule"),
				TzStringError::DateOutOfRange => return Err("Timezone date component out of range"),
				TzStringError::TimeOutOfRange => return Err("Timezone time component out of range"),
				TzStringError::InvalidTzDateRuleSpecifier => return Err("Invalid timezone date rule"),
				TzStringError::UnexpectedInput => return Err("Unexpected input at end of timezone string"),
				TzStringError::InvalidOrUnsupportedTzString => return Err("Invalid timezone string")
			}
		}
	};
	match signal {
		SIGNAL_JUNGHANS => make_writer_impl_!(junghans, timezone, time),
		SIGNAL_WWVB => make_writer_impl_!(wwvb, timezone, time),
		SIGNAL_DCF77 => make_writer_impl_!(dcf77, timezone, time),
		SIGNAL_JJY => make_writer_impl_!(jjy, timezone, time),
		_ => Err("Invalid signal type")
	}
}

/// Write an error message to the custom argument stack.
///
/// If `val` is longer than [`MAX_ERROR_LEN - 1`](MAX_ERROR_LEN), it will be truncated. The error
/// message should not contain nulls, as the string is null-terminated on the stack.
///
/// For simplicity, all errors should be ASCII but this is not strictly required.
///
/// # Safety
///
/// The caller must ensure that `ptr` is valid and points to a contiguous block of at least
/// [`MAX_ERROR_LEN`] bytes.
unsafe fn write_to_stack(ptr: *mut u8, val: &str) {
	// Fail to compile if the max error length exceeds the stack size
	const { assert!(MAX_ERROR_LEN <= CUSTOM_STACK_SIZE); }
	let val = val.as_bytes();
	let len = core::cmp::min(val.len(), MAX_ERROR_LEN - 1);
	unsafe {
		ptr::copy_nonoverlapping(val.as_ptr(), ptr, len);
		// Null-terminate
		ptr.add(len).write(0);
	}
}

/// Construct a [`Writer`] on the heap.
///
/// This function returns a handle that can be used in calls to [`write_signal`] and
/// [`destroy_writer`]. Failure to call [`destroy_writer`] when done with the writer will result in
/// a memory leak. Using the handle after destruction is undefined behavior.
///
/// # Errors
///
/// If this function returns `0`, then an error occurred and the handle is invalid. The
/// null-terminated error string will be written to `timezone`.
///
/// # Safety
///
/// The caller must ensure that `timezone` is valid and points to a contiguous block of at least
/// `max(timezone_len, MAX_ERROR_LEN)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn make_writer(signal: u8, msec: i64, timezone: *mut u8, timezone_len: usize) -> usize {
	let time = TimeSpec { sec: msec / 1000, nsec: (msec % 1000) * 1000000 };
	unsafe {
		let t = slice::from_raw_parts(timezone, timezone_len);
		match make_writer_impl(signal, time, t) {
			Ok(u) => u,
			Err(e) => {
				write_to_stack(timezone, e);
				0
			}
		}
	}
}

/// Destroy a [`Writer`] previously made with [`make_writer`].
///
/// This functions cleans up all the memory used by `writer`. Using `writer` after this call is
/// undefined behavior. It is not safe to call this function multiple times with the same handle.
///
/// # Safety
///
/// The caller must ensure that `writer` is a valid, non-zero handle returned by [`make_writer`]
/// that has not yet been destroyed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn destroy_writer(writer: usize) {
	let writer = writer as *mut Writer;
	unsafe {
		writer.drop_in_place();
	}
}

/// Write the time signal to a buffer.
///
/// This function will try to fill the buffer, advancing to the next message as needed. On success,
/// it returns the number of samples written.
///
/// # Errors
///
/// If this function returns `0`, then an error has occurred and the null-terminated error string
/// will be written to `v`. `writer` may be in an invalid state and the only allowable use
/// following an error is a call to [`destroy_writer`].
///
/// # Safety
///
/// The caller must ensure that `v` is valid and points to a properly aligned, contiguous block of
/// at least `max(len * 4, MAX_ERROR_LEN)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn write_signal(writer: usize, v: *mut f32, len: usize) -> usize {
	unsafe {
		let writer = &mut *(writer as *mut Writer);
		let buf = slice::from_raw_parts_mut(v, len);
		match writer.write(buf) {
			Ok(n) => n,
			Err(e) => {
				write_to_stack(v as *mut u8, message_error_to_string(e));
				0
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use core::mem::transmute;
	use super::*;

	unsafe fn get_str(stack: &[u8]) -> &[u8] {
		match stack.iter().position(|v| *v == 0) {
			Some(end) => &stack[..end],
			None => &stack[0..0]
		}
	}

	#[test]
	fn make_writer_test_error() {
		let mut stack: [u8; MAX_ERROR_LEN] = [0; MAX_ERROR_LEN];
		unsafe {
			write_to_stack(stack.as_mut_ptr(), "invalid string");
			assert_eq!(make_writer(SIGNAL_JUNGHANS, 0, stack.as_mut_ptr(), 14), 0);
			assert_eq!(get_str(&stack), b"Invalid timezone string");
		}

		unsafe {
			write_to_stack(stack.as_mut_ptr(), "CET-1CEST,M3.5.0,M100.5.0/3");
			assert_eq!(make_writer(SIGNAL_JUNGHANS, 0, stack.as_mut_ptr(), 27), 0);
			assert_eq!(get_str(&stack), b"Timezone date component out of range");
		}

		unsafe {
			assert_eq!(make_writer(255, 0, stack.as_mut_ptr(), 0), 0);
			assert_eq!(get_str(&stack), b"Invalid signal type");
		}

		unsafe {
			assert_eq!(make_writer(SIGNAL_JUNGHANS, -100000, stack.as_mut_ptr(), 0), 0);
			assert_eq!(get_str(&stack), b"Unsupported time");
		}
	}

	#[test]
	fn make_writer_write_test() {
		let mut stack: [u8; CUSTOM_STACK_SIZE] = [0; CUSTOM_STACK_SIZE];
		unsafe {
			let writer = make_writer(SIGNAL_WWVB, 1716742680000, stack.as_mut_ptr(), 0);
			assert_ne!(writer, 0);
			let w = writer as *mut Writer;
			assert_eq!((*w).time, TimeSpec { sec: 1716742740, nsec: 0 } );

			let mut stack_f32 = transmute::<_, [f32; CUSTOM_STACK_SIZE / 4]>(stack);
			assert_ne!(write_signal(writer, stack_f32.as_mut_ptr(), stack_f32.len()), 0);

			let power = stack_f32
				.iter()
				.copied()
				.reduce(|acc, x| acc + x.abs())
				.unwrap_or(0.)
			/ (stack_f32.len() as f32);
			assert!((power - 0.095).abs() < 0.01, "{}", power);

			for _ in 1..11300 {
				assert_ne!(write_signal(writer, stack_f32.as_mut_ptr(), stack_f32.len()), 0);
			}

			destroy_writer(writer);
		}
	}

	#[test]
	fn make_writer_write_test_error() {
		let mut stack: [u8; CUSTOM_STACK_SIZE] = [0; CUSTOM_STACK_SIZE];
		unsafe {
			let writer = make_writer(SIGNAL_WWVB, 1716742680000, stack.as_mut_ptr(), 0);
			assert_ne!(writer, 0);
			let w = writer as *mut Writer;
			assert_eq!((*w).time, TimeSpec { sec: 1716742740, nsec: 0 } );
			(*w).time.sec = -1000;

			for _ in 1..11250 {
				assert_ne!(write_signal(writer, stack.as_mut_ptr() as *mut f32, stack.len() / 4), 0);
			}

			assert_eq!(write_signal(writer, stack.as_mut_ptr() as *mut f32, stack.len() / 4), 0);
			assert_eq!(get_str(&stack), b"Unsupported time");

			destroy_writer(writer);
		}
	}

	#[test]
	fn module_doc_test() {
		let mut stack_as_u8: [u8; CUSTOM_STACK_SIZE] = [0; CUSTOM_STACK_SIZE];
		unsafe {
			let mut stack_as_f32 = transmute::<_, [f32; CUSTOM_STACK_SIZE / 4]>(stack_as_u8);

			let writer = make_writer(SIGNAL_WWVB, 1716742680000, stack_as_u8.as_mut_ptr(), 0);
			assert_ne!(writer, 0);

			let w = writer as *mut Writer;
			assert_eq!((*w).time, TimeSpec { sec: 1716742740, nsec: 0 } );

			let status = write_signal(writer, stack_as_f32.as_mut_ptr(), stack_as_f32.len());
			assert_ne!(status, 0);

			destroy_writer(writer);
		}

		// Documentation for Writer
		let mut time = TimeSpec { sec: 1716742740, nsec: 0 };
		let generator = junghans::new(None).map_err(message_error_to_string).unwrap();
		let message = generator.get_message(&mut time).map_err(message_error_to_string).unwrap().sample();
		let writer = junghans::make_writer::<48000>();
		let wrapper = Writer::new(time, message, generator, writer).map(|p| p as usize);
		assert!(wrapper.is_ok());
		let wrapper = wrapper.unwrap() as *mut Writer;
		unsafe { wrapper.drop_in_place(); }
	}
}
