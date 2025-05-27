//! Generate time signals using simple audio output.
//!
//! This crate can generate public time signals ([DCF77], [WWVB], and [JJY40/60]) as well as a
//! proprietary time signal ([Junghans]), outputting them to the device's default audio output.
//! This works by taking advantage of stray RF signals created by audio hardware as a side effect
//! of their operation -- the audio output itself is not useful as devices listening for these time
//! signals use RF rather than audio.
//!
//! [DCF77]: https://en.wikipedia.org/wiki/DCF77
//! [WWVB]: https://en.wikipedia.org/wiki/WWVB
//! [JJY40/60]: https://en.wikipedia.org/wiki/JJY
//! [Junghans]: signals::junghans
//!
//! # Command Line Arguments
//!
//! General form: `timesignal [options...] signal`
//!
//! In addition to one required argument (the signal to generate), this application supports
//! several optional command line arguments for configuration:
//!
//! | Short form | Long form    | Argument                | Default          | Description                     |
//! | ---------- | ------------ | ----------------------- | ---------------- | ------------------------------- |
//! | `-n`, `-c` | `--count`    | Integer > 0             | 4                | The number of messages to ouput |
//! | `-z`       | `--timezone` | Filename or [TZ string] | Signal-dependent | The [timezone] to use           |
//! | `-t`       | `--time`     | [Date time string]      | Current time     | The starting time to transmit   |
//! |            | `--ntp`      | Hostname or IP          | None             | Use [NTP] to determine the time |
//!
//! For public time signals, the message rate is one message per minute. For Junghans, the message
//! rate is four messages per minute.
//!
//! Each signal uses timezone information slightly differently, as described here:
//! - Junghans: the timezone represents the device's local time, defaulting to /etc/localtime
//! - WWVB: the timezone represents US standard DST rules, defaulting to
//!         /usr/share/zoneinfo/America/New_York
//! - DCF77: the timezone represents the time in Berlin, Germany, defaulting to
//!          /usr/share/zoneinfo/Europe/Berlin
//! - JJY: the timezone represents Japan standard time, defaulting to
//!        /usr/share/zoneinfo/Asia/Tokyo
//! - MSF: the timezone represents the time in the UK, defaulting to
//!        /usr/share/zoneinfo/Europe/London
//!
//! Timezone files must be in TZif format, which is common to Unix-like systems. Alternatively, a
//! TZ string can be used in its place (e.g. `EST5EDT,M3.2.0,M11.1.0` for US Eastern). If DST is
//! specified in the TZ string, the rules for switching to/from DST must be included.
//!
//! The last argument must be the signal to generate, one of:
//! - `junghans`
//! - `dcf77`
//! - `wwvb`
//! - `jjy`
//! - `jjy40` (alias for `jjy`)
//! - `jjy60` (alias for `jjy`)
//! - `msf`
//!
//! [timezone]: time::tz
//! [NTP]: sntp
//! [TZ string]: time::tz::tzstring
//! [date time string]: time::parse::parse_timestamp
//!
//! # Examples
//!
//! Launch with default settings using Junghans time signal
//! ```sh
//! timesignal junghans
//! ```
//!
//! Transmit DCF77 for 8 minutes
//! ```sh
//! timesignal -n 8 dcf77
//! ```
//!
//! Transmit Junghans using the US east timezone
//! ```sh
//! timesignal -z /usr/share/zoneinfo/America/New_York junghans
//! timesignal -z "EST5EDT,M3.2.0,M11.1.0" junghans
//! ```

use std::error::Error;
use std::num::NonZero;
use std::process::ExitCode;

use std::sync::{Arc, Condvar, Mutex};
use std::sync::mpsc::{sync_channel, Receiver};
use cpal::traits::{DeviceTrait, HostTrait, StreamTrait};
use cpal::Sample;

use args::{Arguments, ArgumentsError, SignalType};
use signals::{Message, SampledMessage, MessageGenerator, dcf77, junghans, wwvb, jjy, msf};

mod args;

/// Simple multi-threaded flag using a condition variable.
///
/// Note that this type does not currently support re-use, i.e. when a single thread calls
/// [`Flagger::notify`], all subsequent calls to [`Flagger::wait`] will return immediately.
///
/// # Examples
/// ```
/// let flagger = Flagger::new();
/// let flagger_clone = flagger.clone();
/// thread::spawn(move || {
/// 	// Do some work
///
/// 	// Notify work completed
/// 	flagger_clone.notify();
/// });
///
/// // Wait for thread to complete
/// flagger.wait();
/// ```
struct Flagger {
	/// Mutex containing the flag. `true` means continue waiting.
	mutex: Mutex<bool>,
	/// Condition variable to manage wait/notify.
	cond: Condvar
}

impl Flagger {
	/// Create a new [`Flagger`] ready to be [`wait`](Flagger::wait)ed on.
	fn new() -> Arc<Flagger> {
		Arc::new(Flagger {
			mutex: Mutex::new(true),
			cond: Condvar::new()
		})
	}

	/// Wait for another thread to call [`Flagger::notify`].
	///
	/// This call will block the current thread until another thread calls `notify`, avoiding spurious
	/// wakeups using the owned codition variable.
	fn wait(&self) {
		drop(self.cond.wait_while(self.mutex.lock().unwrap(), |pending| { *pending }).unwrap());
	}

	/// Notify threads [`wait`](Flagger::wait)ing to unblock.
	///
	/// This call will unblock all waiting threads, and immediately unblock all subsequent calls to
	/// [`Flagger::wait`].
	fn notify(&self) {
		let mut flag = self.mutex.lock().unwrap();
		*flag = false;
		self.cond.notify_all();
	}
}

/// Current state of the writer.
enum WriterState {
	/// Waiting for initial message ready to send. Write [`f32::EQUILIBRIUM`].
	Waiting,
	/// Running, write the outputs of the associated writer function.
	Running,
	/// Finishing, write the remaining output and then pad with [`f32::EQUILIBRIUM`].
	Finishing
}

/// Try to read a message from the channel.
///
/// This function does not block, and instead returns `None` if no messages are immediately
/// available.
///
/// The [`Message::delay`] field in the returned message is converted from real time in nanoseconds
/// to sample space at 48 kHz, meaning 1 unit of delay is 20.833 microseconds.
#[inline(always)]
fn get_message(rx: &Receiver<Message>) -> Option<SampledMessage<48000>> {
	if let Ok(m) = rx.try_recv() {
		// Convert delay to samples
		Some(m.sample())
	} else {
		None
	}
}

/// Make a writer function that calls `func` to generate the time signal.
///
/// This writer provides three core behaviors for all time signals:
/// 1. It reads messages from the receiver, `rx`, to provide to the time signal writer `func`.
/// 2. It repeatedly calls `func`, as needed, to ensure the buffer is written fully.
/// 3. It ensures the audio channel does not get blocked before/after messages are available.
///
/// `func` must be a function or function-like object that takes two inputs:
/// 1. The message to transmit.
/// 2. The buffer to write the transmitted values into (ranging [-1, 1]).
///
/// ... and returns a tuple of two outputs:
/// 1. The number of samples written.
/// 2. A boolean indicating whether the message has been transmitted completely.
///
/// # Examples
/// ```
/// let host = cpal::default_host();
/// let device = host.default_output_device().ok_or("Failed to get default audio output device")?;
/// let config = cpal::StreamConfig {
/// 	channels: 1,
/// 	sample_rate: cpal::SampleRate(48000),
/// 	buffer_size: cpal::BufferSize::Fixed(1024),
/// };
/// let (tx, rx) = sync_channel::<Message>(0);
/// let flagger = Flagger::new();
/// let stream = device.build_output_stream(
/// 				&config,
/// 				make_writer(rx, flagger.clone(), junghans::make_writer()),
/// 				audio_error,
/// 				None)?;
/// stream.play()?;
///
/// let j = junghans::new(tz::parse_file("/etc/localtime")?);
/// let mut time = time::currenttime().ok_or("Failed to get current system time")?;
/// for _ in 0..4 {
/// 	tx.send(j.get_message(&mut time)?)?;
/// }
///
/// flagger.wait();
/// ```
fn make_writer<F>(rx: Receiver<Message>, flagger: Arc<Flagger>, count: NonZero<usize>, mut func: F)
-> impl FnMut(&mut [f32], &cpal::OutputCallbackInfo)
where F: FnMut(&mut SampledMessage<48000>, &mut [f32]) -> (usize, bool) + Send
{
	let mut state = WriterState::Waiting;
	let mut message = Default::default();
	let mut c = 0;
	let count = count.get();

	move |data: &mut [f32], _info: &cpal::OutputCallbackInfo| {
		// Check whether to transition state
		match state {
			WriterState::Waiting => {
				if let Some(m) = get_message(&rx) {
					message = m;
					state = WriterState::Running;
				}
			},
			WriterState::Finishing => {
				// Notify for exit
				flagger.notify();
			},
			_ => ()
		}

		// Write the data
		if let WriterState::Running = state {
			let mut i = 0;
			let len = data.len();
			// Keep writing until the buffer is full
			while i < len {
				let (j, next) = func(&mut message, &mut data[i..]);
				i += j;
				// If we reached the end of message, try to start writing the next message
				// or simply finish the buffer with silence
				if next {
					c += 1;
					if let Some(m) = get_message(&rx) {
						message = m;
					} else {
						if c < count {
							state = WriterState::Waiting;
						} else {
							state = WriterState::Finishing;
						}
						data.iter_mut().skip(i).for_each(|v| *v = f32::EQUILIBRIUM);
						break;
					}
				}
			}
		} else {
			// Write silence if a message isn't available
			data.iter_mut().for_each(|v| *v = f32::EQUILIBRIUM);
		}
	}
}

/// Error handler for audio streaming.
///
/// Panics and prints the error.
fn audio_error(error: cpal::StreamError) {
	panic!("Error occured on the stream: {}", error);
}

/// Generate a time signal and play it over the default audio output device.
///
/// Creates and configures output at 48kHz, 1024 sample `f32` buffer, and transmits `$args.count`
/// messages, blocking until complete. Optionally uses `$args.ntp` to get NTP time.
///
/// # Inputs
///
/// - `$args`: identifier for a variable of type [`Arguments`]
/// - `$signal`: [`SignalType`] match arm
/// - `$mod`: module name for the signal. The module must include two functions:
///
///   1.
///       ```
///       pub fn make_writer() -> impl FnMut(&mut Message, &mut [f32]) -> (usize, bool)
///       ```
///   2.
///       ```
///       pub fn new(tz: Option<Timezone>) -> Result<T, Error>
///       ```
///       where
///       ```
///       T::get_message(&self, time: &mut TimeSpec) -> Result<Message, Error>
///       ```
///
/// # Errors
///
/// This macro can generate a variety of errors, all of which can be converted to `Box<dyn Error>`:
/// - [`cpal::BuildStreamError`], [`cpal::PlayStreamError`] from configuring and playing audio.
/// - `&str` for several untyped errors (no output audio device, failed to get system time,
///    unsupported signal type).
/// - [`std::io::Error`] for NTP errors.
/// - [`signals::MessageError`] for message generation errors.
/// - [`std::sync::mpsc::SendError`] for errors sending messages to the audio output thread.
///
/// # Examples
///
/// ```
/// fn play(args: Arguments) -> Result<ExitCode, Box<dyn Error>> {
/// 	play!(args,
/// 		SignalType::Junghans => junghans,
/// 		SignalType::DCF77 => dcf77
/// 	);
/// 	Ok(ExitCode::SUCCESS)
/// }
/// ```
macro_rules! play {
	($args:ident, $($signal:pat_param => $mod:ident),+) => ({
		// Set up output device
		let host = cpal::default_host();
		let device = host.default_output_device().ok_or("Failed to get default audio output device")?;
		let config = cpal::StreamConfig {
			channels: 1,
			sample_rate: cpal::SampleRate(48000),
			buffer_size: cpal::BufferSize::Fixed(1024),
		};
		// Set up thread synchronization
		let (tx, rx) = sync_channel::<Message>(0);
		let flagger = Flagger::new();

		match $args.signal {
			$($signal => {
				// Create output stream & message writers
				let stream = device.build_output_stream(
								&config,
								make_writer(rx, flagger.clone(), $args.count, $mod::make_writer::<48000>()),
								audio_error,
								None)?;
				stream.play()?;

				// Create time signal message generator
				let n = $mod::new($args.timezone)?;

				// Get current time
				let mut time = match $args.time {
					Some(t) => t,
					None => match $args.ntp {
						Some(addr) => sntp::get_ntp_time(&addr)?,
						None => time::now().ok_or("Failed to get current system time")?
					}
				};

				// Create time signal messages
				for _ in 0..$args.count.get() {
					tx.send(n.get_message(&mut time)?)?;
				}

				// Wait for audio to complete
				flagger.wait();
			})+
			//_ => return Err(format!("Signal {:?} not yet supported!", $args.signal).into())
		}
	});
}

/// Generate a time signal and play it over the default audio output device.
///
/// Creates and configures output at 48kHz, 1024 sample `f32` buffer, and transmits `args.count`
/// messages, blocking until complete. Optionally uses `args.ntp` to get NTP time.
///
/// # Errors
///
/// This function can generate a variety of errors, all wrapped in `Box<dyn Error>`:
/// - [`cpal::BuildStreamError`], [`cpal::PlayStreamError`] from configuring and playing audio.
/// - `&str` for several untyped errors (no output audio device, failed to get system time,
///    unsupported signal type).
/// - [`std::io::Error`] for NTP errors.
/// - [`signals::MessageError`] for message generation errors.
/// - [`std::sync::mpsc::SendError`] for errors sending messages to the audio output thread.
///
/// # Examples
/// ```
/// play(args)
/// 	.inspect_err(|e| eprintln!("{}", e))
/// 	.unwrap_or(ExitCode::FAILURE)
/// ```
fn play(args: Arguments) -> Result<ExitCode, Box<dyn Error>> {
	play!(args,
		SignalType::Junghans => junghans,
		SignalType::DCF77 => dcf77,
		SignalType::WWVB => wwvb,
		SignalType::JJY => jjy,
		SignalType::MSF => msf
	);

	Ok(ExitCode::SUCCESS)
}

/// Main program entry point.
///
/// Parses input arguments and plays time signal audio output. See [`crate`] documentation for
/// details.
fn main() -> ExitCode {
	let args = match Arguments::parse(std::env::args_os().skip(1)) {
		Ok(a) => a,
		Err(e) => {
			return if let ArgumentsError::Help = e {
				println!("\
Generate time signals for setting radio-controlled clocks with no extra hardware.

Usage: timesignal [OPTIONS] <SIGNAL>

Options:
  -n, -c, --count <COUNT>   the number of messages to output, default 4
  -z, --timezone <TIMEZONE> the timezone to use, default depends on signal
  -t, --time <DATETIME>     the starting time to use, defaults to now
  --ntp <SERVER>            the NTP server to use for time, default none

Supported signals:
  wwvb
  dcf77
  junghans
  jjy (alias jjy40/jjy60)
  msf

Examples:
  timesignal -n 6 wwvb
  timesignal -z \"EST5EDT,M3.2.0,M11.1.0\" junghans
  timesignal -t \"2024-04-12 10:27:00.519 -07:00\" junghans
  timesignal -n 8 --ntp time.google.com dcf77\n");
				ExitCode::SUCCESS
			} else {
				eprintln!("{}", e);
				ExitCode::FAILURE
			}
		}
	};

	if args.time.is_some() && args.ntp.is_some() {
		println!("Warning: --ntp does nothing when manual time is set with -t or --time");
	}

	play(args)
		.inspect_err(|e| eprintln!("{}", e))
		.unwrap_or(ExitCode::FAILURE)
}
