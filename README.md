# timesignal
Generate time signals for setting radio-controlled clocks with no extra hardware.

This program can generate public time signals ([DCF77], [WWVB], and [JJY40/60]) as well as a
proprietary time signal ([Junghans]), outputting them to the device's default audio output. This
works by taking advantage of stray RF signals created by audio hardware as a side effect of their
operation -- the audio output itself is not useful as devices listening for these time signals use
RF rather than audio.

Why use this instead of the many other time signal generators available? Three possible reasons:

1. This program does not require special hardware. Most other projects are designed for a Raspberry
   Pi or similar device, using its clock output and extra components to generate the RF signal.
   This project instead takes advantage of existing audio hardware on a laptop or desktop.
2. One of the limitations of how most projects use the Raspberry Pi's clock output is that they
   cannot implement phase modulated signals. This project aims to fully reproduce the public time
   signals, including both amplitude and phase modulation.
3. This program supports Junghans's proprietary format, which is more featureful if you have a
   supported clock or watch.

## Quick Setup Guide
1. Install a recent version of [Rust].
2. Clone this repository.
3. Run `cargo run -r -- <signal>` in the root directory. Try `wwvb` for signal.

The initial build may take a few seconds. Once done, this will start to play a very high-pitched,
encoded message representing the time. Make sure you place the clock or watch you want to set as
close as possible to the speaker since the radiated RF signal will be weak. Also make sure the
clock or watch are in reception mode!

As an alternative to step 3 above, you can build and run the program separately:

3. Run `cargo build -r`
4. Run `target/release/timesignal <signal>`

## Command Line Options
The general form for running this program is
```sh
timesignal [options] signal
```

The possible signal types are:
- `junghans`: Proprietary Junghans signal
- `wwvb`: US's [WWVB]
- `dcf77`: Germany's [DCF77]
- `jjy40`: Japan's [JJY40] (not yet implemented)
- `jjy60`: Japan's [JJY60] (not yet implemented)
- `msf`: UK's [MSF] (not yet implemented)

The supported options are:

| Short Form | Long Form   | Value                 | Default          | Description                      |
| ---------- | ----------- | --------------------- | ---------------- | -------------------------------- |
| `-n`, `-c` | `--count`   | Positive Integer      | 4                | The number of messages to send.  |
| `-t`       | `--timezone`| Filename or TZ string | Signal-dependent | The timezone to use. More below. |
|            | `--ntp`     | Hostname or IP        | None             | Use NTP to determine the time.   |

For public time signals, the message rate is one message per minute. For Junghans, the message rate
is four messages per minute.

Each signal uses timezone information slightly differently, as described here:
- **Junghans**: the timezone represents the device's local time, defaulting to /etc/localtime
- **WWVB**: the timezone represents US standard DST rules, defaulting to
            /usr/share/zoneinfo/America/New_York
- **DCF77**: the timezone represents the time in Berlin, Germany, defaulting to
             /usr/share/zoneinfo/Europe/Berlin

Timezone files must be in [TZif format], which is common to Unix-like systems. Alternatively, a
[TZ string] can be used in its place (e.g. `EST5EDT,M3.2.0,M11.1.0` for US Eastern). If DST is
specified in the TZ string, the rules for switching to/from DST must be included.

## Examples
Run the Junghans signal for two minutes (8 messages), setting a custom timezone configuration:
```sh
timesignal -n 8 -t "CET-1CEST,M3.5.0,M10.5.0/3" junghans
```

Run the DCF77 signal for four minutes (default), using Google's NTP server to get the most accurate
current time:
```sh
timesignal --ntp time.google.com dcf77
```

## Modifying the Code
Feel free to modify and add code as you see fit. To build the documentation, run `cargo doc` and
then open `target/doc/timesignal/index.html`. To run unit tests, run `cargo test` or if you have
[cargo-nextest] run `cargo nextest run`.

Documentation for the Junghans message format can be found at the top of `src/junghans.rs`.

[DCF77]: https://en.wikipedia.org/wiki/DCF77
[WWVB]: https://en.wikipedia.org/wiki/WWVB
[JJY40/60]: https://en.wikipedia.org/wiki/JJY
[JJY40]: https://en.wikipedia.org/wiki/JJY
[JJY60]: https://en.wikipedia.org/wiki/JJY
[Junghans]: https://www.junghans.de/
[MSF]: https://en.wikipedia.org/wiki/Time_from_NPL_(MSF)
[Rust]: https://www.rust-lang.org/
[TZif format]: https://www.rfc-editor.org/rfc/rfc9636.txt
[TZ string]: https://www.gnu.org/software/libc/manual/html_node/TZ-Variable.html
[cargo-nextest]: https://nexte.st/
