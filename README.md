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
Try it online [here](https://timesignal.pages.dev/)!

Alternatively, to install the program locally:
1. Install a recent version of [Rust].
    - On Linux, you may also need to install the `libasound2-dev` package on Debian-based
      distributions or `alsa-lib-devel` on Fedora.
2. Clone this repository.
3. Run `cargo run -r -- <signal>` in the root directory. Try `wwvb` for signal.

The initial build may take a few seconds. Once done, this will start to play a very high-pitched,
encoded message representing the time. Make sure you place the clock or watch you want to set as
close as possible to the speaker since the radiated RF signal will be weak. Also make sure the
clock or watch are in reception mode!

As an alternative to step 3 above, you can build and run the program separately:

3. Run `cargo build -r`
4. Run `./target/release/timesignal <signal>`

## Command Line Options
The general form for running this program is
```sh
timesignal [options] signal
```

The possible signal types are:
- `junghans`: Proprietary Junghans signal
- `wwvb`: US's [WWVB]
- `dcf77`: Germany's [DCF77]
- `jjy`: Japan's [JJY]. `jjy40` and `jjy60` are aliases.
- `msf`: UK's [MSF] (not yet implemented)

The supported options are:

| Short Form | Long Form   | Value                 | Default          | Description                      |
| ---------- | ----------- | --------------------- | ---------------- | -------------------------------- |
| `-n`, `-c` | `--count`   | Positive Integer      | 4                | The number of messages to send.  |
| `-z`       | `--timezone`| Filename or TZ string | Signal-dependent | The timezone to use. More below. |
| `-t`       | `--time`    | Date time string      | Current time     | The starting time to transmit.   |
|            | `--ntp`     | Hostname or IP        | None             | Use NTP to determine the time.   |

For public time signals, the message rate is one message per minute. For Junghans, the message rate
is four messages per minute.

Each signal uses timezone information slightly differently, as described here:
- **Junghans**: the timezone represents the device's local time, defaulting to /etc/localtime
- **WWVB**: the timezone represents US standard DST rules, defaulting to
            /usr/share/zoneinfo/America/New_York
- **DCF77**: the timezone represents the time in Berlin, Germany, defaulting to
             /usr/share/zoneinfo/Europe/Berlin
- **JJY**: the timezone represents Japan standard time, defaulting to
           /usr/share/zoneinfo/Asia/Tokyo

Timezone files must be in [TZif format], which is common to Unix-like systems. Alternatively, a
[TZ string] can be used in its place (e.g. `EST5EDT,M3.2.0,M11.1.0` for US Eastern). If DST is
specified in the TZ string, the rules for switching to/from DST must be included.

Date time strings follow a similar format to [Javascript], with some small modifications: niche
features (extended years, special 24:00:00 time) are unsupported, dates and times without a
timezone are always interpreted as UTC, and spaces are allowed between date and time components.

## Examples
Run the Junghans signal for two minutes (8 messages), setting a custom timezone configuration:
```sh
timesignal -n 8 -z "CET-1CEST,M3.5.0,M10.5.0/3" junghans
```

Run the DCF77 signal for four minutes (default), using Google's NTP server to get the most accurate
current time:
```sh
timesignal --ntp time.google.com dcf77
```

Run the WWVB signal for four minutes (default), using a fixed starting time:
```sh
timesignal -t "2024-06-03 17:21:05.692 -08:00" wwvb
```

## Modifying the Code
Feel free to modify and add code as you see fit. To build the documentation, run `just doc` and
then open `target/doc/timesignal/index.html`. To run unit tests, run `just test` or if you have
[cargo-nextest] run `cargo nextest run`.

If you don't have [just], you can open and run the commands from `justfile` manually.

Documentation for the Junghans message format can be found at the top of `src/junghans.rs`.

[DCF77]: https://en.wikipedia.org/wiki/DCF77
[WWVB]: https://en.wikipedia.org/wiki/WWVB
[JJY40/60]: https://en.wikipedia.org/wiki/JJY
[JJY]: https://en.wikipedia.org/wiki/JJY
[Junghans]: https://www.junghans.de/
[MSF]: https://en.wikipedia.org/wiki/Time_from_NPL_(MSF)
[Rust]: https://www.rust-lang.org/
[TZif format]: https://www.rfc-editor.org/rfc/rfc9636.txt
[TZ string]: https://www.gnu.org/software/libc/manual/html_node/TZ-Variable.html
[cargo-nextest]: https://nexte.st/
[Javascript]: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Date#date_time_string_format
[just]: https://github.com/casey/just
