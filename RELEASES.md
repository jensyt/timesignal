# Version 0.3.0 (2025-05-26)

Added support for [MSF].

[MSF]: https://en.wikipedia.org/wiki/Time_from_NPL_(MSF)

# Version 0.2.1 (2025-04-28)

Added support for [JJY]. Some minor `JJY` features are unsupported:
- **Negative leap seconds**. All leap seconds to date have been positive.
- **Alternate format**. During minutes 15 and 45 the standard time format is transmitted rather than
  transmitting the station's call sign and service interruption notifications.

This release also fixes a bug where WWVB would insert a leap second one minute too late.

[JJY]: https://en.wikipedia.org/wiki/JJY

# Version 0.2.0 (2025-01-31)

Added the ability to set a custom time from the command line rather than using the current time.
This is a breaking change with v0.1.0 because the command line parameters have changed. The relevant
changes can be seen below:

v0.1.0:
| Short Form | Long Form   | Value                 | Default          | Description                      |
| ---------- | ----------- | --------------------- | ---------------- | -------------------------------- |
| `-t`       | `--timezone`| Filename or TZ string | Signal-dependent | The timezone to use. More below. |

v0.2.0:
| Short Form | Long Form   | Value                 | Default          | Description                      |
| ---------- | ----------- | --------------------- | ---------------- | -------------------------------- |
| `-z`       | `--timezone`| Filename or TZ string | Signal-dependent | The timezone to use. More below. |
| `-t`       | `--time`    | Date time string      | Current time     | The starting time to transmit.   |

# Version 0.1.0 (2025-01-03)

Initial release with support for [WWVB], [DCF77], and Junghans's proprietary format.

WWVB's amplitude modulated signal is fully implemented, but its phase modulated signal currently
has some unsupported features:
- **6-minute time frames**. 1-minute frames are transmitted instead.
- **Full-year DST in the `dst_next` field**. Time and current DST information can be transmitted in
  full-year DST situations successfully, but the `dst_next` field will be incorrectly set to `0x23`
  (DST transition occurs at a different time).
- **Negative leap seconds**. All leap seconds to date have been positive.
- **Message frames**. These are special, non-time messages that are not intended use of this
  module.

[WWVB]: https://en.wikipedia.org/wiki/WWVB
[DCF77]: https://en.wikipedia.org/wiki/DCF77
