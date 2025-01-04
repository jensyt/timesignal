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
