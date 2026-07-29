# Reel — QR pairing (design)

**Date:** 2026-07-29
**Status:** Approved for planning
**Constraint:** One new dependency only (`qrcode`, via pip). Everything else about the file's
current behavior is unchanged. If `qrcode` isn't installed, the app runs exactly as it does
today — this is the first *optional* pip dependency `reel.py` has ever had, and it must degrade
the same way a missing `rclone`/`ffmpeg`/`webtorrent` already does.

## Goal

A QR code on the page, pointing at whatever LAN URL this server is currently reachable at.
Point a phone's camera at the Mac's screen and the phone opens the app — no typing an IP, no
`.local` guessing, no re-doing this every time DHCP hands out a new address.

## Why this needs a decision at all

`reel.py`'s docstring currently promises "No pip installs." Hand-rolling a dependency-free QR
encoder was the alternative and was scoped out (see below) — writing correct QR encoding from
memory is genuinely risky: a QR code that *renders* but doesn't *scan* is worse than not having
the feature, and the failure wouldn't show up until someone's phone fails to read it. You chose
to accept one pip dependency instead. This doc reflects that decision.

## What was actually verified (not assumed)

Before writing this doc, the real `qrcode` package (PyPI, MIT-licensed, the standard tool for
this in Python) was installed in an isolated scratch venv and tested end to end:

- Generated QR codes for both `http://192.168.1.192:8000` (version 2, 25×25 modules) and
  `http://shikhars-macbook-air.local:8000` (version 3, 29×29 modules) — the two realistic shapes
  this feature will actually produce.
- Decoded both back with **`jsQR`, a completely independent implementation** (different
  language, different codebase, no shared code with `qrcode`) — both matched byte-for-byte.
- Confirmed the SVG output path (`qrcode.image.svg.SvgPathImage`) imports only `xml.etree`
  (stdlib) — no Pillow, no `pypng`. So shipping SVG keeps this to exactly **one** new dependency,
  not three.

## Non-goals

- No PNG/Pillow output — SVG only, to avoid a second and third dependency.
- No configurable QR content, styling, or size. One code, one purpose: the URL this server
  answers on.
- No terminal/ASCII QR in the startup banner. Easy to add later with the same library, but the
  ask was specifically "on the page," so that's the only surface this covers.

## Architecture

### Dependency check (mirrors `has_rclone()` / `has_ffmpeg()` / `has_webtorrent()`)

```
HAS_QRCODE = None

def has_qrcode():
    global HAS_QRCODE
    if HAS_QRCODE is None:
        try:
            import qrcode          # noqa: F401
            HAS_QRCODE = True
        except ImportError:
            HAS_QRCODE = False
    return HAS_QRCODE
```

Computed once, cached — same pattern as `HAS_ZSCALE`. `qrcode` is imported lazily inside this
function and inside the route handler, never at module load time, so a machine without it
installed never fails to *start* `reel.py` — it just doesn't get this one feature, exactly like
a machine without `webtorrent` still runs the Drive half of the app fine today.

### What gets encoded

The same address the startup banner already prints: `http://{lan_ip()}:{PORT}`. Two cases where
there is nothing to encode, both already distinguishable with existing code:

- `HOST == "127.0.0.1"` (the existing `REEL_HOST` opt-out) — no LAN address is being served at
  all, so there is nothing useful to point a phone at.
- `lan_ip()` returns `None` — no active network interface (e.g., no wifi connected).

In both cases the QR affordance is hidden client-side rather than shown broken.

### New endpoint

`GET /qr` → `image/svg+xml` body, generated fresh per request (generation measured at low
single-digit milliseconds in testing above — no caching needed). Returns `404` if `has_qrcode()`
is false or there's no LAN address to encode, consistent with how other routes already 404 on
"nothing to serve" (`/stream`, `/live`).

No origin check needed — it's a read-only GET carrying no new information (anyone on the LAN
can already see this port is open), matching the existing unauthenticated-GET pattern used by
`/jobs`, `/sys`, `/stream`, `/live`.

### `/sys` gets one new field

```
"lan_url": "http://192.168.1.192:8000"   # or null if there's nothing to share
```

So the client can decide whether to show the QR button at all without duplicating the
host/lan_ip logic in JavaScript. Purely additive to the existing `/sys` response
(`rclone`/`ffmpeg`/`webtorrent`/`cap_gb`/`used_gb` are untouched).

### UI

A small icon button in the header, next to the existing status light. Clicking it opens a
lightweight popover: the SVG rendered inline, the plain URL text underneath it (so it can be
read aloud or typed manually as a fallback), nothing else. Hidden entirely — not shown disabled
— when `/sys` reports `lan_url: null`.

## Testing

**Regression (must prove nothing broke):**
- With `qrcode` not installed, `reel.py` starts and runs identically to today; `/qr` 404s;
  the header shows no QR button.
- `REEL_HOST=127.0.0.1` hides the QR button (nothing to share) without affecting anything else.
- Existing `/sys` consumers (the cache meter) are unaffected by the new `lan_url` field.

**Feature (the round-trip already proven above, re-run against the actual shipped code path):**
- `/qr`'s SVG response, decoded by an independent scanner, matches the URL reported in `/sys`.
- Confirmed for both a plain-IP address and a `.local` hostname, since they land on different
  QR versions (2 vs 3) and this must not only work for the shorter, easier case.
- A real phone camera (not just a decoder library) scans it and opens the page — the actual
  point of the feature, and the one thing a library-level test can't fully stand in for.

## Open implementation details (for the plan, not blockers)

- Exact popover placement/styling to match the existing header's terminal aesthetic.
- Whether `/qr` should also reflect `X-Forwarded-Host`-style overrides for any future reverse-proxy
  use — out of scope now, no such use exists today.
