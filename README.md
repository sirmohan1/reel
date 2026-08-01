# reel

A single-file, stdlib-only Python media server. Paste a Google Drive link or a
BitTorrent magnet/search, and it streams to your browser while it's still
downloading — no waiting for the whole file, no client app, just a page served
to anything on your network.

Two phases per item: a fragmented, unseekable stream starts within seconds
while the download is in progress ("live"), then it's remuxed into a seekable
file once the download completes ("done"). Season packs are split into one
queue item per episode automatically. Playback adapts to what your specific
device can decode, matching subtitles by name, and reordering audio tracks so
the right language plays first.

## Requirements

Nothing to `pip install` — `reel.py` is 100% Python standard library. What it
does need, all external command-line tools:

| Tool | Needed for | Without it |
|---|---|---|
| **Python 3.9+** | running it at all | — |
| **ffmpeg + ffprobe** | almost everything: remuxing, transcoding, subtitle timing, probing codecs, corruption checks | the app barely functions; install this |
| **[webtorrent-cli](https://github.com/webtorrent/webtorrent-cli)** | BitTorrent/magnet support | torrent search and magnet links won't work; Drive links still will |
| **rclone**, with a remote named exactly `gdrive` | Google Drive links | Drive links won't work; torrents still will |
| **TMDB API key** (free, optional) | the "Picks" recommendation shelves, genre/actor/year search filters | those features are hidden; everything else works |

Platform: built and run on macOS. Linux should mostly work but isn't
regularly tested. Windows isn't supported — the pause feature (SIGSTOP) and
LAN-address detection (`ifconfig`) are POSIX-only and won't work there.

### Installing the prerequisites (macOS, via Homebrew)

```bash
brew install ffmpeg rclone node
npm install -g webtorrent-cli
```

Then configure the Drive remote (skip this if you don't need Drive links):

```bash
rclone config
# create a new remote, type "drive", name it exactly: gdrive
```

## Setup

```bash
git clone https://github.com/sirmohan1/reel.git
cd reel
```

Optional: give it a TMDB key for the recommendation shelves and richer search
filters. Get a free key at https://www.themoviedb.org/settings/api, then
either:

```bash
export REEL_TMDB_KEY=your_key_here
```

or drop it in a file (works across restarts without re-exporting):

```bash
echo "your_key_here" > ~/.reel_tmdb_key
```

No folders to create by hand — `reel_downloads/` (the cache) and
`reel_cache/` (ratings, posters, tracker list) are created automatically the
moment you run it.

## Running it

```bash
python3 reel.py
```

```
  reel  ->  http://localhost:8000
  on this wifi  ->  http://192.168.1.42:8000
  rclone gdrive: True   ffmpeg+ffprobe: True
  cache: /path/to/reel/reel_downloads  (cap 15 GB, 0 restored)
```

Open the first URL locally, or the second from your phone or another device
on the same network — there's also a QR-code button in the header for that
(needs `pip install qrcode`; entirely optional, everything else works without
it).

**No login, no authentication.** Anyone on the same network as the machine
running this can add, remove, and stream anything through it. Set
`REEL_HOST=127.0.0.1` before starting it to restrict it to just this machine:

```bash
REEL_HOST=127.0.0.1 python3 reel.py
```

Stop it with Ctrl-C. Only one instance can run at a time on a given port — a
second `python3 reel.py` will detect the first and refuse to start.

## Using it

- **Paste** a Drive link, a magnet URI, or a bare film/show title into the box
  at the top and hit Add — a title is treated as a search, a link or magnet is
  queued directly.
- **Season packs** split automatically into one queue row per episode. Only
  the episode you actually picked starts downloading; the rest sit held until
  you click to start them yourself — nothing cascades through an entire
  season unattended.
- **Queue rows**: click a row to play it (or start it, if it's only queued).
  Each row also has **pause**/**resume** (stops the download in place,
  keeping progress — not the same as removing it), **refetch** (discards the
  current copy and downloads it again from scratch — for when a file turns
  out corrupt; a background integrity check flags this automatically once a
  download finishes), a **log** panel, and remove (✕, with a few seconds to
  undo).
- **Picks**: horizontally-scrolling shelves of recommended movies and TV
  (needs the TMDB key). Filters for genre, actor, year, rating, language, and
  quality are available once search is expanded.
- **Cache**: capped at 15 GB by default, adjustable from the "Keep at most"
  control at the bottom of the page. Oldest-played, finished files are
  evicted first once you're over the cap; anything still downloading or
  currently playing is never touched.

## Configuration (environment variables)

| Variable | Default | Controls |
|---|---|---|
| `REEL_HOST` | `0.0.0.0` (every interface) | set to `127.0.0.1` to stop listening on the network |
| `REEL_TMDB_KEY` | — | TMDB API key (or use `~/.reel_tmdb_key`) |
| `REEL_PACK` | `50` | max episodes split out of one season-pack torrent; `1` restores old "biggest file only" behaviour |
| `REEL_SHELF` | `12` | how many cards per Picks shelf |
| `REEL_SUB_LANG` | `eng` | subtitle language to look for (ISO 639-2, e.g. `spa`, `fre`) |

The port (`8000`) and per-item cache defaults are constants near the top of
`reel.py` if you want to change them permanently — there's no env var for
those yet.

## Tests

```bash
python3 -m unittest test_reel -v
```

Stdlib `unittest`, no extra packages. Most tests run with no external tools
at all; a handful that need a real ffmpeg decode are decorated to skip
themselves automatically if ffmpeg isn't installed, rather than failing.
