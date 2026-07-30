# Reel — Subtitles

**Status:** Built. This describes what exists, not what was planned; where the
two diverged the reasons are recorded, since most of them were things the live
API taught us rather than decisions made up front.

## What it does

Finds English subtitles for an item and serves them as a WebVTT sidecar, which
the player attaches as a `<track>`. Nothing about playback waits on it: it runs
on a background thread, and an item with no subtitles behaves exactly as before.

Source: **OpenSubtitles' legacy endpoint** (`rest.opensubtitles.org`). It needs
no API key, so this works on a fresh machine rather than waiting on credentials,
and no new dependency — `gzip` and `struct` are stdlib, and ffmpeg was already
required.

## How a subtitle is chosen

Two lookups, tried in order, because they carry very different guarantees.

**1. By file hash.** OpenSubtitles identifies a release by size plus 64-bit sums
of its first and last 64 KiB (`osdb_hash`). A hit means the subtitle was uploaded
for a byte-identical file, so its timings *are* this file's. Shown as **`CC`**.

**2. By release name.** The fallback, and the risky one: it returns subtitles for
*a* copy of the film, not necessarily this copy. So candidates are scored
(`subs_fit`) rather than trusted:

- **runtime** — the subtitle's last cue against the film's duration. The
  strongest signal available without a hash. On one search this rejected 18 of
  84 candidates, ending 12, 64 and 77 minutes from where the film ends.
- **source tokens** — `1080p`, `brrip`, `bluray`, `extended`, `remastered`
  shared between the two names, since different sources cut differently.
- **quality** — skips what uploaders flagged bad; trusted uploaders and download
  count break ties rather than deciding.

Shown as **`CC?`** in amber, with the reasoning in its tooltip, because a judged
fit can still drift.

The difference is not cosmetic. Ranking by popularity alone picked a 720p HD-DVD
rip for a 1080p BrRip; scoring picks the matching YIFY release.

## Two things the live API forced

Neither was foreseeable from documentation, and both are silent failures:

- **The query must be lowercase.** With any uppercase it 302s to
  `https://_/…` — an unresolvable host — so the request fails in a way
  indistinguishable from "this film has no subtitles". Lowercase returns 200
  with 84 results.
- **These files open with adverts.** `strip_subs_spam` drops them; on the file
  tested, 2 of 1309 cues.

## When it runs, and why that matters

Timed around a constraint the original plan listed only as an open detail, and
which turned out to be central: **both conversions run `-map 0:v:0 -map 0:a:0?`,
so they strip subtitles**, and `finalize_torrent` then deletes the torrent
folder. The hash must therefore be taken from the release *as downloaded*.

So there are two kinds of call site:

- **Early, by name** — right after the torrent probe, and in `consider_live` for
  a Drive download. Reads nothing from disk, so it costs one request and
  subtitles arrive within seconds of pressing play. This was a correction: every
  call site originally fired only after a download *completed*, which for a
  two-hour film meant no subtitles until roughly the moment they stopped being
  useful. A live job was observed playing with `subs_status: None`.
- **Late, by hash** — after a Drive download and in `finalize_torrent`, both
  before the source is deleted. These carry the actual file and can *upgrade* a
  name match to an exact one.

`start_subs` allows that upgrade while refusing to duplicate a running search,
disturb an already-exact match, or downgrade a good result: a failed upgrade
keeps what was already there rather than reverting to "unavailable".

## Surface

- `GET /subs/<id>.vtt` → `text/vtt`, or 404. Accepts the id with or without the
  suffix, since that is how `<track>` requests it.
- Job fields on `/jobs`: `subs`, `subs_status` (`searching`/`ready`/
  `unavailable`), `subs_source`, `subs_lang`, `subs_name`, `subs_exact`,
  `subs_why`, `subs_note`.
- `REEL_SUB_LANG` selects the language, ISO 639-2, default `eng`.
- Client: `applySubs()` runs after every `v.load()`, since `load()` discards text
  tracks; the poll re-applies it when a late arrival lands, so a subtitle found
  after playback began simply appears. Chrome ignores `default` on a track added
  after load, so the mode is set explicitly.

## Naming and cleanup

Sidecars are `{jobid}.subs.{lang}.vtt` — dotted, like the existing `.live.` and
`.compat.` files. `restore()` rebuilds jobs by splitting filenames on `__` into
three parts, so a `__`-separated name would have been resurrected as a phantom
video job.

The sidecar is in `drop()` and eviction cleanup, and `restore()` reattaches one
whose job came back while deleting one whose job did not — otherwise it would
count against the cache cap forever with nothing able to reach it.

## Not built

- **Embedded subtitle tracks.** Both conversions strip them, so this would need
  extraction before conversion. Straightforward to add; simply not needed once
  OpenSubtitles worked.
- **Whisper transcription.** Would be the only hard dependency in the file, for
  a result that arrives long after a first watch. Deferred deliberately.
- **A language picker.** One target language, configurable, no UI.
- **OCR of image-based subtitles** (PGS/VOBSUB).

## Corrections to the original design

- It claimed the torrent path never sets `job["path"]`. True when written; the
  `finalize_torrent` work has since made it false.
- It expected the CSP to block the `<track>` fetch. Per CSP3, `media-src` covers
  text tracks, and the existing `media-src 'self'` permits it. No change needed.
- It planned a three-stage chain (embedded → online → Whisper). Only the online
  stage was built, and it proved sufficient on its own.
