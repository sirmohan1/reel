#!/usr/bin/env python3
"""
Reel (local) — stream Google Drive videos to your browser while they download.

Two phases per item:

  1. Live.  rclone writes the download to disk; ffmpeg reads that growing file
     and emits a fragmented MP4 (or MP3) which is served as it is written, so
     playback starts within seconds. No seeking yet.
  2. Seekable.  When the download lands, the file is remuxed to a faststart MP4
     with range support and the player swaps to it at the same timestamp.

Phase 1 needs the container's index at the *front* of the file. An MP4 or MOV
with `moov` at the end cannot be decoded until the last byte arrives, so those
items skip straight to phase 2. Reel probes the header and picks per file.

Run:  python3 reel_local.py   then open http://localhost:8000, or the
http://<this-machine>:8000 address printed on startup from any device on the
same wifi. Bind to this machine only with REEL_HOST=127.0.0.1.
Needs: an rclone remote named 'gdrive' (rclone config), plus ffmpeg + ffprobe.
No pip installs required. Optional: `pip install qrcode` puts a QR code for the
LAN address in the header, so a phone can scan its way in instead of typing an
IP. Everything else runs exactly the same without it.
"""

import http.server
import socketserver
import socket
import signal
import sys
import urllib.request
import urllib.parse
import re
import os
import json
import queue
import gzip
import struct
import random
import binascii
import json as _json
import uuid
import shutil
import hashlib
import threading
import subprocess
import time
import math
import html

# A client vanishing is normal, not an error. Media elements abort constantly:
# seeking, swapping source, closing a tab. socket.timeout is only an alias of
# TimeoutError from 3.10 on, so name both.
GONE = (ConnectionResetError, BrokenPipeError, ConnectionAbortedError,
        TimeoutError, socket.timeout)

PORT = 8000
# Listen on every interface so a phone or laptop on the same wifi can reach it.
# There is no authentication, so anyone on that network can drive the queue and
# watch what's cached. Set REEL_HOST=127.0.0.1 to go back to this machine only.
HOST = os.environ.get("REEL_HOST", "0.0.0.0")
DL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reel_downloads")
os.makedirs(DL, exist_ok=True)
# Deliberately not inside DL: everything in there is either a video or something
# restore() tries to reattach to a job, and it all counts against the cache cap.
# A ratings dump is neither, and should not be able to evict a film.
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reel_cache")
os.makedirs(CACHE_DIR, exist_ok=True)

GB = 1_000_000_000  # decimal GB, matching what Finder displays

# Rolling cache. When the folder goes over the cap, finished files are deleted
# oldest-first (by last play, falling back to mtime). The file currently being
# streamed and any file whose job is still working are never touched.
CACHE_CAP_GB = 15.0
CAP_LOCK = threading.Lock()

# How many downloads run at once. Pasting 50 links should not spawn 50 rclones.
WORKERS = 2

# Torrents are handed to webtorrent-cli, which already does piece prioritisation
# for streaming. Its own HTTP server defaults to 8000, which is ours, so we always
# assign it a free port explicitly.
WT_PORTS = (8801, 8899)         # range we hand out
WT_META_TIMEOUT = 75            # seconds to wait for magnet metadata
WT_SERVER_WAIT = 45             # seconds to wait for its http server to appear
# How long to wait for the swarm to hand over a first few MB before deciding
# nothing is coming. Reading an endpoint that has no data yet burns ffprobe's
# timeout and then produces an empty encode, which used to be reported as
# "couldn't convert the torrent stream" -- blaming the conversion for what was
# really an empty swarm.
WT_DATA_WAIT = 90
WT_DATA_MIN = 2 * 1024 * 1024
# When the first probe learns nothing, how long to keep waiting and how much of
# the file to want before asking again. Not a format threshold -- the first 4 MB
# of that mp4 identifies itself perfectly once those bytes exist. The problem is
# a starved swarm: the pieces holding the header had not arrived and could not be
# fetched inside ffprobe's timeout, so waiting for the download to be genuinely
# moving is what makes the second attempt succeed.
WT_REPROBE_WAIT = 60
WT_REPROBE_MIN = 24 * 1024 * 1024
VIDEO_EXT = (".mp4", ".mkv", ".avi", ".mov", ".m4v", ".webm", ".ts", ".flv", ".wmv",
             ".mpg", ".mpeg", ".m2ts")
AUDIO_EXT = (".mp3", ".m4a", ".flac", ".wav", ".aac", ".ogg", ".opus")

# A torrent holding several films or episodes becomes several queue items, one
# per file, rather than one item and a pile of bytes nothing can reach.
# REEL_PACK=1 restores the old behaviour of taking only the largest file.
# 50 covers a full season of most things, and two of some. Files past the limit
# are dropped silently today -- see fan_out.
try:
    PACK_MAX = max(1, int(os.environ.get("REEL_PACK", "50")))
except ValueError:
    PACK_MAX = 50
# What counts as a feature rather than an extra. A sample, a trailer or a
# "please seed" clip is always a small fraction of the real thing, so a file has
# to be both absolutely and relatively substantial to earn its own row --
# otherwise a film with three extras becomes four items, three of them junk.
# Deliberately loose, because the name check below is the precise instrument and
# this is only a backstop. Tightening it to exclude bonus material instead cost
# real files: an uneven trilogy, or a season with one double-length episode,
# has smaller entries that are still whole features.
PACK_MIN_SHARE = 0.20
PACK_MIN_BYTES = 50 * 1024 * 1024
# Bonus material is named as such by convention, and a size bar alone lets the
# larger of it through: a 1.9 GB "behind the scenes" beside an 8 GB feature is
# a quarter of it, which no threshold loose enough to keep a short episode can
# also exclude. The name is the more precise signal.
PACK_EXTRAS = re.compile(r"""(sample|trailer|teaser|extras?|bonus|featurette|
    behind[ ._-]?the[ ._-]?scenes|deleted[ ._-]?scenes?|making[ ._-]?of|
    interview|blooper|outtake|gag[ ._-]?reel|commentary|proof|screener)""",
    re.I | re.X)

# Search. One indexer to begin with, behind a normalising layer so another can
# be added without the caller noticing. These endpoints go dark without warning
# -- yts.mx already refuses the requests this was first written against -- so a
# dead source has to read as "no results", never as a broken feature.
# Three indexers, because one is not enough: against an independent source,
# apibay was missing 10-12 viable torrents per film -- including a 195-seeder
# Dune release that would have ranked near the top. They are queried together
# and merged on infohash. Any one of them going dark has to read as "that source
# returned nothing", never as a broken search: yts.mx, which this was first
# written against, has already vanished entirely.
SEARCH_URL = "https://apibay.org/q.php"
SEARCH_CSV_URL = "https://torrents-csv.com/service/search"
SEARCH_RARBG_URL = "https://therarbg.to/get-posts"
# The search response truncates `name` -- at 64 or 80 characters, depending on
# the row -- and a release puts its codec at the *end*, so the one field that
# decides whether this needs remuxing is exactly what gets cut. This endpoint
# returns the real filenames inside the torrent, untruncated.
SEARCH_FILES_URL = "https://apibay.org/f.php"
SEARCH_TIMEOUT = 12
SEARCH_LIMIT = 25               # rows kept after ranking, not rows fetched
# How many top results to look up full filenames for. One request each, so this
# is a straight trade of latency against how many rows can be judged properly.
SEARCH_DETAIL = 10
# A torrent with no seeders cannot transfer a byte, so it is dropped rather than
# offered. Below this it can technically start and still never stream: the magnet
# that prompted this had 2 peers, found its endpoint correctly, and sat at
# 14 KB/s against the ~1.5 MB/s the film needed.
SEARCH_MIN_SEEDERS = 5
# How many top results to verify against the trackers themselves. Each scrape is
# a couple of UDP packets, run in parallel, so this costs about a second -- worth
# it, since the indexer figure it replaces was out by 50x on one row.
SEARCH_VERIFY = 8
# Appended to every magnet we build, since the indexer hands back a bare
# infohash. DHT finds most peers on its own; these only speed up the start.
# Tracker liveness drifts too: the dead ones in that Spider-Man magnet
# (coppersurfer, leechers-paradise, rarbg) are why it took 150s to find
# metadata the first time.
# Every tracker here was scraped and confirmed to answer, rather than trusted
# because it appears on a list: of 47 in the maintained public list, 31 replied
# and 16 did not, and three of the four originally hardcoded here were among the
# dead. Refresh occasionally from github.com/ngosang/trackerslist, testing before
# adopting -- trackers go dark quietly and a dead one costs a timeout every time.
#
# Two lists, because they are used for two different things. Announcing wants
# breadth: each tracker knows only its own slice of a swarm, so the peers found
# are the union, and one reporting six seeders may still hold the six nobody else
# has. Measuring wants the few big ones that answer fastest, since the number we
# want is the largest and a slow tracker just delays the search.
SEARCH_TRACKERS = (
    "udp://tracker.torrent.eu.org:451/announce",
    "udp://open.demonii.com:1337/announce",
    "udp://leet-tracker.moe:1337/announce",
    "udp://tracker.qu.ax:6969/announce",
    "udp://tracker.auctor.tv:6969/announce",
    "udp://tracker.dler.org:6969/announce",
    "udp://bittorrent-tracker.e-n-c-r-y-p-t.net:1337/announce",
    "udp://explodie.org:6969/announce",
    "udp://tracker.0x7c0.com:6969/announce",
    "udp://open.demonoid.ch:6969/announce",
    "udp://evan.im:6969/announce",
    "udp://tracker.peerfect.org:6969/announce",
    "udp://tracker.opentrackr.com:6969/announce",
    "udp://tracker.filemail.com:6969/announce",
    "udp://t.overflow.biz:6969/announce",
    "udp://mail.segso.net:6969/announce",
    "udp://ipv4announce.sktorrent.eu:6969/announce",
    "udp://tracker.gmi.gd:6969/announce",
)

# The subset asked when checking a seeder count: biggest and quickest to reply.
VERIFY_TRACKERS = SEARCH_TRACKERS[:5]

# Recommendations. Search answers "do you have this?"; this answers "what should
# I watch?", which needs a source that is browsable rather than queryable.
# apibay publishes precompiled top-100 lists per category as static json -- no
# query, no rate limit, and they carry the three fields the ranking needs that a
# search result does not: an imdb id, an upload timestamp, and an uploader
# status. 201 is Movies and 207 HD Movies; the television categories are
# deliberately absent, since a feed mixing episode 4 of something into a list of
# films is not a list of films.
FEED_URL = "https://apibay.org/precompiled/data_top100_%d.json"
FEED_CATS = (201, 207)
# The same index also publishes what appeared in the last 48 hours, and it is
# almost entirely disjoint from the all-time lists: 99 of its 100 rows were
# absent from the pool built without it. Without this a "just landed" shelf has
# fourteen candidates and fills itself with whatever was *uploaded* recently,
# which included a 1976 film with five seeders.
FEED_48H_URL = "https://apibay.org/precompiled/data_top100_48h_207.json"
# therarbg lists as well as searches, 50 rows a page and 1250 available. Every
# row is under two days old, so this deepens what is new rather than what is
# old -- the back catalogue still comes from the all-time lists above. Only
# about 40% carry an imdb id, but the title+year merge lends them one when
# another source listed the same film.
FEED_RARBG_URL = "https://therarbg.to/get-posts/category:Movies:format:json/"
FEED_RARBG_PAGES = 6
# Indian cinema never appears in those lists -- zero of 137 films, since they
# rank by global swarm size -- so this shelf has to ask for it by name. Searched
# rather than browsed, through the same three sources search already uses.
FEED_BOLLY_QUERY = "hindi"
# Ratings come from IMDb's own daily dump, which needs no API key -- the same
# reason the subtitle source was chosen. 8.6 MB gzipped, and only ever scanned
# for the ~150 ids the feed actually mentions, so it costs no resident memory:
# holding all 1.7M rows would cost about 20 MB to answer 150 questions.
RATINGS_URL = "https://datasets.imdbws.com/title.ratings.tsv.gz"
RATINGS_MAX_AGE = 86400.0        # the dump is rebuilt daily; no point refetching sooner
RATINGS_TIMEOUT = 90
# The feed changes on the order of hours, so rebuilding it per page load would be
# pure waste -- and every rebuild is ~10 UDP scrapes and two http fetches.
FEED_TTL = 1800.0
FEED_LIMIT = 24
# Rows per shelf, and how many of each get their seeder count measured. Only the
# top of a shelf is checked: the rest show a tilde, exactly as search does, since
# 5 shelves fully verified would be 40 scrapes to draw one page.
try:
    FEED_SHELF = max(1, int(os.environ.get("REEL_SHELF", "12")))
except ValueError:
    FEED_SHELF = 12              # a typo in an env var must not stop the server
# Candidates measured per shelf, which is more than are shown. Indexer counts
# are inflated, and on the gems shelf -- where every row is thinly seeded by
# definition -- rows claiming 100+ measured out at 2 and 4. Verifying only what
# fits the shelf leaves no way to replace those, so a few spares are checked and
# the ones that cannot stream are dropped before trimming.
FEED_VERIFY = 12
# When a shelf comes up short, more candidates are measured rather than the
# shelf being left thin -- Bollywood swarms are a fraction of a global
# release's, so nine of its first twelve were too thin to stream and it drew
# three films. This bounds how many any one shelf may check before giving up.
FEED_MAX_VERIFY = 36
# A film is one film. Anything with this many files is a boxset, a season, or a
# 400-file cartoon collection -- all of which were really in the list, and none
# of which is something to press play on. Measured: legitimate single films top
# out around 6 files (video, subtitles, sample, nfo), collections start at 16.
FEED_PACK_FILES = 12
# Ranking weights. Rating dominates because it is the only factor about the film
# rather than about the torrent; without it the list is just "what is popular
# right now", which is what every other index already shows.
W_RATING, W_RECENT, W_SEEDERS = 0.42, 0.24, 0.22
B_DIRECT, B_TRUSTED = 0.12, 0.04
# Recency blends two different things: when the torrent appeared, and when the
# film came out. Torrent age alone puts a fresh re-upload of a 1998 film above a
# genuinely new release, which is not what "recent" means to someone browsing.
RECENT_TORRENT, RECENT_YEAR = 0.7, 0.3
FEED_HALFLIFE = 60.0             # days; torrent recency decays on this scale
FEED_SEED_FULL = 3000.0          # seeders at which the swarm score saturates
# A bare average is not a rating: 9.2 from 300 votes is noise next to 8.1 from a
# million. Pulling every score toward the global mean in proportion to how few
# votes back it is the standard fix, and it costs one line.
RATING_PRIOR, RATING_PRIOR_VOTES = 6.6, 2000.0
# Shelf thresholds.
GEM_RATING, GEM_SEEDERS = 7.2, 150   # well reviewed, barely seeded
LANDED_DAYS = 30                     # and released this year or last
# Films rated this badly are not recommended. Only applied where a rating
# exists: an unrated film is an unknown, not a bad one. Without it the "just
# landed" shelf offered a film rated 3.2, which is not a recommendation so much
# as a warning.
FLOOR_RATING = 5.0

# Subtitles, from OpenSubtitles' legacy endpoint -- which needs no API key, so
# this works out of the box rather than waiting on credentials.
SUBS_URL = "https://rest.opensubtitles.org/search"
SUBS_LANG = os.environ.get("REEL_SUB_LANG", "eng")   # ISO 639-2, e.g. eng/spa/fre
SUBS_TIMEOUT = 25
SUBS_UA = "reel/1.0"
# The query must be lowercase. Sent with any uppercase, the API 302s to
# "https://_/..." -- a literally unresolvable host -- so the request fails in a
# way that looks exactly like "this film has no subtitles".
# Lines matching this are the uploader's advertising, which OpenSubtitles files
# routinely carry as the first cue or two.
SUBS_SPAM = re.compile(r"osdb\.link|opensubtitles|watch online movies|"
                       r"subtitles? by|api\.OpenSubtitles|www\.[a-z0-9.-]+\.(com|org|net)",
                       re.I)

# Seconds of history the download rate is averaged over. Long enough to ride
# out the gap between one 64 MiB rclone chunk and the next.
RATE_WINDOW = 8.0

# Prefetch: keep this many items warm ahead of what's playing. More than one
# and they compete with the stream for bandwidth.
PREFETCH = 1
# Only prefetch while the playing item has this much rate-to-bitrate margin.
HEADROOM_OK = 1.35
HEADROOM_TIGHT = 1.1
PREFETCH_KBPS = 0          # 0 = unlimited; a cap here also protects the stream
CAN_PAUSE = hasattr(signal, "SIGSTOP")

# Live streaming (phase 1).
LIVE_HEAD = 256 * 1024          # bytes needed before the container can be judged
LIVE_GIVEUP = 64 * 1024 * 1024  # stop trying to identify it after this much
LIVE_OPEN = 32 * 1024           # live output must reach this before we serve it
LIVE_GRACE = 90.0               # keep the live copy this long after the swap
LIVE_IDLE = 45.0                # give up on a live reader starved this long
COMPAT_WAIT = 30.0              # hold a compat request this long for its first
                                # fragment before telling the player to retry

JOBS = {}
LOCK = threading.RLock()
WORK_Q = queue.Queue()

# Jobs with an open /stream response. Never evict these.
STREAMING = {}
STREAM_LOCK = threading.Lock()


# ---- cache accounting --------------------------------------------------------

SIZE_CACHE = {"at": 0.0, "bytes": 0}
SIZE_TTL = 2.0


def folder_size_bytes(max_age=SIZE_TTL):
    """Every byte under DL, including in-progress *_raw temp dirs, so the cap
    reflects what the folder actually costs on disk.

    Memoised for a couple of seconds: this walks the whole cache, and it is
    asked by the janitor every 2s *and* by /sys, which every connected device
    polls. Three phones made it a full stat of several thousand files per
    second, all to answer a number that changes slowly. Pass max_age=0 where the
    answer must be current, as the evictor does between deletions.
    """
    now = time.time()
    if max_age and now - SIZE_CACHE["at"] < max_age:
        return SIZE_CACHE["bytes"]
    total = 0
    for root, _dirs, files in os.walk(DL):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    SIZE_CACHE["at"], SIZE_CACHE["bytes"] = now, total
    return total


def cap_bytes():
    with CAP_LOCK:
        return int(CACHE_CAP_GB * GB)


EVICT_GRACE = 30.0        # don't reclaim something that only just started
PLAY_GRACE = 60.0         # nor what the player is on, between range requests


def job_dirs(jid):
    return [os.path.join(DL, jid + suffix)
            for suffix in ("_wt", "_raw", "_meta", "_probe")]


def in_use(jid):
    """Being read right now, or the thing the player is sitting on.

    The refcount alone isn't enough: a seekable torrent is served as a series of
    separate range requests, so between them the count drops to zero even though
    it is very much in use.
    """
    with STREAM_LOCK:
        if STREAMING.get(jid, 0) > 0:
            return True
    return watching(jid)


def cancel_status(job):
    """Why a worker was stopped decides what the row should say.

    Without this the worker's own cancel handling races the evictor and
    overwrites 'evicted' with 'removed', losing the distinction.
    """
    if job.get("evicted"):
        return "evicted"
    if job.get("overflow"):
        return "error"
    return "removed"


def stop_procs(job):
    for proc in [job.get("proc")] + list(job.get("procs") or []):
        if proc and proc.poll() is None:
            try:
                proc.kill()
            except Exception:
                pass


def evictable():
    """Everything we may reclaim, least valuable first.

    Three kinds, not one:
      * orphaned directories, owned by no job at all -- pure garbage
      * finished files -- Drive's, or a torrent finalized into a seekable copy
      * torrent data directories still seeding, which previously were never
        considered, so a seeding torrent held its bytes forever and the cap
        became impossible to satisfy

    Ordered by last play, which puts never-watched items (a prefetch, say) ahead
    of something watched yesterday.
    """
    now = time.time()
    out = []
    with LOCK:
        live = set(JOBS.keys())
        jobs = list(JOBS.items())

    # 1. orphans: directories whose job is gone (a restart, or a hard exit)
    try:
        for name in os.listdir(DL):
            full = os.path.join(DL, name)
            if not os.path.isdir(full):
                continue
            for suffix in ("_wt", "_raw", "_meta", "_probe"):
                if name.endswith(suffix) and name[:-len(suffix)] not in live:
                    out.append((-1.0, None, full, "dir"))
                    break
    except OSError:
        pass

    for jid, j in jobs:
        if in_use(jid):
            continue
        if now - (j.get("started_at") or 0) < EVICT_GRACE:
            continue
        when = j.get("last_played") or 0.0
        p = j.get("path")
        if j["status"] == "done" and p and os.path.isfile(p):
            # A torrent that needed transcoding ends up here too, once
            # finalize_torrent() replaces its _wt folder with a seekable file --
            # checked first, since that folder won't exist to find below.
            out.append((when or _mtime(p), jid, p, "file"))
        elif j.get("source") == "torrent":
            if j.get("status") == "converting":
                continue          # finalize_torrent() is reading it right now
            d = os.path.join(DL, jid + "_wt")
            if os.path.isdir(d) and tree_bytes(d) > 0:
                out.append((when, jid, d, "dir"))
    out.sort(key=lambda t: t[0])
    return out


def _mtime(p):
    try:
        return os.path.getmtime(p)
    except OSError:
        return 0.0


def enforce_cache_cap():
    """Evict until the folder fits. Returns True if it now fits.

    Evicted jobs stay in the queue marked 'evicted' — the file is gone but the
    Drive id is kept, so the row can be re-fetched with one click.
    """
    cap = cap_bytes()
    if folder_size_bytes() <= cap:
        return True
    for _ts, jid, path, kind in evictable():
        with LOCK:
            j = JOBS.get(jid) if jid else None
        if j is not None:
            # a torrent has to be stopped before its data can go, otherwise it
            # keeps seeding from files that no longer exist
            j["evicted"] = True
            j["cancel"].set()
            stop_procs(j)
        try:
            if kind == "dir":
                shutil.rmtree(path, ignore_errors=True)
            else:
                os.remove(path)
        except OSError:
            continue
        if j is not None:
            lf = j.get("live_file")
            if lf and os.path.exists(lf):
                try:
                    os.remove(lf)
                except OSError:
                    pass
            # A finalized torrent's magnet sidecar (see finalize_torrent) is
            # only useful paired with the file restore() would find it next to;
            # once that file is gone, keeping it would just orphan it.
            mg = os.path.join(DL, jid + ".magnet")
            if os.path.exists(mg):
                try:
                    os.remove(mg)
                except OSError:
                    pass
            j.update(status="evicted", path=None, received=0, total=0,
                     live_file=None, live_ready=False, wt_url=None,
                     wt_direct=False, rate=None, headroom=None, pct=None)
            record(j, "evicted to stay under the %g GB cap" % CACHE_CAP_GB)
        # Measured afresh after every deletion: a cached figure here would still
        # show the file we just removed and we would carry on evicting past the
        # point where the folder already fits.
        if folder_size_bytes(0) <= cap:
            return True
    return folder_size_bytes(0) <= cap


# ---- scheduling: one item warm ahead, using only spare bandwidth -------------

# Where each device is up to, keyed by the client id the page generates. One
# global entry was enough while this only served localhost, but on a network two
# people watch two different things: with a single slot the second viewer's item
# looks unwatched, and the evictor is free to delete the file underneath them.
PLAYING = {}
PLAY_LOCK = threading.Lock()


def note_playing(cid, jid, at):
    if not cid:
        return
    now = time.time()
    with PLAY_LOCK:
        PLAYING[cid] = {"id": jid, "at": at, "seen": now}
        for k in [k for k, v in PLAYING.items() if now - v["seen"] > 3600]:
            del PLAYING[k]


def viewers(ttl=15.0):
    """Everyone still watching, most recently heard from first."""
    now = time.time()
    with PLAY_LOCK:
        live = [dict(v) for v in PLAYING.values() if now - v["seen"] < ttl]
    return sorted(live, key=lambda v: -v["seen"])


def watching(jid, ttl=None):
    """Is any device sitting on this item?"""
    ttl = PLAY_GRACE if ttl is None else ttl
    return any(v["id"] == jid for v in viewers(ttl))


def viewer_count(jid):
    """How many devices are on this item right now, this one included.

    Counts only devices actively playing: the page reports its position as it
    plays, so a paused or backgrounded one ages out within seconds. That is the
    honest reading -- someone who paused ten minutes ago is not watching.
    """
    return sum(1 for v in viewers() if v["id"] == jid)


def playhead(jid):
    """The furthest-along position among everyone watching this item.

    Furthest, because that viewer has the least downloaded ahead of them, and a
    buffer figure is only useful if it describes whoever is closest to running
    out.
    """
    at = [v["at"] for v in viewers() if v["id"] == jid]
    return max(at) if at else 0.0
ACTIVE = ("downloading", "converting", "fetching metadata", "starting",
          "connecting", "streaming")


def stream_health(job):
    """How comfortably the playing item is keeping ahead of playback.

    'ok'      -> plenty of margin, safe to prefetch
    'tight'   -> keeping up, but barely; hold the prefetch
    'behind'  -> arriving slower than it plays; it will stall
    'unknown' -> no bitrate yet
    """
    if job is None:
        return "unknown"
    if (job.get("status") == "done" or job.get("path") or job.get("wt_done")):
        return "ok"                              # all of it is already local
    if job.get("status") == "converting":
        # The source is already fully downloaded; only the re-encode matters.
        cs = job.get("conv_speed")
        if cs is None:
            return "unknown"
        return "behind" if cs < 1.0 else ("tight" if cs < 1.15 else "ok")
    # A transcoded stream can be network-fine and still stall, because ffmpeg
    # is the bottleneck rather than the swarm.
    es = job.get("encode_speed")
    if es is not None:
        # The encoder reads through the download, so it already accounts for the
        # network: starve it of bytes and its speed falls. Believing it over the
        # byte counter matters because that counter moves in 64 MiB steps -- one
        # step can take 20 seconds, and every sample in between reads as 0 B/s,
        # which used to announce a stall in the middle of a 15 MB/s transfer.
        return "behind" if es < 1.0 else ("tight" if es < 1.15 else "ok")
    h = job.get("headroom")
    if h is None:
        return "unknown"
    return "ok" if h >= HEADROOM_OK else ("tight" if h >= HEADROOM_TIGHT else "behind")


def buffered_seconds(job):
    """Seconds of media downloaded ahead of the playhead."""
    if job.get("status") == "converting":
        return None                      # whole source is already local
    bps = job.get("bitrate") or 0
    if bps <= 0:
        return None
    have = (job.get("received") or 0) * 8 / bps
    return max(0.0, round(have - playhead(job["id"]), 1))


def scheduler():
    """Starts queued items, keeps PREFETCH of them warm ahead of the one being
    watched, and suspends a prefetch whenever the stream needs the bandwidth."""
    while True:
        time.sleep(1.0)
        try:
            with LOCK:
                order = list(JOBS.values())
            # Everything being watched right now, freshest viewer first. A
            # client that has gone quiet drops out of viewers() on its own.
            seen_ids, watched = [], []
            for vw in viewers():
                if vw["id"] and vw["id"] not in seen_ids:
                    seen_ids.append(vw["id"])
                    j = next((x for x in order if x["id"] == vw["id"]), None)
                    if j:
                        watched.append(j)
            playing = watched[0] if watched else None
            active = [j for j in order if j["status"] in ACTIVE]
            queued = [j for j in order if j["status"] == "queued" and j.get("hold")]
            # The worst of what anyone is watching. A prefetch that would be fine
            # for one viewer can still be what stalls the other.
            grades = [stream_health(j) for j in watched] or ["unknown"]
            health = next((g for g in ("behind", "tight", "ok", "unknown")
                           if g in grades), "unknown")

            # 1. nothing playing and nothing running: start the first item
            if not active and queued:
                release(queued[0])
                continue

            # 2. suspend or resume prefetches according to the stream's margin
            for j in order:
                if not j.get("prefetch") or j["status"] not in ACTIVE:
                    continue
                want_paused = health in ("tight", "behind")
                if want_paused and not j.get("paused"):
                    if pause_proc(j.get("wt_proc") or j.get("proc"), True):
                        j["paused"] = True
                        j["note"] = "paused so the stream keeps up"
                elif not want_paused and j.get("paused"):
                    if pause_proc(j.get("wt_proc") or j.get("proc"), False):
                        j["paused"] = False
                        j["note"] = "prefetching"

            # 3. start the next item once the stream has room to spare
            if playing is None or health not in ("ok", "unknown"):
                continue
            running_pf = sum(1 for j in order
                             if j.get("prefetch") and j["status"] in ACTIVE)
            if running_pf >= PREFETCH:
                continue
            try:
                after = order.index(playing)
            except ValueError:
                after = -1
            nxt = next((j for j in order[after + 1:]
                        if j["status"] == "queued" and j.get("hold")), None)
            if nxt:
                nxt["prefetch"] = True
                nxt["note"] = "prefetching"
                release(nxt)
        except Exception:
            pass


def release(job):
    """Hand a held job to the workers."""
    job["hold"] = False
    job["started_at"] = time.time()
    WORK_Q.put(job["id"])


def janitor():
    """Keeps the cap honest *during* transfers, not just after them. If we're
    over cap with nothing left to evict, the newest still-growing download is
    stopped so a single oversized file can't fill the disk.

    'converting' is deliberately excluded from that last resort. A conversion
    is actively *freeing* disk -- finalize_torrent() is about to delete a raw
    download several times the size of what it produces -- so killing it is
    self-defeating: it destroys completed work and delays the very space this
    is trying to reclaim. The temporary overlap while it runs (raw + in-progress
    output + a live copy, all at once) is exactly what pushes the folder over
    cap in the first place, and it resolves itself within a couple of minutes
    once the conversion finishes on its own.
    """
    while True:
        time.sleep(2.0)
        try:
            if folder_size_bytes() <= cap_bytes():
                continue
            if enforce_cache_cap():
                continue
            with LOCK:
                active = [j for j in JOBS.values() if j["status"] == "downloading"]
            if active:
                victim = active[-1]
                victim["cancel"].set()
                victim["overflow"] = True
        except Exception:
            pass


# ---- helpers -----------------------------------------------------------------

MAGNET_RE = re.compile(r"magnet:\?[^\s\"'<>]+", re.I)
BTIH_RE = re.compile(r"xt=urn:btih:([0-9a-fA-F]{40}|[A-Za-z2-7]{32})")


def subs_path_for(jid, lang=None):
    """Dotted, like .live. and .compat., so restore()'s three-part __ parse
    cannot mistake a sidecar for a finished download and resurrect it as a job."""
    return os.path.join(DL, "%s.subs.%s.vtt" % (jid, lang or SUBS_LANG))


def osdb_hash(path):
    """OpenSubtitles' file hash: the size, plus 64-bit little-endian sums of the
    first and last 64 KiB. Identifies the exact release, so the subtitles come
    back timed to this cut rather than to some other rip of the same film."""
    CHUNK = 65536
    try:
        size = os.path.getsize(path)
        if size < CHUNK * 2:
            return None, size
        h = size
        with open(path, "rb") as f:
            for offset in (0, size - CHUNK):
                f.seek(offset)
                buf = f.read(CHUNK)
                if len(buf) < CHUNK:
                    return None, size
                for i in range(0, CHUNK, 8):
                    h = (h + struct.unpack("<q", buf[i:i + 8])[0]) & 0xFFFFFFFFFFFFFFFF
        return "%016x" % h, size
    except (OSError, struct.error):
        return None, 0


def subs_get(url, timeout=SUBS_TIMEOUT):
    req = urllib.request.Request(url, headers={"User-Agent": SUBS_UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def subs_search(moviehash=None, size=0, name=None, lang=None):
    """Candidates for this file, best first.

    Tried by hash before name: a hash match is the same release, where a name
    match is often a different rip whose timings drift. Ranked by download
    count, which is the only quality signal the endpoint offers.
    """
    lang = lang or SUBS_LANG
    attempts = []
    if moviehash and size:
        attempts.append(("moviehash", "moviehash-%s/moviebytesize-%d" % (moviehash, size)))
    if name:
        # Lowercased deliberately -- see SUBS_LANG notes above; uppercase gets a
        # 302 to an unresolvable host and reads as "no subtitles found".
        stem = os.path.splitext(os.path.basename(name))[0].lower()
        attempts.append(("name", "query-" + urllib.parse.quote(stem)))
    for how, sel in attempts:
        url = "%s/%s/sublanguageid-%s" % (SUBS_URL, sel, lang)
        try:
            rows = _json.loads(subs_get(url).decode("utf-8", "replace"))
        except Exception:
            continue
        if not isinstance(rows, list) or not rows:
            continue
        rows = [r for r in rows if isinstance(r, dict) and r.get("SubDownloadLink")
                and (r.get("SubFormat") or "srt").lower() in ("srt", "vtt", "sub")]
        if not rows:
            continue

        def dls(r):
            try:
                return int(r.get("SubDownloadsCnt") or 0)
            except (TypeError, ValueError):
                return 0
        rows.sort(key=dls, reverse=True)
        return rows, how
    return [], None


def hhmmss(text):
    """'02:08:40' -> seconds, or None."""
    parts = str(text or "").strip().split(":")
    if not (2 <= len(parts) <= 3):
        return None
    try:
        vals = [float(p) for p in parts]
    except ValueError:
        return None
    while len(vals) < 3:
        vals.insert(0, 0.0)
    return vals[0] * 3600 + vals[1] * 60 + vals[2]


# Words that say which cut and which source a release is, and therefore whether
# one set of timings will suit another.
RELEASE_TOKENS = re.compile(
    r"\b(2160p|1080p|720p|480p|bluray|blu-ray|bdrip|brrip|bdremux|remux|web-?dl|"
    r"webrip|web|hdtv|hddvd|hd-dvd|dvdrip|cam|extended|theatrical|directors?|"
    r"remastered|imax|unrated|proper|repack)\b", re.I)


def subs_fit(cand, our_name, our_duration=None, matched_by=None):
    """How well one candidate suits the file we actually have.

    Returns (score, reasons). A hash match needs none of this -- it is the same
    bytes, so the timings are the file's own. A name match is the risky case: a
    search for a 1080p BrRip returns a 720p HD-DVD as its most-downloaded
    result, which is the same film from a different source, and different
    sources cut and frame differently.
    """
    score, why = 0.0, []
    if (cand.get("SubBad") or "0") == "1":
        return -100.0, ["flagged bad by uploaders"]
    if matched_by == "moviehash" or (cand.get("MatchedBy") or "") == "moviehash":
        return 100.0, ["exact file match"]

    # Duration is the strongest evidence available without the hash: subtitles
    # for a different cut stop minutes away from where this film ends. The last
    # cue normally lands a little before the end, never after it by much.
    last = hhmmss(cand.get("SubLastTS"))
    if our_duration and last:
        gap = our_duration - last
        if -120 <= gap <= 600:
            score += 40
            why.append("ends %s before the film does" % clock_short(max(gap, 0)))
        else:
            # Decisive, not a penalty to be weighed. Subtracting a fixed amount
            # let the popularity bonus buy the difference back: a subtitle 94
            # minutes out of sync scored -48 against a -50 threshold and was
            # accepted. Nothing about a download count makes wrong timings fit.
            return -100.0, ["timings end %s out" % clock_short(abs(gap))]

    # Which source it was cut from. Shared words mean shared structure.
    ours = {t.lower() for t in RELEASE_TOKENS.findall(our_name or "")}
    theirs = {t.lower() for t in RELEASE_TOKENS.findall(
        (cand.get("MovieReleaseName") or "") + " " + (cand.get("SubFileName") or ""))}
    if ours and theirs:
        shared = ours & theirs
        score += 12 * len(shared) - 6 * len(ours ^ theirs)
        if shared:
            why.append("same " + "/".join(sorted(shared)))
        diff = sorted(ours ^ theirs)
        if diff:
            why.append("differs on " + "/".join(diff[:3]))

    if (cand.get("SubFromTrusted") or "0") == "1":
        score += 8
    try:
        score += min(int(cand.get("SubDownloadsCnt") or 0) / 50000.0, 10)
    except (TypeError, ValueError):
        pass
    return score, why


def clock_short(seconds):
    s = int(max(0, seconds or 0))
    return "%dm%02ds" % (s // 60, s % 60) if s >= 60 else "%ds" % s


def strip_subs_spam(text):
    """Drop the uploader's advertising cues, keeping the actual dialogue."""
    out, dropped = [], 0
    for block in re.split(r"\n\s*\n", text):
        body = "\n".join(block.strip().splitlines()[2:])   # past index + timing
        if body and SUBS_SPAM.search(body) and len(body) < 200:
            dropped += 1
            continue
        if block.strip():
            out.append(block.strip())
    return "\n\n".join(out) + "\n", dropped


def install_subs(job, cand, lang=None):
    """Fetch one candidate and leave a WebVTT sidecar. Returns True on success.

    Converted with ffmpeg rather than by hand because these files arrive in
    whatever encoding the uploader used -- CP1252 is common -- and ffmpeg is
    already a hard requirement, so this costs nothing extra.
    """
    lang = lang or SUBS_LANG
    dest = subs_path_for(job["id"], lang)
    tmp = dest + ".srt"
    try:
        raw = subs_get(cand["SubDownloadLink"])
        if raw[:2] == b"\x1f\x8b":                  # gzip, which it always is
            raw = gzip.decompress(raw)
        if not raw.strip():
            return False
        with open(tmp, "wb") as f:
            f.write(raw)
        enc = (cand.get("SubEncoding") or "").strip()
        cmd = ["ffmpeg", "-nostdin", "-y", "-hide_banner", "-loglevel", "error"]
        if enc and enc.upper() not in ("UTF-8", "UTF8"):
            cmd += ["-sub_charenc", enc]
        cmd += ["-i", tmp, dest]
        r = subprocess.run(cmd, capture_output=True, timeout=60)
        if r.returncode != 0 or not os.path.exists(dest) or not os.path.getsize(dest):
            job["subs_note"] = tail(r.stderr, 2, 160)
            return False
        with open(dest, encoding="utf-8", errors="replace") as f:
            text = f.read()
        cleaned, dropped = strip_subs_spam(text)
        if cleaned.count("-->") > 0:
            with open(dest, "w", encoding="utf-8") as f:
                f.write(cleaned if cleaned.startswith("WEBVTT")
                        else "WEBVTT\n\n" + cleaned)
        job["subs_cues"] = cleaned.count("-->")
        job["subs_spam_dropped"] = dropped
        return True
    except Exception as e:
        job["subs_note"] = "%s: %s" % (type(e).__name__, str(e)[:120])
        return False
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


def start_subs(job, src, name=None):
    """Look for subtitles for a release, in the background.

    `src` must be the release as downloaded -- not reel's remux of it, whose
    bytes hash to nothing anyone has seen. Hashing is two 64 KiB reads and is
    done up front, so the caller is free to delete the file immediately after.
    """
    # An exact match cannot be improved on, and a search already running should
    # not be duplicated. Otherwise a *later* call carrying a real file is allowed
    # through even when something was already found: the early call can only look
    # up by name, and a hash match beats it.
    if job.get("subs_exact") or job.get("subs_status") == "searching":
        return
    have = job.get("subs_status") == "ready"
    if have and not (src and os.path.isfile(src)):
        return
    if not have and os.path.exists(subs_path_for(job["id"])):
        job.update(subs_status="ready", subs_lang=SUBS_LANG)
        return
    moviehash, size = osdb_hash(src) if src and os.path.isfile(src) else (None, 0)
    title = name or (os.path.basename(src) if src else None) or job.get("title")
    job["subs_status"] = "searching"

    def work():
        try:
            rows, how = subs_search(moviehash, size, title)
            # Ranked by how well each suits *this* file, not by popularity. The
            # most-downloaded result for a 1080p BrRip was a 720p HD-DVD rip,
            # which is a different source and drifts.
            scored = []
            for cand in rows:
                s, why = subs_fit(cand, title, job.get("duration"), how)
                if s > -50:
                    scored.append((s, why, cand))
            scored.sort(key=lambda t: -t[0])
            for s, why, cand in scored[:3]:   # a top pick can be a dead link
                if job["cancel"].is_set():
                    break
                if install_subs(job, cand):
                    job.update(subs_status="ready", subs_source=how,
                               subs_lang=SUBS_LANG,
                               subs_fit=round(s, 1),
                               subs_exact=bool(s >= 100),
                               subs_why="; ".join(why)[:160],
                               subs_name=cand.get("SubFileName", "")[:120])
                    record(job, "subtitles: %s match by %s, fit %.0f (%s)"
                           % ("exact" if s >= 100 else "judged", how, s,
                              cand.get("SubFileName", "")[:80]))
                    return
            # A failed upgrade attempt must not throw away what we already have.
            job["subs_status"] = "ready" if have else "unavailable"
            if rows and not scored and not have:
                job["subs_note"] = "found %d, none matched this cut" % len(rows)
            record(job, "subtitles: %d candidate(s) by %s, none usable"
                   % (len(rows or []), how))
        except Exception as e:
            job["subs_status"] = "ready" if have else "unavailable"
            job["subs_note"] = "%s: %s" % (type(e).__name__, str(e)[:120])
            record(job, "subtitle search failed: %s: %s"
                   % (type(e).__name__, str(e)[:120]))
    threading.Thread(target=work, daemon=True).start()


def read_release(name):
    """What a release name tells us about how this file will actually play.

    Guesswork, but useful guesswork, and it is the difference between a choice
    made blind and one made informed. An x264 release satisfies the wt_direct
    test: webtorrent's own ranged stream goes straight to the browser, no
    encoder involved and nothing extra written to disk. An x265 one has to be
    remuxed once it lands, and an HDR one will look flat unless ffmpeg has
    zscale. None of that is visible on a torrent site, because it depends on
    this machine rather than the file.
    """
    n = " " + (name or "").lower().replace(".", " ").replace("_", " ") + " "
    hevc = bool(re.search(r"\b(x265|h ?265|hevc)\b", n))
    h264 = bool(re.search(r"\b(x264|h ?264|avc)\b", n))
    av1 = bool(re.search(r"\bav1\b", n))
    res = None
    for pat, label in ((r"\b(2160p|4k|uhd)\b", "2160p"), (r"\b1080p\b", "1080p"),
                       (r"\b720p\b", "720p"), (r"\b(480p|sd)\b", "480p")):
        if re.search(pat, n):
            res = label
            break
    hdr = bool(re.search(r"\b(hdr|hdr10|dolby ?vision|dv)\b", n))
    # Only h264 is in BROWSER_VIDEO *and* reliably 8-bit here. AV1 is in that
    # set too, but 10-bit AV1 is common enough that claiming "direct" would be
    # wrong often; unknown codecs stay unclaimed rather than over-promise.
    codec = "hevc" if hevc else "h264" if h264 else "av1" if av1 else None
    # The container decides as much as the codec. An h264 .mkv cannot play in a
    # browser at all, so calling it "plays directly" would send someone to a
    # file that just refuses. Only judged when the real filename was found --
    # the truncated search name usually has no extension, and treating unknown
    # as bad would mark almost everything as needing a remux.
    # Only a *recognised* media extension says anything about the container.
    # Release names are dotted, so splitext happily returns ".h264-kyogo" or
    # ".hevc" as the extension -- neither is a container, and treating them as
    # unplayable ones marked every dotted h264 release as needing a remux when
    # the real-filename lookup came back empty.
    ext = os.path.splitext(name or "")[1].lower()
    known = ext in VIDEO_EXT + AUDIO_EXT
    container_ok = (ext in BROWSER_CONTAINERS) if known else True
    return {"codec": codec, "res": res, "hdr": hdr, "container": ext or None,
            "direct": codec == "h264" and not hdr and container_ok}


def search_real_name(tid, timeout=6):
    """The largest filename inside a torrent, or None.

    Worth one extra request per row because the truncated search name loses the
    codec, and the codec is the difference between "streams as-is" and "costs a
    remux and twice the disk". Picks the largest file, since that is the one
    pick_file() will choose to play.
    """
    try:
        url = SEARCH_FILES_URL + "?" + urllib.parse.urlencode({"id": tid})
        req = urllib.request.Request(url, headers={"User-Agent": "reel/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            rows = _json.loads(r.read().decode("utf-8", "replace"))
    except Exception:
        return None

    # Two shapes come back from the same endpoint, seemingly at random:
    #   {"name": {"0": "a.mkv"}, "size": {"0": "123"}}   -- index-keyed maps
    #   {"name": ["a.mkv"],      "size": [123]}          -- plain lists
    # and either may carry several entries. Flattening both to a list keeps the
    # pairing between a name and its size, which matters because the largest
    # file is the one pick_file() will play -- taking the first instead picked
    # "NEW upcoming releases by Xclusive.txt" as the name to judge a film by.
    def values(v):
        if isinstance(v, dict):
            return [v[k] for k in sorted(v, key=lambda x: str(x))]
        if isinstance(v, list):
            return v
        return [] if v is None else [v]

    best, best_size = None, -1
    for row in rows if isinstance(rows, list) else []:
        if not isinstance(row, dict):
            continue
        names, sizes = values(row.get("name")), values(row.get("size"))
        for i, nm in enumerate(names):
            if not isinstance(nm, (str, int, float)):
                continue
            nm = str(nm).strip()
            # Sentinel for torrents whose file list this index never stored.
            if not nm or nm.lower() == "filelist not found":
                continue
            try:
                size = int(sizes[i]) if i < len(sizes) else 0
            except (TypeError, ValueError):
                size = 0
            if size > best_size:
                best, best_size = nm, size
    # A name is only worth trusting if it belongs to something big enough to be
    # the feature: a .txt or .jpg tells us nothing about the video's codec.
    if best and best.lower().endswith(VIDEO_EXT + AUDIO_EXT):
        return best
    return best if best_size > 50_000_000 else None


def build_magnet(infohash, name):
    parts = ["magnet:?xt=urn:btih:" + infohash.lower()]
    if name:
        parts.append("dn=" + urllib.parse.quote_plus(name))
    parts += ["tr=" + urllib.parse.quote(t) for t in SEARCH_TRACKERS]
    return "&".join(parts)


def udp_scrape(infohash, tracker, timeout=4.0):
    """Ask a tracker how many seeders a torrent actually has.

    Indexer counts are cached and wildly optimistic -- measured against this,
    they overstated by about 2x across the board, and in one case reported 203
    seeders for a torrent with 4. That is precisely the torrent that looks safe
    and then never streams, so the number worth showing is this one.

    BEP 15: connect for a connection id, then scrape with it.
    """
    host, _, port = tracker.partition("://")[2].partition("/")[0].rpartition(":")
    try:
        raw = binascii.unhexlify(infohash)
        if len(raw) != 20:
            return None
        addr = (host, int(port))
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(timeout)
        try:
            tid = random.randint(0, 2 ** 31)
            s.sendto(struct.pack(">QII", 0x41727101980, 0, tid), addr)
            data, _ = s.recvfrom(512)
            action, rtid, cid = struct.unpack(">IIQ", data[:16])
            if action != 0 or rtid != tid:
                return None
            tid2 = random.randint(0, 2 ** 31)
            s.sendto(struct.pack(">QII", cid, 2, tid2) + raw, addr)
            data, _ = s.recvfrom(512)
            if len(data) < 20 or struct.unpack(">I", data[:4])[0] != 2:
                return None
            seeders, _done, _leech = struct.unpack(">III", data[8:20])
            return seeders
        finally:
            s.close()
    except Exception:
        return None


def live_seeders(infohash, timeout=3.0):
    """The best count any of our trackers will admit to, or None if none answer.

    Highest rather than lowest across trackers: each knows only its own slice of
    a swarm, so the largest answer is the closest to the whole.

    All of them at once, because most will not answer at all -- three of the four
    time out from here -- and asking in turn made one search take 14 seconds
    waiting on trackers that were never going to reply.
    """
    found = []
    def ask(tr):
        got = udp_scrape(infohash, tr, timeout)
        if got is not None:
            found.append(got)
    for tr in VERIFY_TRACKERS:
        threading.Thread(target=ask, args=(tr,), daemon=True).start()
    # Returns shortly after the first answer instead of waiting out the ones that
    # never reply. Those took the full timeout every time, which made a search of
    # eight rows sit for three seconds and put 32 requests in flight at once --
    # enough for the trackers that do work to start refusing them.
    deadline = time.time() + timeout + 0.5
    while time.time() < deadline:
        if found:
            time.sleep(0.35)          # brief grace, in case a second is close behind
            break
        time.sleep(0.05)
    return max(found) if found else None


def _search_json(url, timeout=SEARCH_TIMEOUT):
    req = urllib.request.Request(url, headers={"User-Agent": "reel/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return _json.loads(r.read().decode("utf-8", "replace"))


def _row(ih, name, seeders, leechers, size, files=0, tid="", imdb=""):
    """One shape for every source, so the ranking never has to know which
    indexer a result came from.

    imdb is carried through even though search itself never displays it: it is
    what lets a searched row be rated, and dropping it here left the whole
    Bollywood shelf unrated while the id sat in the response all along.
    """
    ih = (ih or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", ih) or set(ih) == {"0"}:
        return None
    name = (name or "").strip()
    if not name:
        return None
    def num(v):
        try:
            return max(0, int(float(v or 0)))
        except (TypeError, ValueError):
            return 0
    imdb = str(imdb or "")
    return {"infohash": ih, "name": name, "id": str(tid or ""),
            "seeders": num(seeders), "leechers": num(leechers),
            "size": num(size), "files": num(files),
            "imdb": imdb if imdb.startswith("tt") else "",
            "magnet": build_magnet(ih, name)}


def source_apibay(query):
    """The Pirate Bay's json api. Returns rows already sorted by seeders, and
    caps at 100 -- which costs nothing, since what it drops is the tail."""
    url = SEARCH_URL + "?" + urllib.parse.urlencode({"q": query, "cat": 200})
    rows = _search_json(url)
    out = []
    for r in rows if isinstance(rows, list) else []:
        if not isinstance(r, dict) or r.get("id") in ("0", 0):
            continue          # the no-results sentinel row
        out.append(_row(r.get("info_hash"), r.get("name"), r.get("seeders"),
                        r.get("leechers"), r.get("size"), r.get("num_files"),
                        r.get("id"), r.get("imdb")))
    return [x for x in out if x]


def source_csv(query):
    """torrents-csv: an aggregated dataset, and the source that demonstrated the
    gap -- 10-12 torrents per film that apibay simply does not list."""
    url = SEARCH_CSV_URL + "?" + urllib.parse.urlencode({"q": query, "size": 100})
    data = _search_json(url)
    rows = data.get("torrents", []) if isinstance(data, dict) else data
    out = []
    for r in rows if isinstance(rows, list) else []:
        if not isinstance(r, dict):
            continue
        out.append(_row(r.get("infohash"), r.get("name"), r.get("seeders"),
                        r.get("leechers"), r.get("size_bytes")))
    return [x for x in out if x]


def source_rarbg(query):
    """therarbg, RARBG's successor. Keys are abbreviated -- h hash, n name,
    se seeders, le leechers, s size -- and it needs its redirect followed."""
    url = "%s/keywords:%s:format:json/" % (SEARCH_RARBG_URL,
                                           urllib.parse.quote(query))
    data = _search_json(url)
    rows = data.get("results", []) if isinstance(data, dict) else data
    out = []
    for r in rows if isinstance(rows, list) else []:
        if not isinstance(r, dict):
            continue
        out.append(_row(r.get("h"), r.get("n"), r.get("se"), r.get("le"),
                        r.get("s")))
    return [x for x in out if x]


SEARCH_SOURCES = (("apibay", source_apibay), ("torrents-csv", source_csv),
                  ("therarbg", source_rarbg))


def search_all(query):
    """Every source at once, merged on infohash. Returns (rows, per_source).

    Run in parallel because three sequential lookups would treble the wait, and
    each is wrapped so one being dead or reshaped costs only its own results --
    per_source records what each contributed, so a source that quietly stops
    working is visible rather than guessed at.
    """
    got, per = {}, {}

    def fetch(name, fn):
        try:
            rows = fn(query)
            per[name] = len(rows)
        except Exception as e:
            per[name] = "failed: " + str(e)[:40]
            return
        for r in rows:
            old = got.get(r["infohash"])
            if old is None:
                r["counts"] = [r["seeders"]]
                got[r["infohash"]] = r
            else:
                # Every count each source gave, kept so the merge can take a
                # middle value rather than the most flattering one.
                old["counts"].append(r["seeders"])
                if r["size"] and not old["size"]:
                    old["size"] = r["size"]
                if len(r["name"]) > len(old["name"]):
                    old["name"] = r["name"]
                if r["id"] and not old["id"]:
                    old["id"] = r["id"]
                if r.get("imdb") and not old.get("imdb"):
                    old["imdb"] = r["imdb"]     # only apibay supplies one

    threads = [threading.Thread(target=fetch, args=(n, f), daemon=True)
               for n, f in SEARCH_SOURCES]
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT + 4)

    # Indexer seeder counts disagree wildly, and are all cached rather than
    # live. One torrent came back as 109, 487 and 1313 from the three sources
    # while the tracker itself reported 283. Taking the highest -- which this
    # first did -- reliably picks the stalest, most flattering number, which is
    # the opposite of useful when the whole point of ranking by seeders is to
    # avoid a dead swarm. The middle value is the one that survives an outlier
    # in either direction.
    for r in got.values():
        c = sorted(r.pop("counts", [r["seeders"]]))
        # Lower median, so two sources resolve to the smaller figure rather than
        # the larger. Erring low is the right direction here: an overstated count
        # invites a stall, an understated one only makes a good torrent look
        # slightly worse than it is.
        r["seeders"] = c[(len(c) - 1) // 2]
        r["sources"] = len(c)
    return list(got.values()), per


def search_torrents(query, limit=SEARCH_LIMIT):
    """Find magnets by name. Returns (results, error).

    Ranked by seeders above all else, because a dead swarm is the one failure
    no amount of local cleverness recovers from -- the 2-peer magnet earlier
    found its endpoint correctly and still could not stream a byte.
    """
    q = (query or "").strip()
    if not q:
        return [], "nothing to search for", 0, {}
    rows, per_source = search_all(q)
    if not rows:
        alive = [n for n, v in per_source.items() if isinstance(v, int)]
        if not alive:
            # Every source failed, which is a different thing from "no results"
            # and deserves to be said as such.
            return [], "no search source could be reached (%s)" % "; ".join(
                "%s %s" % (n, v) for n, v in per_source.items())[:120], 0, per_source
        return [], None, 0, per_source

    out = []
    dropped = 0                 # zero-seeder rows, reported so their absence
                                # is visible rather than silent
    for row in rows:
        size = row["size"]
        seeders = row["seeders"]
        # Nothing to serve the file, so there is nothing to offer. Dropped here
        # rather than shown greyed out, because on an obscure search these can
        # be the entire result set -- one search returned 19 rows of which 6
        # had exactly zero seeders, sorted indistinguishably among the rest.
        if seeders <= 0:
            dropped += 1
            continue
        out.append(row)          # already normalised by _row()

    out.sort(key=lambda r: (-r["seeders"], r["size"]))
    out = out[:limit]

    # Two lookups per candidate, both in parallel: the real filename, and the
    # seeder count from the trackers rather than from an indexer's cache.
    def enrich(res, verify):
        if res["id"]:
            real = search_real_name(res["id"])
            if real:
                res["real_name"] = real
        if verify:
            live = live_seeders(res["infohash"])
            if live is not None:
                res["reported"] = res["seeders"]
                res["seeders"] = live
                res["verified"] = True
    threads = [threading.Thread(target=enrich,
                                args=(r, i < SEARCH_VERIFY), daemon=True)
               for i, r in enumerate(out[:max(SEARCH_DETAIL, SEARCH_VERIFY)])]
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT)

    # Re-rank on the verified numbers, since verification can move a row a long
    # way -- one claiming 203 seeders turned out to have 4, and belongs at the
    # bottom rather than in the middle of the list.
    #
    # An unverified row is ranked on half of what its indexer claimed, because
    # that is roughly how much they overstate (1085 against 485, 487 against 289,
    # 447 against 123). Without the haircut a row nobody could check outranks
    # rows measured to be better, purely for being optimistic.
    out.sort(key=lambda r: (-(r["seeders"] if r.get("verified")
                              else r["seeders"] // 2), r["size"]))

    # The zero-seeder filter above ran on what the indexers claimed, which is the
    # only figure available at that point. Verification then contradicts some of
    # them: a search for one film left three rows sitting in the list showing
    # "0 seed" because they claimed more before being checked. Drop them now that
    # the truth is known, rather than offering a torrent measured to be dead.
    before = len(out)
    out = [r for r in out if not (r.get("verified") and r["seeders"] <= 0)]
    dropped += before - len(out)

    cap = cap_bytes()
    for res in out:
        # Judge the real filename when we have it, since the search name is
        # missing whatever fell off the end -- usually the codec.
        info = read_release(res.get("real_name") or res["name"])
        # What this will actually cost on disk, which is not the same as its
        # size. A direct stream is served from the download itself, so it costs
        # exactly that. Anything needing a remux holds the source and the output
        # at once while converting -- the overlap that put a 8.6 GB film 20 GB
        # over a 15 GB cap and got its conversion killed mid-run. An unknown
        # codec is costed as if it needs one: better to warn and be wrong than
        # to promise and stall.
        res["peak"] = res["size"] if info["direct"] else int(res["size"] * 2.05)
        res["fits"] = res["peak"] <= cap
        # Enough of a swarm to actually stream. Kept as a flag rather than a
        # filter: a handful of seeders may still be the only copy of something
        # obscure, and downloading it slowly is a legitimate choice -- being
        # surprised by it is not.
        res["weak"] = res["seeders"] < SEARCH_MIN_SEEDERS
        res.setdefault("verified", False)
        res.setdefault("reported", None)
        res.update(info)
    return out, None, dropped, per_source


# Release names carry the title, but buried in the encoding vocabulary. Cutting
# at the first of these tokens is what separates "Toy Story 5" from
# "Toy.Story.5.2026.1080p.WEB-DL.DDP5.1.H264-GROUP".
FEED_STOP = re.compile(r"""\b(1080p|720p|2160p|480p|576p|4k|uhd|web[- ]?dl|webrip|
    webscr|bluray|brrip|bdrip|hdrip|dvdrip|dvdscr|hdts|hdcam|camrip|cam|telesync|
    hdtv|x264|x265|h ?264|h ?265|hevc|avc|av1|xvid|divx|aac|ac3|dd5|ddp5|dts|
    truehd|atmos|10bit|8bit|sdr|hdr10?|dolby|vision|remux|extended|unrated|proper|
    repack|internal|amzn|nf|dsnp|hmax|atvp|imax|multi|dual|subs?)\b""",
    re.I | re.X)
FEED_YEAR = re.compile(r"[\(\[\.\s_-]((?:19|20)\d{2})[\)\]\.\s_-]")
FEED_PACK = re.compile(r"""\b(collection|boxset|box ?set|complete|seasons?|duology|
    trilogy|quadrilogy|anthology|mega ?pack|movie pack|filmography)\b""", re.I | re.X)
FEED_EPISODE = re.compile(r"\bS\d{1,2}(E\d{1,2}|\b)", re.I)
# Filmed off a cinema screen, or an unfinished review copy. These rank well --
# new, heavily seeded, and too recent to have collected a rating that would drag
# them down -- so three of the top twelve were camcorder recordings. Recommending
# one is worse than recommending nothing, though search still finds them, which
# is where you would go having decided you want one.
FEED_CAM = re.compile(r"""\b(cam|camrip|hdcam|hqcam|ts|telesync|hdts|tc|hdtc|
    telecine|scr|screener|dvdscr|bdscr|workprint|predvd)\b""", re.I | re.X)
# A Hollywood film carrying a Hindi audio track is not Indian cinema, and it is
# most of what a search for "hindi" returns. Both markers are needed: "dual
# audio" and "multi" name the packaging, while a run of other language tags is
# what a multi-language remux looks like.
FEED_DUB = re.compile(r"\b(dual ?audio|multi|dubbed|dub)\b", re.I)
FEED_OTHER_LANG = re.compile(r"\b(fre|ita|spa|ger|lat|rus|kor|jpn|chi|por|tur|vf2)\b",
                             re.I)


def _words(name):
    """Release names separate on dots as often as spaces."""
    return " " + (name or "").lower().replace(".", " ").replace("_", " ") + " "


def feed_cam(name):
    """Whether this is a camcorder recording or a screener."""
    return bool(FEED_CAM.search(_words(name)))


def feed_dubbed(name):
    """Whether this looks like a foreign film carrying a Hindi track."""
    w = _words(name)
    return bool(FEED_DUB.search(w) or FEED_OTHER_LANG.search(w))


def feed_title(name):
    """A film's title and year, dug out of a release name. Returns (title, year).

    The year is taken as the *last* plausible one, not the first, because a title
    can contain a number that looks like one -- "Blade Runner 2049.HDRip.XviD"
    parsed left to right gives the title "Blade Runner" and the year 2049. Any
    year past next year is a title, not a date, which is the rule that fixes it.
    """
    # Some listings hand back html-escaped names, and the entity survives just
    # far enough to be visible: "Shake Rattle &amp; Roll" reached the shelf as
    # "Shake Rattle&amp Roll", the semicolon having been stripped as punctuation.
    n = html.unescape(name or "").replace("_", " ")
    limit = time.gmtime().tm_year + 1
    m = None
    for hit in FEED_YEAR.finditer(" " + n + " "):
        if int(hit.group(1)) <= limit:
            m = hit
    year = int(m.group(1)) if m else None
    head = (" " + n + " ")[:m.start()] if m else n
    head = FEED_STOP.split(head.replace(".", " "))[0]
    head = re.sub(r"[\(\[\{].*", " ", head)          # "(2026) [1080p]" and friends
    head = re.sub(r"[^0-9A-Za-z':&!,\- ]+", " ", head)
    return re.sub(r"\s+", " ", head).strip(" -:"), year


def feed_pack(name, files):
    """Whether this is a collection rather than a film.

    The file count arrives as an int from the precompiled lists and as a string
    from the search endpoint -- the same field, the same api, two types -- so it
    is coerced rather than compared. Left alone this raises TypeError on every
    search-sourced row.
    """
    try:
        count = int(files or 0)
    except (TypeError, ValueError):
        count = 0
    return count >= FEED_PACK_FILES or bool(
        FEED_PACK.search(name or "") or FEED_EPISODE.search(name or ""))


def _norm_title(t):
    return re.sub(r"[^a-z0-9]", "", (t or "").lower())


def ratings_file():
    """The IMDb ratings dump on disk, refetched only when stale.

    A failed refresh keeps yesterday's copy rather than discarding it: a rating
    a day old is worth far more than no rating, and this is the only part of the
    feed that depends on a host we do not otherwise talk to.
    """
    path = os.path.join(CACHE_DIR, "imdb-ratings.tsv.gz")
    try:
        fresh = os.path.exists(path) and (time.time() - os.path.getmtime(path)) < RATINGS_MAX_AGE
    except OSError:
        fresh = False
    if fresh:
        return path
    tmp = path + ".part"
    try:
        req = urllib.request.Request(RATINGS_URL, headers={"User-Agent": "reel/1.0"})
        with urllib.request.urlopen(req, timeout=RATINGS_TIMEOUT) as r, open(tmp, "wb") as f:
            shutil.copyfileobj(r, f)
        os.replace(tmp, path)                 # never a half-written file in place
    except Exception:
        try:
            os.remove(tmp)
        except OSError:
            pass
        return path if os.path.exists(path) else None
    return path


def ratings_for(ids):
    """{tconst: (rating, votes)} for just the ids asked about.

    Streamed and matched against a set rather than loaded into a dict, because
    the dump holds 1.7M titles and the feed asks about ~150 of them.
    """
    want = {i for i in ids if i}
    if not want:
        return {}
    path = ratings_file()
    if not path:
        return {}
    out = {}
    try:
        with gzip.open(path, "rt", encoding="utf-8", errors="replace") as f:
            f.readline()                      # header
            for line in f:
                tid = line.split("\t", 1)[0]
                if tid in want:
                    parts = line.rstrip("\n").split("\t")
                    if len(parts) >= 3:
                        try:
                            out[tid] = (float(parts[1]), int(parts[2]))
                        except ValueError:
                            pass
                    if len(out) == len(want):
                        break                 # nothing left to find
    except (OSError, EOFError, gzip.BadGzipFile):
        return out                            # truncated dump: partial beats none
    return out


def feed_fetch():
    """Raw rows from every feed list at once. Returns (rows, per_source)."""
    rows, per = [], {}
    lock = threading.Lock()

    def grab(label, url):
        try:
            got = _search_json(url)
        except Exception as e:
            with lock:
                per[label] = "failed: " + str(e)[:40]
            return
        got = [r for r in got if isinstance(r, dict)] if isinstance(got, list) else []
        with lock:
            per[label] = len(got)
            rows.extend(got)

    def grab_rarbg():
        try:
            got = rarbg_browse()
        except Exception as e:
            with lock:
                per["therarbg"] = "failed: " + str(e)[:40]
            return
        with lock:
            per["therarbg"] = len(got)
            rows.extend(got)

    lists = [(str(c), FEED_URL % c) for c in FEED_CATS] + [("48h", FEED_48H_URL)]
    threads = [threading.Thread(target=grab, args=(n, u), daemon=True)
               for n, u in lists]
    threads.append(threading.Thread(target=grab_rarbg, daemon=True))
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT + 8)
    return rows, per


def rarbg_browse(pages=FEED_RARBG_PAGES):
    """therarbg's movie listing, reshaped to look like a precompiled row.

    Its keys are abbreviated the same way its search is -- h hash, n name, se
    seeders, s size, a added, i imdb -- and it pages rather than returning
    everything, so the pages are fetched together and flattened.
    """
    rows, lock = [], threading.Lock()

    def page(n):
        url = FEED_RARBG_URL + ("?page=%d" % n if n > 1 else "")
        try:
            data = _search_json(url)
        except Exception:
            return                      # one dead page is not a dead source
        got = data.get("results", []) if isinstance(data, dict) else data
        out = []
        for r in got if isinstance(got, list) else []:
            if not isinstance(r, dict):
                continue
            out.append({"info_hash": r.get("h"), "name": r.get("n"),
                        "seeders": r.get("se"), "leechers": r.get("le"),
                        "size": r.get("s"), "added": r.get("a"),
                        "imdb": r.get("i") or "",
                        # The listing does not say how many files a torrent
                        # holds, so packs are caught by name alone here.
                        "num_files": 1, "status": ""})
        with lock:
            rows.extend(out)

    threads = [threading.Thread(target=page, args=(n,), daemon=True)
               for n in range(1, max(1, pages) + 1)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT + 4)
    return rows


def bolly_fetch():
    """Indian cinema, which the browse lists never carry. Returns (rows, per).

    Reuses search rather than adding a source: the three indexers already behind
    search_all between them list far more of this than any one of them does.
    Shaped to look like a browse row so the rest of the pipeline cannot tell the
    difference -- the browse lists carry an imdb id and an upload time that a
    search result does not, so both are supplied as blanks.
    """
    try:
        found, per = search_all(FEED_BOLLY_QUERY)
    except Exception as e:
        return [], {"hindi": "failed: " + str(e)[:40]}
    rows = []
    for r in found:
        if feed_dubbed(r["name"]):
            continue
        rows.append({"info_hash": r["infohash"], "name": r["name"],
                     "seeders": r["seeders"], "leechers": r["leechers"],
                     "size": r["size"], "num_files": r.get("files") or 1,
                     "added": 0, "status": "", "imdb": r.get("imdb") or ""})
    return rows, {("hindi/" + k): v for k, v in per.items()}


def rating_score(rating, votes):
    """A vote-weighted rating in 0..1, or None when there is no rating.

    None rather than a default, because a missing rating is a thing we do not
    know, and substituting the average would let an unrated film pass itself off
    as an average one.
    """
    if not rating:
        return None
    v = max(0, votes or 0)
    weighted = ((v / (v + RATING_PRIOR_VOTES)) * rating
                + (RATING_PRIOR_VOTES / (v + RATING_PRIOR_VOTES)) * RATING_PRIOR)
    return max(0.0, min(1.0, weighted / 10.0))


def feed_score(item, now=None):
    """How strongly to recommend this. Returns (score, why).

    An unrated film scores as exactly average, which is what the vote-weighting
    already does with zero votes -- it falls back to the prior. Dropping the
    factor and averaging the rest was tried first and is subtly wrong: it scores
    an unknown film on its *best* remaining signals, so two films nobody has
    rated took the top two places over one rated 8.2. Not knowing something is
    not evidence in its favour.
    """
    now = now or time.time()
    why = []
    q = rating_score(item.get("rating"), item.get("votes"))
    if q is None:
        q = RATING_PRIOR / 10.0
        why.append("no rating found")
    else:
        why.append("rated %.1f from %s votes" % (item["rating"], f"{item['votes']:,}"))

    added = item.get("added") or 0
    year = item.get("year")
    this_year = time.gmtime(now).tm_year
    year_rec = 1.0 if not year else max(0.0, min(1.0, 1.0 - (this_year - year) / 6.0))
    age_days = max(0.0, (now - added) / 86400.0) if added else None
    if age_days is None:
        # A search result carries no upload time. Guessing "just now" hands every
        # one of them the full bonus; guessing "long ago" denies it; and falling
        # back to the film's year turns the shelf into a list of this year's
        # releases, which buried 3 Idiots and Gangs of Wasseypur under four
        # unrated 2026 obscurities. Unknown scores as neutral, so the ranking
        # falls to what we do know -- the rating and the swarm.
        rec = 0.5
    else:
        rec = RECENT_TORRENT * math.exp(-age_days / FEED_HALFLIFE) + RECENT_YEAR * year_rec
        if age_days <= 14:
            why.append("posted %d days ago" % round(age_days))

    seeders = max(0, item.get("seeders") or 0)
    seed = min(1.0, math.log10(max(1, seeders)) / math.log10(FEED_SEED_FULL))
    if seeders >= 500:
        why.append("%d seeders" % seeders)

    score = W_RATING * q + W_RECENT * rec + W_SEEDERS * seed

    if item.get("direct"):
        score += B_DIRECT
        why.append("plays without converting")
    if item.get("status") in ("vip", "trusted"):
        score += B_TRUSTED
    return score, why


FEED_CACHE = {"at": 0.0, "rows": [], "sources": {}, "error": None}
FEED_LOCK = threading.Lock()


def feed_pool(raw):
    """Raw index rows -> one scored, deduplicated entry per film.

    Shared by every shelf, including the Bollywood one, so a film is judged the
    same way regardless of which list it arrived on.
    """
    items = []
    for r in raw:
        name = (r.get("name") or "").strip()
        ih = (r.get("info_hash") or "").strip().lower()
        if not name or not re.fullmatch(r"[0-9a-f]{40}", ih):
            continue
        files = r.get("num_files") or 1
        if feed_pack(name, files) or feed_cam(name):
            continue
        title, year = feed_title(name)
        if not title:
            continue
        try:
            added = int(r.get("added") or 0)
        except (TypeError, ValueError):
            added = 0
        imdb = r.get("imdb") or ""
        items.append({"infohash": ih, "name": name, "title": title, "year": year,
                      "imdb": imdb if imdb.startswith("tt") else "",
                      "seeders": max(0, int(r.get("seeders") or 0)),
                      "leechers": max(0, int(r.get("leechers") or 0)),
                      "size": max(0, int(r.get("size") or 0)),
                      "files": files, "added": added,
                      "status": r.get("status") or "",
                      "magnet": build_magnet(ih, name)})

    rated = ratings_for({i["imdb"] for i in items})
    for i in items:
        i["rating"], i["votes"] = rated.get(i["imdb"], (None, 0))
        i["direct"] = read_release(i["name"])["direct"]

    def better(a, b):
        # One release per film, and the one worth offering is the one that will
        # actually play: a direct 1080p beats a marginally better-seeded x265
        # that costs a remux and twice the disk.
        return (a["direct"], a["seeders"]) > (b["direct"], b["seeders"])

    # Two passes. An imdb id is the reliable key, but 30 of 200 rows carry none,
    # so a second pass on title+year collapses what the first could not see --
    # otherwise the same film appears twice, once with a rating and once without.
    best = {}
    for i in items:
        key = i["imdb"] or ("t:" + _norm_title(i["title"]) + str(i["year"]))
        if key not in best or better(i, best[key]):
            best[key] = i
    merged = {}
    for i in best.values():
        key = _norm_title(i["title"]) + str(i["year"] or "")
        prev = merged.get(key)
        if prev is None:
            merged[key] = i
            continue
        keep, drop = (i, prev) if better(i, prev) else (prev, i)
        if keep["rating"] is None and drop["rating"] is not None:
            keep = dict(keep, rating=drop["rating"], votes=drop["votes"],
                        imdb=drop["imdb"])
        merged[key] = keep

    now = time.time()
    rows = list(merged.values())
    for r in rows:
        r["score"], r["why"] = feed_score(r, now)
        r.setdefault("verified", False)
        r.setdefault("reported", None)
    rows.sort(key=lambda r: -r["score"])
    return rows


def feed_dress(rows):
    """What each row costs and whether it can be served, once it is on a shelf."""
    cap = cap_bytes()
    for r in rows:
        info = read_release(r["name"])
        r["peak"] = r["size"] if info["direct"] else int(r["size"] * 2.05)
        r["fits"] = r["peak"] <= cap
        r["weak"] = r["seeders"] < SEARCH_MIN_SEEDERS
        r.update(info)
    return rows


def feed_verify(rows, now=None):
    """Measure the seeder counts of rows about to be shown.

    The indexer's figure is a cache and overstates by roughly 2x, so the ones
    being offered are checked against the trackers. Only the top of each shelf:
    the rest keep their tilde, as in search.
    """
    now = now or time.time()

    def check(res):
        live = live_seeders(res["infohash"])
        if live is not None:
            res["reported"] = res["seeders"]
            res["seeders"] = live
            res["verified"] = True
    threads = [threading.Thread(target=check, args=(r,), daemon=True) for r in rows]
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT)
    for r in rows:
        if r.get("verified"):
            r["score"], r["why"] = feed_score(r, now)
    # A measured-dead swarm cannot serve a byte, so it is not a recommendation.
    return [r for r in rows if not (r.get("verified") and r["seeders"] <= 0)]


def gem(r):
    """Well reviewed and barely seeded: the films no index will ever surface,
    because they rank by exactly the quantity these are short of."""
    return bool(r["rating"] and rating_score(r["rating"], r["votes"])
                and r["rating"] >= GEM_RATING and r["seeders"] < GEM_SEEDERS)


def landed(r, now=None):
    """Out recently *and* uploaded recently.

    Upload time alone is not newness: it put a 1976 film with five seeders at
    the top of the shelf, because someone had posted it that morning.
    """
    now = now or time.time()
    if not r.get("added"):
        return False
    fresh = (now - r["added"]) / 86400.0 <= LANDED_DAYS
    return fresh and (r.get("year") or 0) >= time.gmtime(now).tm_year - 1


# Order matters: a film lands on the first shelf that wants it, so the ones
# earlier in this list get first pick. Hidden gems sits above "plays instantly"
# because a well-reviewed obscurity is a better thing to be told about than a
# convenient one.
SHELVES = (
    ("Tonight", "the best of everything on offer", lambda r, now: True),
    ("Just landed", "out now, and new to the index", landed),
    ("Hidden gems", "well reviewed, barely seeded", lambda r, now: gem(r)),
    ("Plays instantly", "no conversion, starts immediately",
     lambda r, now: bool(r.get("direct"))),
)


def build_shelves():
    """Every shelf, filled in order. Returns (shelves, error, sources)."""
    raw, per = feed_fetch()
    bolly_raw, bolly_per = bolly_fetch()
    per.update(bolly_per)
    if not raw and not bolly_raw:
        alive = [n for n, v in per.items() if isinstance(v, int)]
        if not alive:
            return [], "could not reach the recommendation source", per
        return [], None, per

    now = time.time()

    def watchable(rows):
        return [r for r in rows
                if not (r["rating"] and r["rating"] < FLOOR_RATING)]

    pool = watchable(feed_pool(raw))
    # Built separately so the browse lists cannot crowd it out: these films have
    # a fraction of the seeders of a global release, so on one combined ranking
    # not one of them would ever place.
    bolly = watchable(feed_pool(bolly_raw))

    built, used = {}, set()

    def fill(name, note, rows):
        queue = [r for r in rows if r["infohash"] not in used]
        kept, checked = [], 0
        # Measured in batches, refilling only while the shelf is short. A shelf
        # whose first twelve all survive costs one batch; one whose candidates
        # keep measuring dead pays for the extra rounds it actually needs.
        while queue and len(kept) < FEED_SHELF and checked < FEED_MAX_VERIFY:
            batch = queue[:FEED_VERIFY]
            del queue[:FEED_VERIFY]
            checked += len(batch)
            for r in batch:
                used.add(r["infohash"])
            # Too thin to stream. Search keeps these behind a warning, because
            # there you asked for that specific film; a recommendation has no
            # such excuse, and offering a 2-seeder swarm as something to watch
            # tonight is worse than offering one film fewer.
            kept += [r for r in feed_verify(batch, now)
                     if not (r.get("verified") and r["seeders"] < SEARCH_MIN_SEEDERS)]
        if not kept:
            return
        kept.sort(key=lambda r: -r["score"])
        built[name] = {"name": name, "note": note,
                       "films": feed_dress(kept[:FEED_SHELF])}

    # Filled before the general shelves so they cannot take the few films it
    # has. A Hindi release rarely wins a general ranking, but that is a fact
    # about swarm size rather than about the film.
    fill("Bollywood", "Hindi-language cinema", bolly)
    for name, note, want in SHELVES:
        fill(name, note, [r for r in pool if want(r, now)])

    # Shown headline-first, which is not the order they were filled in: what
    # needed protecting and what deserves the top of the page are different
    # questions. A shelf that came up empty is omitted rather than shown bare.
    order = [n for n, _, _ in SHELVES] + ["Bollywood"]
    return [built[n] for n in order if n in built], None, per


def recommendations(force=False):
    """Cached feed. Rebuilt at most every FEED_TTL, since it moves in hours."""
    with FEED_LOCK:
        fresh = (time.time() - FEED_CACHE["at"]) < FEED_TTL
        if fresh and FEED_CACHE["rows"] and not force:
            return FEED_CACHE["rows"], FEED_CACHE["error"], FEED_CACHE["sources"]
        try:
            rows, err, per = build_shelves()
        except Exception as e:
            # Never a broken page: a dead source reads as an empty shelf.
            rows, err, per = [], "%s: %s" % (type(e).__name__, str(e)[:120]), {}
        if rows or not FEED_CACHE["rows"]:
            FEED_CACHE.update(at=time.time(), rows=rows, error=err, sources=per)
        return FEED_CACHE["rows"], FEED_CACHE["error"], FEED_CACHE["sources"]


def split_sources(text):
    """Pull magnets out first, then treat what's left as Drive links.

    Magnets can't be split on commas the way link lists can -- tracker lists
    inside the uri contain them -- so they're extracted whole by regex.
    """
    text = text or ""
    magnets = []
    for m in MAGNET_RE.finditer(text):
        uri = m.group(0)
        if BTIH_RE.search(uri):
            magnets.append(uri)
    rest = MAGNET_RE.sub(" ", text)
    ids = []
    bad = 0
    for tok in re.split(r"[\s,]+", rest):
        if not tok.strip():
            continue
        # a bare infohash is a valid torrent id too
        if re.fullmatch(r"[0-9a-fA-F]{40}", tok.strip()):
            magnets.append("magnet:?xt=urn:btih:" + tok.strip().lower())
            continue
        did = extract_id(tok)
        if did:
            ids.append(did)
        else:
            bad += 1
    return magnets, ids, bad


def infohash(magnet):
    m = BTIH_RE.search(magnet or "")
    return m.group(1).lower() if m else ""


def free_port(): 
    return free_port_excluding(set())


def free_port_excluding(skip):
    """A port webtorrent can have. Never ours -- its default is 8000, same as
    this server, and a collision makes it fail to start rather than complain."""
    for cand in range(*WT_PORTS):
        if cand == PORT or cand in skip:
            continue
        with LOCK:
            taken = {j.get("wt_port") for j in JOBS.values()}
        if cand in taken:
            continue
        try:
            with socket.socket() as t:
                t.bind(("127.0.0.1", cand))
            return cand
        except OSError:
            continue
    return None


# Interfaces that are not the local network however they are addressed: VPN and
# other tunnels. An address on one of these is reachable from inside the tunnel
# and nowhere else, which is no use to a phone on the same wifi.
TUNNEL_IFACES = ("utun", "ipsec", "ppp", "tun", "tap", "wg", "gpd", "zt")


def lan_ip():
    """This machine's address on the local network, for the QR code and banner.

    Read from the interfaces rather than inferred from a route. The inference --
    connect a UDP socket somewhere and see which local address the OS picks --
    is what a VPN quietly breaks: with one up it returned the tunnel address
    (10.5.1.147) while the wifi was on 192.168.0.193, so the QR code and the
    printed url pointed somewhere no phone could reach. It also assumed the
    gateway was 192.168.1.1, which stops being true the moment the router hands
    out a different subnet.
    """
    try:
        out = subprocess.run(["ifconfig", "-a"], capture_output=True, text=True,
                             timeout=6).stdout
    except Exception:
        out = ""
    iface, best = None, []
    for line in out.splitlines():
        if line and not line[0].isspace():
            iface = line.split(":", 1)[0]
            continue
        m = re.match(r"\s+inet (\d+\.\d+\.\d+\.\d+)", line)
        if not m or not iface:
            continue
        ip = m.group(1)
        if ip.startswith("127.") or iface.startswith(TUNNEL_IFACES):
            continue
        # Ordinary private ranges first, since that is what a home network hands
        # out; anything else only if there is nothing better.
        rank = 0 if ip.startswith(("192.168.", "10.", "172.")) else 1
        best.append((rank, iface, ip))
    if best:
        best.sort()
        return best[0][2]
    # Last resort: the old inference, better than nothing on a platform where
    # ifconfig is absent.
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("192.168.1.1", 9))
            return s.getsockname()[0]
    except OSError:
        return None


def has_webtorrent():
    return bool(shutil.which("webtorrent"))


HAS_QRCODE = None


def has_qrcode():
    """The one optional pip dependency this file has. Checked lazily and cached,
    like HAS_ZSCALE below -- so a machine without it installed never fails to
    start, it just doesn't get the QR button in the header."""
    global HAS_QRCODE
    if HAS_QRCODE is None:
        try:
            import qrcode  # noqa: F401
            HAS_QRCODE = True
        except ImportError:
            HAS_QRCODE = False
    return HAS_QRCODE


def lan_url():
    """The address the QR code and startup banner both point at, or None if
    there's nothing on the LAN worth sharing."""
    if HOST == "127.0.0.1":
        return None
    ip = lan_ip()
    return f"http://{ip}:{PORT}" if ip else None


def qr_svg(url):
    """A scannable SVG for `url`. Verified against an independent decoder
    (jsQR) before this shipped, for both a plain IP and a .local hostname --
    see 2026-07-29-qrcode-design.md.
    """
    import io
    import qrcode
    import qrcode.image.svg
    qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                       box_size=8, border=3,
                       image_factory=qrcode.image.svg.SvgPathImage)
    qr.add_data(url)
    qr.make(fit=True)
    buf = io.BytesIO()
    qr.make_image().save(buf)
    return buf.getvalue()


def extract_id(raw):
    s = raw.strip()
    if not s:
        return None
    for p in (r"/file/d/([a-zA-Z0-9_-]{10,})", r"[?&]id=([a-zA-Z0-9_-]{10,})",
              r"/d/([a-zA-Z0-9_-]{10,})"):
        m = re.search(p, s)
        if m:
            return m.group(1)
    if re.fullmatch(r"[a-zA-Z0-9_-]{20,}", s):
        return s
    return None


def has_rclone():
    if not shutil.which("rclone"):
        return False
    try:
        out = subprocess.run(["rclone", "listremotes"], capture_output=True,
                             text=True, timeout=10)
        return "gdrive:" in out.stdout
    except Exception:
        return False


def has_ffmpeg():
    """ffprobe is needed too — is_audio_only() depends on it."""
    return bool(shutil.which("ffmpeg")) and bool(shutil.which("ffprobe"))


def tail(text, lines=4, chars=280):
    """Last few meaningful lines. Accepts bytes as well as str: subprocess
    stderr arrives as bytes whenever the process was opened with text=False,
    and this being strict crashed the reporting path -- which then hid the very
    ffmpeg error it was trying to show.
    """
    if isinstance(text, (bytes, bytearray)):
        text = text.decode("utf-8", "replace")
    keep = [l for l in (text or "").splitlines() if l.strip()][-lines:]
    return "\n".join(keep)[-chars:]


# How many events a job remembers. A download that probes, stalls, converts and
# fetches subtitles produces a few dozen; the cap only bites on something
# pathological, and the oldest is the right end to lose.
JOB_LOG_MAX = 300


def record(job, msg):
    """Add one line to a job's timeline.

    job["note"] holds only the most recent thing that happened, so the sequence
    that actually explains a stuck download -- what it probed, what it decided,
    when it stopped moving -- was overwritten as fast as it was produced. The
    difference this makes is between reading what happened and dumping the
    server's state to infer it.

    Appending to a list is atomic under the GIL, so this is safe to call from
    the workers, the janitor, the ffmpeg readers and the request threads without
    taking LOCK -- which matters, because several callers already hold it.
    """
    if job is None:
        return
    log = job.get("log")
    if log is None:
        return
    log.append({"t": round(time.time(), 3), "m": str(msg)[:400]})
    if len(log) > JOB_LOG_MAX:
        del log[:-JOB_LOG_MAX]


def new_job(drive_id, jid=None, **extra):
    job = {"id": jid or uuid.uuid4().hex[:12], "drive_id": drive_id,
           "path": None, "total": 0, "received": 0, "status": "queued",
           "error": "", "title": drive_id or "recovered", "kind": "video",
           "cancel": threading.Event(), "proc": None, "procs": [],
           "last_played": None, "overflow": False, "log": [],
           # live phase: streamable is None until the header has been read
           "hold": True, "prefetch": False, "paused": False, "rate": None,
           "bitrate": None, "duration": None, "headroom": None, "eta": None,
           "peers": None, "uploaded": None, "up_rate": None,
           "source": "drive", "magnet": None, "wt_port": None, "wt_url": None,
           "wt_proc": None, "wt_done": False, "wt_ranges": False,
           "wt_codecs": "", "wt_files": 0, "wt_direct": False,
           # Which file of a multi-file torrent this item is. None means "not
           # decided yet"; a pack's siblings are pinned to theirs.
           "wt_index": None,
           "caps": None, "vcodec": None, "vpix": None, "play_key": None,
           "live_proc": None,
           "subs_status": None, "subs_source": None, "subs_lang": None,
           "subs_note": "", "subs_name": "", "subs_cues": None,
           "subs_fit": None, "subs_exact": False, "subs_why": "",
           "compat_file": None, "compat_path": None, "compat_proc": None,
           "compat_seekable_path": None, "compat_ready": False,
           "compat_done": False, "compat_pct": None, "compat_note": "",
           "streamable": None, "live_file": None, "live_kind": None,
           "live_ready": False, "live_done": False, "live_note": "", "note": "",
           "dl_done": False}
    job.update(extra)
    return job


def public(job):
    return {"id": job["id"], "title": job["title"], "status": job["status"],
            "total": job["total"], "received": job["received"],
            "kind": job.get("kind", "video"), "error": job.get("error", ""),
            "replayable": bool(job.get("drive_id") or job.get("magnet")),
            "live": bool(job.get("live_ready") and job.get("live_file")),
            "live_kind": job.get("live_kind"),
            # diagnostics: why live did or didn't happen
            "streamable": job.get("streamable"),
            "live_bytes": (os.path.getsize(job["live_file"])
                           if job.get("live_file") and os.path.exists(job["live_file"]) else None),
            "live_done": job.get("live_done"),
            "live_note": job.get("live_note", ""),
            # False once we know the index is at the end of the file. None on a
            # job restored from disk, which never ran a live phase -- reporting
            # False there made an unrelated file look live-capable.
            "needs_full": (None if job.get("restored") else
                           job.get("streamable") is False),
            "restored": bool(job.get("restored")),
            "note": job.get("note", ""),
            # Only the count here. /jobs is polled every second, and shipping a
            # few hundred events per job on every poll to render a panel that
            # is usually closed would be the most expensive thing on the wire.
            "log_n": len(job.get("log") or ()),
            "probe_log": job.get("probe_log", ""),
            "timings": job.get("timings", {}),
            "url_log": job.get("url_log", ""),
            "rate": int(job.get("rate") or 0) or None,
            "bitrate": job.get("bitrate"),
            "headroom": job.get("headroom"),
            "health": stream_health(job) if job.get("status") in ACTIVE else None,
            "buffered": buffered_seconds(job),
            "eta": job.get("eta"),
            "peers": job.get("peers"),
            "uploaded": job.get("uploaded"),
            "up_rate": job.get("up_rate"),
            "encode_speed": job.get("encode_speed"),
            "conv_pct": job.get("conv_pct"),
            "conv_speed": job.get("conv_speed"),
            # What the finished file holds, so the player can tell whether it
            # needs to ask for the compat rendition instead.
            "viewers": viewer_count(job["id"]),
            "subs": bool(job.get("subs_status") == "ready"
                         and os.path.exists(subs_path_for(
                             job["id"], job.get("subs_lang")))),
            "subs_status": job.get("subs_status"),
            "subs_source": job.get("subs_source"),
            "subs_lang": job.get("subs_lang"),
            "subs_name": job.get("subs_name", ""),
            "subs_note": job.get("subs_note", ""),
            # exact = same bytes, so the timings are the file's own; anything
            # else is a judged fit and may drift
            "subs_exact": bool(job.get("subs_exact")),
            "subs_why": job.get("subs_why", ""),
            "play_key": job.get("play_key"),
            "compat_ready": bool(job.get("compat_ready")),
            "compat_pct": job.get("compat_pct"),
            # the compat rendition has reached its seekable form
            "compat_seekable": bool(job.get("compat_path")
                                    and os.path.isfile(job["compat_path"])),
            # torrents know their exact size from the .torrent, so progress can
            # be a real percentage rather than an animation
            "pct": (round(min(100.0, job["received"] * 100.0 / job["total"]), 1)
                    if job.get("total") and job.get("received") else None),
            "complete": bool(job.get("wt_done") or job.get("status") == "done"),
            "prefetch": bool(job.get("prefetch")),
            "paused": bool(job.get("paused")),
            "queued": bool(job.get("hold")),
            "duration": job.get("duration"),
            "source": job.get("source", "drive"),
            # what *we* serve, not what upstream supports: a transcoded torrent
            # goes out as fragments and cannot be seeked
            "seekable": bool(job.get("path") or job.get("wt_direct")),
            "codecs": job.get("wt_codecs", "")}


# ---- restore across restarts -------------------------------------------------
# Output files are named  {jobid}__{driveid}__{title}.{ext}  so a restart can
# rebuild the queue instead of leaving orphaned files nothing points at.

def playable(path):
    """Can a decoder actually read this file?

    A conversion killed part-way leaves an mp4 whose index was never written,
    which restore() would otherwise hand to the player as ready.
    """
    if not shutil.which("ffprobe"):
        return True                 # no way to tell; assume it's fine
    return stream_kind(path) is not None


def restore():
    for name in os.listdir(DL):
        p = os.path.join(DL, name)
        if os.path.isdir(p):
            if name.endswith(("_raw", "_meta", "_probe")):
                shutil.rmtree(p, ignore_errors=True)   # scratch, never useful
            elif name.endswith("_wt"):
                # resume it if we know what it was; otherwise it's dead weight
                info = None
                try:
                    with open(os.path.join(p, ".reel.json")) as f:
                        info = _json.load(f)
                except Exception:
                    info = None
                if info and info.get("magnet"):
                    jid = name[:-3]
                    JOBS[jid] = new_job(None, jid=jid, source="torrent",
                                        magnet=info["magnet"], restored=True,
                                        total=int(info.get("total") or 0),
                                        title=info.get("title") or "torrent")
                else:
                    shutil.rmtree(p, ignore_errors=True)
            continue
        if not os.path.isfile(p):
            continue
        if ".live." in name or ".compat." in name:
            os.remove(p)          # fragment left by a hard exit; not seekable
            continue
        if ".subs." in name:
            # Reattached below once its job is known; dropped if nothing owns it.
            continue
        parts = name.split("__", 2)
        if len(parts) != 3:
            continue
        jid, did, rest = parts
        size = os.path.getsize(p)
        if size == 0:
            os.remove(p)
            continue
        title = os.path.splitext(rest)[0]
        # "torrent" in the id slot marks a file finalize_torrent() produced --
        # never a real Drive id, those are always 20+ characters. The magnet
        # needed to re-fetch it lives in a sidecar, since it doesn't fit in a
        # filename the way a Drive id does.
        extra = {}
        if did == "torrent":
            did = None
            extra["source"] = "torrent"
            try:
                with open(os.path.join(DL, jid + ".magnet")) as f:
                    extra["magnet"] = f.read().strip() or None
            except OSError:
                extra["magnet"] = None
        if not playable(p):
            # Cut short by a hard exit, so there is nothing to resume. Keep the
            # row -- the Drive id (or magnet) is in hand -- and one click
            # re-fetches it.
            os.remove(p)
            JOBS[jid] = new_job(did, jid=jid, status="evicted", restored=True,
                                hold=False, title=title, **extra)
            continue
        JOBS[jid] = new_job(did, jid=jid, path=p, total=size, received=size,
                            status="done", restored=True, hold=False,
                            title=title, **extra,
                            kind="audio" if name.lower().endswith(".mp3") else "video")

    # Second pass for subtitle sidecars, now that every job is known. One whose
    # job didn't come back is an orphan: it can never be reached, and leaving it
    # would quietly count against the cache cap forever.
    for name in os.listdir(DL):
        if ".subs." not in name or not name.endswith(".vtt"):
            continue
        jid = name.split(".subs.", 1)[0]
        lang = name.split(".subs.", 1)[1][:-4] or SUBS_LANG
        if jid in JOBS:
            JOBS[jid].update(subs_status="ready", subs_lang=lang,
                             subs_source="restored")
        else:
            try:
                os.remove(os.path.join(DL, name))
            except OSError:
                pass


# ---- the work ----------------------------------------------------------------

def ctype_for(path):
    ext = os.path.splitext(path)[1].lower()
    return {".mp3": "audio/mpeg", ".m4a": "audio/mp4", ".mov": "video/quicktime",
            ".m4v": "video/x-m4v"}.get(ext, "video/mp4")


def disk_bytes(p):
    """Bytes actually on disk. Torrent clients preallocate, and a sparse file
    reports its full logical size immediately, so st_size alone would show 100%
    before a single piece arrived. st_blocks reflects real allocation."""
    try:
        st = os.stat(p)
    except OSError:
        return 0
    alloc = getattr(st, "st_blocks", 0) * 512
    return min(st.st_size, alloc) if alloc else st.st_size


def contiguous_end(fd, size):
    """How far the file can be read as one unbroken run from the front.

    rclone downloads anything over --multi-thread-cutoff (256Mi by default) with
    several streams at once, filling a sparse file out of order, so st_size runs
    ahead of the bytes that actually exist. Reading past the first hole hands
    ffmpeg a block of zeros, which it decodes as a corrupt stream -- the video
    track then jumps forward by minutes while the audio keeps going.

    SEEK_HOLE reports EOF when there is no hole, which is the answer we want for
    a file written straight through. Filesystems without it raise, and there the
    old assumption is the best available.
    """
    try:
        here = os.lseek(fd, 0, os.SEEK_CUR)
        try:
            return os.lseek(fd, 0, os.SEEK_HOLE)
        finally:
            os.lseek(fd, here, os.SEEK_SET)
    except (OSError, AttributeError, ValueError):
        return size


def tree_bytes(d):
    total = 0
    for root, _dirs, files in os.walk(d):
        for f in files:
            total += disk_bytes(os.path.join(root, f))
    return total


def note_progress(job, got):
    """Update received bytes and a smoothed download rate.

    Measured here rather than scraped from a client's terminal UI, which varies
    by version and would be the first thing to break on an upgrade.

    Averaged over a trailing window rather than between adjacent samples. Both
    writers we watch land bytes in bursts -- rclone allocates 64 MiB at a time
    per thread, torrents arrive a piece at a time -- so most one-second samples
    show no change at all. Comparing neighbours therefore reads as ~0 B/s most
    of the time, which used to drag headroom to zero and announce a stall that
    was never coming.
    """
    now = time.time()
    job["received"] = got
    hist = job.setdefault("_rate_hist", [])
    hist.append((now, got))
    while len(hist) > 2 and now - hist[0][0] > RATE_WINDOW:
        hist.pop(0)
    span = now - hist[0][0]
    if span < 1.0:
        return
    job["rate"] = max(0.0, (got - hist[0][1]) / span)
    total = job.get("total") or 0
    r = job.get("rate") or 0
    job["eta"] = int((total - got) / r) if (total > got and r > 1000) else None
    bps = job.get("bitrate") or 0
    if bps > 0 and r > 0:
        job["headroom"] = round(r * 8 / bps, 2)


def media_info(target):
    """(bitrate bits/s, duration seconds) for a file or a seekable URL."""
    try:
        out = subprocess.run(
            ["ffprobe", "-v", "error", "-show_entries", "format=bit_rate,duration",
             "-of", "default=nw=1:nk=1", target],
            capture_output=True, text=True, timeout=25)
        vals = [v.strip() for v in out.stdout.splitlines() if v.strip()]
        br = dur = None
        for v in vals:
            try:
                f = float(v)
            except ValueError:
                continue
            if f > 10000:
                br = int(f)
            elif f > 0:
                dur = f
        return br, dur
    except Exception:
        return None, None


ANSI = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")


SIZE_UNITS = {"B": 1, "KB": 1e3, "KIB": 1024, "MB": 1e6, "MIB": 1024**2,
              "GB": 1e9, "GIB": 1024**3, "TB": 1e12, "TIB": 1024**4}


def as_bytes(num, unit):
    try:
        return int(float(num) * SIZE_UNITS.get((unit or "B").upper(), 1))
    except (TypeError, ValueError):
        return None


def parse_stats(text):
    """Best-effort peers and upload figures from a torrent client's output.

    Everything here is supplementary -- download rate, progress and headroom are
    all measured directly -- so an unrecognised format costs only these extras.
    The raw tail is kept in the job so a pattern that misses can be corrected.
    """
    clean = ANSI.sub(" ", text or "")
    out = {}
    for pat in (r"(\d+)\s+peers", r"peers?\s*[:=]\s*(\d+)",
                r"(\d+)\s*/\s*\d+\s+peers"):
        m = re.search(pat, clean, re.I)
        if m:
            out["peers"] = int(m.group(1))
            break
    # total uploaded -- explicitly not followed by /s, which would be a rate
    for pat in (r"upload(?:ed)?\s*[:=]?\s*([\d.]+)\s*([KMGT]?i?B)(?!\s*/\s*s)",
                r"\u2191\s*([\d.]+)\s*([KMGT]?i?B)(?!\s*/\s*s)",
                r"seeded\s*[:=]?\s*([\d.]+)\s*([KMGT]?i?B)"):
        m = re.search(pat, clean, re.I)
        if m:
            v = as_bytes(m.group(1), m.group(2))
            if v is not None:
                out["uploaded"] = v
            break
    for pat in (r"\u2191\s*([\d.]+)\s*([KMGT]?i?B)\s*/\s*s",
                r"up(?:load)?\s*(?:speed)?\s*[:=]?\s*([\d.]+)\s*([KMGT]?i?B)\s*/\s*s"):
        m = re.search(pat, clean, re.I)
        if m:
            v = as_bytes(m.group(1), m.group(2))
            if v is not None:
                out["up_rate"] = v
            break
    return out


def parse_swarm(text):
    return parse_stats(text).get("peers")


def pause_proc(proc, on):
    """Stop or resume a child so a prefetch can't starve what's playing."""
    if not (proc and CAN_PAUSE) or proc.poll() is not None:
        return False
    try:
        proc.send_signal(signal.SIGSTOP if on else signal.SIGCONT)
        return True
    except Exception:
        return False


def newest_file(d):
    """Newest regular file in d. rclone may write `name.partial` and rename on
    completion, so callers must not cache the resulting path."""
    try:
        fs = [os.path.join(d, f) for f in os.listdir(d)
              if os.path.isfile(os.path.join(d, f))]
        return max(fs, key=os.path.getmtime) if fs else None
    except OSError:
        return None


def iso_index_first(head):
    """Walk the top-level atoms of an ISO base media file (mp4/mov/m4a).

    True  -> `moov` precedes `mdat`, so a decoder can start on partial data.
    False -> `mdat` came first, so the index sits at the end of the file and
             nothing is decodable until the final byte arrives.
    None  -> not enough bytes yet to tell.
    """
    o = 0
    while True:
        if o + 8 > len(head):
            return None
        size = int.from_bytes(head[o:o + 4], "big")
        kind = head[o + 4:o + 8]
        if size == 1:                        # 64-bit extended size
            if o + 16 > len(head):
                return None
            size = int.from_bytes(head[o + 8:o + 16], "big")
        if kind == b"moov":
            return True
        if kind == b"mdat":
            return False
        if size < 8:                         # 0 means "runs to end of file"
            return None
        o += size


def can_stream_live(path):
    """True / False / None, where None means ask again once more has landed."""
    try:
        with open(path, "rb") as f:
            head = f.read(1 << 20)
    except OSError:
        return None
    if len(head) < 16:
        return None
    if head[4:8] == b"ftyp":
        return iso_index_first(head)
    if head[:4] == b"\x1a\x45\xdf\xa3":                    # matroska / webm
        return True
    if head[:4] == b"OggS":
        return True
    if head[:3] in (b"ID3", b"FLV"):
        return True
    if head[0] == 0xFF and (head[1] & 0xE0) == 0xE0:       # mp3 frame sync
        return True
    if head[0] == 0x47 and len(head) > 376 and head[188] == 0x47:   # mpeg-ts
        return True
    return None                                            # let ffprobe decide


def stream_kind(path):
    """'audio', 'video', or None if ffprobe can't tell from what's present yet."""
    try:
        out = subprocess.run(
            ["ffprobe", "-v", "error", "-show_entries", "stream=codec_type",
             "-of", "default=nw=1:nk=1", path],
            capture_output=True, text=True, timeout=20)
        types = [t.strip() for t in out.stdout.splitlines() if t.strip()]
        if not types:
            return None
        return "audio" if ("audio" in types and "video" not in types) else "video"
    except Exception:
        return None


# Codecs a browser can decode directly. Deliberately conservative: mkv is left
# out because Safari won't touch it, and hevc/ac3/dts are excluded too.
BROWSER_CONTAINERS = (".mp4", ".m4v", ".mov")
BROWSER_VIDEO = {"h264", "vp8", "vp9", "av1"}
BROWSER_AUDIO = {"aac", "mp3"}
# The codec name alone is not enough. h264 High 10 (yuv420p10le) and the 4:2:2 /
# 4:4:4 profiles are still "h264", and no browser will decode them -- the audio
# plays and the picture never appears. Only 8-bit 4:2:0 is safe to pass through.
SAFE_PIX = {"yuv420p", "yuvj420p", "nv12", "nv21", "yuv420p10le_NOT"}
SAFE_PIX.discard("yuv420p10le_NOT")


def pix_ok(pix):
    """Unknown formats are allowed through: rare, and refusing them would mean
    needlessly re-encoding files that are perfectly fine."""
    return (not pix) or pix in SAFE_PIX


# Video codecs MP4 can carry as-is. Copying one of these is a remux: seconds of
# I/O rather than minutes of encoding, and the output is no larger than the
# source. Whether a given *client* can decode it is a separate question, which
# only the client can answer -- see caps_of().
MP4_VIDEO = {"h264", "hevc", "av1", "vp9", "mpeg4"}

# What each connected browser told us it can decode. Keyed by a client id the
# page generates, because capability is per-device: an iPad decodes HEVC that a
# desktop Firefox will not. Never inferred from the user agent, which lies.
CLIENTS = {}
CLIENT_LOCK = threading.Lock()
CLIENT_TTL = 900.0            # forget a client that hasn't been seen in a while


def note_caps(cid, caps):
    """Record what a client says it can play, and forget stale ones."""
    if not cid:
        return
    now = time.time()
    with CLIENT_LOCK:
        CLIENTS[cid] = {"caps": {str(c) for c in (caps or [])}, "seen": now}
        for k in [k for k, v in CLIENTS.items() if now - v["seen"] > CLIENT_TTL]:
            del CLIENTS[k]


def caps_of(cid):
    """A client's decodable codecs, or the universal baseline if we've not heard
    from it. Assuming the baseline is the safe way to be wrong: it costs a
    transcode that was not strictly needed, rather than silence and a blank
    picture."""
    with CLIENT_LOCK:
        rec = CLIENTS.get(cid)
        if rec:
            return set(rec["caps"])
    return set(BROWSER_VIDEO)


def codec_key(v, pix):
    """The capability name for a stream, which is the codec plus its bit depth.

    x265 rips are routinely Main 10, and 10-bit is a genuinely different
    question from 8-bit -- a device can decode one and not the other.
    """
    if not v:
        return None
    ten = bool(pix and ("10le" in pix or "10be" in pix or "p010" in pix))
    return v + "10" if ten else v


def plays_natively(caps, v, pix):
    """Can this client take the video stream as it stands?"""
    if v is None:
        return True                       # audio only
    key = codec_key(v, pix)
    if key in caps:
        return True
    # An 8-bit stream in the baseline set is fine even from a client that only
    # reported the bare codec name.
    return v in caps and pix_ok(pix)


def probe_all(path, timeout=25):
    """Everything we need about a source in ONE pass.

    Over a torrent every byte ffprobe reads has to be fetched from peers first,
    so repeating this per property was costing real minutes. The probe size is
    capped too: the defaults read far more than is needed to identify streams.
    """
    try:
        out = subprocess.run(
            ["ffprobe", "-v", "error",
             "-probesize", "2000000", "-analyzeduration", "3000000",
             "-show_entries",
             "stream=codec_type,codec_name,height,color_transfer,pix_fmt,profile:"
             "format=bit_rate,duration",
             "-of", "json", path], capture_output=True, text=True, timeout=timeout)
        data = _json.loads(out.stdout)
    except Exception:
        return {}
    return data


def codecs_of(path):
    """(video_codec, audio_codec, height, hdr) for the first stream of each."""
    try:
        streams = probe_all(path).get("streams", [])
    except Exception:
        return (None, None, None, False)
    if not streams:
        return (None, None, None, False)
    try:
        pass
    except Exception:
        return (None, None, None, False)
    vs = [t for t in streams if t.get("codec_type") == "video"]
    a = [t.get("codec_name") for t in streams if t.get("codec_type") == "audio"]
    v = vs[0] if vs else {}
    hdr = (v.get("color_transfer") or "") in ("smpte2084", "arib-std-b67")
    return (v.get("codec_name"), a[0] if a else None, v.get("height"), hdr)


def probe_media(path, timeout=25):
    """(v, a, height, hdr, bitrate, duration, pix) from a single ffprobe."""
    data = probe_all(path, timeout)
    streams = data.get("streams", [])
    fmt = data.get("format", {})
    if not streams:
        return (None, None, None, False, None, None, None)
    vs = [t for t in streams if t.get("codec_type") == "video"]
    a = [t.get("codec_name") for t in streams if t.get("codec_type") == "audio"]
    v = vs[0] if vs else {}
    hdr = (v.get("color_transfer") or "") in ("smpte2084", "arib-std-b67")
    def num(x, cast):
        try:
            return cast(x)
        except (TypeError, ValueError):
            return None
    return (v.get("codec_name"), a[0] if a else None, v.get("height"), hdr,
            num(fmt.get("bit_rate"), int), num(fmt.get("duration"), float),
            v.get("pix_fmt"))


_ENCODER = None


def encoder_works(name):
    """Being listed by ffmpeg is not the same as working. Hardware encoders are
    compiled in regardless of whether the machine has the hardware, and only
    fail when you actually try to open a session -- so try one."""
    try:
        r = subprocess.run(
            ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
             "-f", "lavfi", "-i", "color=c=black:s=320x240:r=5:d=0.4",
             "-c:v", name, "-f", "null", "-"],
            capture_output=True, timeout=30)
        return r.returncode == 0
    except Exception:
        return False


def h264_encoder():
    """Prefer a hardware encoder that genuinely works. Software x264 on a 2160p
    source is far from realtime on a laptop, so live playback would stall."""
    global _ENCODER
    if _ENCODER:
        return _ENCODER
    try:
        have = subprocess.run(["ffmpeg", "-hide_banner", "-encoders"],
                              capture_output=True, text=True, timeout=20).stdout
    except Exception:
        have = ""
    for cand in ("h264_videotoolbox",          # macOS, hardware
                 "h264_nvenc", "h264_qsv", "h264_vaapi"):
        if cand in have and encoder_works(cand):
            _ENCODER = cand
            return _ENCODER
    _ENCODER = "libx264"
    return _ENCODER


def encode_bitrate(src_bps, height, vcodec):
    """Bits/s to aim for when a hardware encoder needs an explicit target.

    A flat 6 Mbps was picked for the worst case and then applied to everything,
    so a 2.4 Mbps source came back two and a half times larger than it went in,
    for no visible gain. H264 is less efficient than the codecs we transcode away
    from, so the source rate is raised rather than matched -- but never past what
    the resolution warrants, and never below a floor that would look bad.

    src_bps is only passed once the whole file is on disk, where size over
    duration is exact. ffprobe's guess from a partial download is not: it read
    572 kbps for a file genuinely running at 2.4 Mbps.
    """
    ceil = (6_000_000 if (not height or height > 720)
            else 3_000_000 if height > 480 else 1_500_000)
    if not src_bps or src_bps <= 0:
        return ceil                       # unknown: the old ceiling, unchanged
    slack = 1.5 if (vcodec or "") in ("hevc", "vp9", "av1") else 1.15
    return int(max(1_000_000, min(ceil, src_bps * slack)))


HAS_ZSCALE = None


def has_zscale():
    global HAS_ZSCALE
    if HAS_ZSCALE is None:
        try:
            out = subprocess.run(["ffmpeg", "-hide_banner", "-filters"],
                                 capture_output=True, text=True, timeout=20).stdout
            HAS_ZSCALE = "zscale" in out and "tonemap" in out
        except Exception:
            HAS_ZSCALE = False
    return HAS_ZSCALE


def video_args(v, height, hdr, live=True, pix=None, src_bps=None, caps=None):
    """How to handle the video stream, and any filter it needs.

    Copying is always preferable, but only when the browser can decode what's
    there. H265/HEVC in particular plays in Safari and not in Chrome, and
    copying it produces a file that loads and shows nothing.
    """
    allow = BROWSER_VIDEO if caps is None else caps
    if v is None or plays_natively(allow, v, pix):
        # Copied, not encoded. HEVC must be tagged hvc1 going into MP4: with the
        # hev1 tag ffmpeg would otherwise write, Apple's decoders refuse the file
        # outright, so the one client that can play it natively would not.
        return ["-c:v", "copy"] + (["-tag:v", "hvc1"] if v == "hevc" else []), [], ""
    enc = h264_encoder()
    args = ["-c:v", enc, "-pix_fmt", "yuv420p"]
    # libx264 is already quality-driven, so only the hardware path needs a target
    target = None
    if enc == "libx264":
        args += ["-preset", "veryfast", "-crf", "23"]
    else:
        target = encode_bitrate(src_bps, height, v)
        args += ["-b:v", str(target)]
    chain = []
    if v in allow and not pix_ok(pix):
        note = f"{v} {pix} is not 8-bit 4:2:0, re-encoded ({enc})"
    else:
        note = f"{v} transcoded to h264 ({enc})"
    if target:
        note += f" at {target / 1e6:.1f} Mbps"
    tagged = []
    # Scale before tonemapping: at 2160p the filter cost dominates, and a
    # quarter of the pixels is a quarter of the work.
    if height and height > 1080:
        chain.append("scale=-2:1080")
        note += ", scaled to 1080p"
    if hdr:
        if has_zscale():
            chain += ["zscale=t=linear:npl=100", "format=gbrpf32le",
                      "zscale=p=bt709", "tonemap=tonemap=hable:desat=0",
                      "zscale=t=bt709:m=bt709:r=tv", "format=yuv420p"]
            # Retag the output: the pixels are SDR now, and leaving the PQ
            # transfer in the metadata makes players wash the colours out.
            tagged = ["-color_primaries", "bt709", "-color_trc", "bt709",
                      "-colorspace", "bt709"]
            note += ", HDR tonemapped"
        else:
            note += ", HDR left as-is (no zscale; colours may look flat)"
    return args + tagged, (["-vf", ",".join(chain)] if chain else []), note


def browser_ready(path):
    """True if the browser can play this file exactly as downloaded.

    Where `moov` sits is irrelevant here: given a server that honours ranges,
    the browser fetches the tail to find the index and then reads forward, the
    same way ffmpeg does. So for these files the remux pass is pure waste --
    a full read and rewrite, plus a lossy audio re-encode, for no gain.
    """
    if os.path.splitext(path)[1].lower() not in BROWSER_CONTAINERS:
        return False
    v, a, _h, _hdr, _br, _du, pix = probe_media(path)
    if v is None and a is None:
        return False
    if v is not None and (v not in BROWSER_VIDEO or not pix_ok(pix)):
        return False
    if a is not None and a not in BROWSER_AUDIO:
        return False
    return True


def is_audio_only(path):
    kind = stream_kind(path)
    if kind:
        return kind == "audio"
    return path.lower().endswith((".mp3", ".m4a", ".wav", ".aac", ".flac", ".ogg"))


def phase(job, name):
    """Record how long each stage took, so a slow start can be attributed
    instead of guessed at."""
    now = time.time()
    t = job.setdefault("timings", {})
    last = job.pop("_phase_t", None)
    prev = job.pop("_phase_n", None)
    if prev and last:
        t[prev] = round(now - last, 1)
    if name:
        job["_phase_t"], job["_phase_n"] = now, name
        job["status"] = name if name in ACTIVE else job["status"]


def fail(job, msg):
    """Mark a job failed and make sure nothing of it keeps running.

    A failed job used to leave its children alive: an ffmpeg was still reading a
    webtorrent server three minutes after the row read 'failed', with the server
    itself long gone. Stopping them here covers every failure path rather than
    the ones someone remembered.
    """
    job["status"] = "error"
    job["error"] = msg[:300]
    record(job, "failed: " + msg[:200])
    stop_procs(job)


# ---- phase 1: live -----------------------------------------------------------

def feed_live(job, raw_dir, proc):
    """Pump the growing download into ffmpeg's stdin.

    Reads through EOF repeatedly rather than stopping at it, and sizes the file
    with fstat on the open handle so an rclone `.partial` -> final rename mid
    transfer doesn't strand us on a dead path.

    Never reads past the first hole: a multi-threaded rclone fills the file out
    of order, and the gap between written chunks is not yet data. Unbuffered so
    the position we track is the one the descriptor is actually at, since
    contiguous_end() seeks on the same descriptor.
    """
    f = None
    for _ in range(50):                     # the file may not exist for a moment
        raw = newest_file(raw_dir)
        if raw:
            try:
                f = open(raw, "rb", buffering=0)
                break
            except OSError:
                pass
        if job["cancel"].is_set():
            break
        time.sleep(0.2)
    if f is None:
        try:
            proc.stdin.close()
        except Exception:
            pass
        return
    try:
        while True:
            try:
                fd = f.fileno()
                size = os.fstat(fd).st_size
                pos = f.tell()
                avail = contiguous_end(fd, size)
            except OSError:
                break
            if avail > pos:
                chunk = f.read(min(1 << 20, avail - pos))
                if chunk:
                    proc.stdin.write(chunk)
                    continue
            if job["cancel"].is_set():
                break
            # Done only when the download has landed AND the hole it may have
            # left has been filled in behind us.
            if job.get("dl_done") and pos >= size:
                break
            time.sleep(0.15)
    except (BrokenPipeError, OSError, ValueError):
        pass
    finally:
        f.close()
        try:
            proc.stdin.close()
        except Exception:
            pass


def watch_live(job, raw_dir, kind, proc, out, transcoding):
    try:
        _watch_live(job, raw_dir, kind, proc, out, transcoding)
    except Exception as e:
        # never leave the job claiming a live stream that isn't there
        job["live_done"] = True
        job["live_ready"] = False
        job["live_note"] = "watcher failed: %s: %s" % (type(e).__name__, e)


def _watch_live(job, raw_dir, kind, proc, out, transcoding):
    proc.wait()
    err = proc.stderr.read() if proc.stderr else ""
    if isinstance(err, (bytes, bytearray)):
        err = err.decode("utf-8", "replace")
    size = os.path.getsize(out) if os.path.exists(out) else 0

    # A stream copy can be refused outright — a codec the MP4 container won't
    # accept. Worth one retry that re-encodes, but only while the download is
    # still running; otherwise phase 2 is about to produce the real file anyway.
    if (proc.returncode != 0 and size < LIVE_OPEN and kind == "video"
            and not transcoding and not job["cancel"].is_set()
            and not job.get("dl_done")):
        try:
            os.remove(out)
        except OSError:
            pass
        job["live_note"] = tail(err, 2, 160)
        start_live(job, raw_dir, kind, transcoding=True)
        return

    job["live_done"] = True
    if proc.returncode != 0 or size < LIVE_OPEN:
        job["live_note"] = (("transcoded, " if transcoding else "copy, ")
                            + "rc=%s, %s bytes; " % (proc.returncode, size)
                            + tail(err, 3, 200))
    if size < LIVE_OPEN:
        # nothing servable came out; don't advertise it
        job["live_file"] = None
        job["live_ready"] = False
        if size == 0:
            job["streamable"] = False


def start_live(job, raw_dir, kind, transcoding=False, vcodec=None,
               height=None, hdr=False, pix=None):
    """Begin emitting a fragmented, immediately-playable copy.

    Codec-aware: copying an HEVC stream into the fragments produces something
    Chrome loads and refuses to show, and the viewer would then also have to sit
    through the full conversion before anything played.
    """
    if kind == "audio":
        out = os.path.join(DL, job["id"] + ".live.mp3")
        cmd = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
               "-i", "pipe:0", "-vn", "-c:a", "libmp3lame", "-q:a", "4",
               # without this ffmpeg holds everything in its io buffer and the
               # file stays empty until close — nothing to serve
               "-flush_packets", "1", "-f", "mp3", out]
    else:
        out = os.path.join(DL, job["id"] + ".live.mp4")
        if transcoding:
            vargs = ["-c:v", "libx264", "-preset", "ultrafast", "-crf", "26"]
            vfilter, vnote = [], "re-encoded for the live stream"
        else:
            vargs, vfilter, vnote = video_args(vcodec, height, hdr, pix=pix,
                                               caps=set(job.get("caps") or ())
                                               or None)
        if vnote:
            job["note"] = (job.get("note", "") + "; " + vnote).strip("; ")
        cmd = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
               "-progress", "pipe:1", "-nostats",
               "-i", "pipe:0", *vfilter, *vargs,
               "-c:a", "aac", "-ac", "2", "-f", "mp4",
               # empty_moov puts a playable header up front; frag_keyframe closes
               # a fragment on every keyframe so the browser gets data early.
               "-movflags", "+frag_keyframe+empty_moov+default_base_moof",
               "-frag_duration", "1500000", "-flush_packets", "1", out]
    try:
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=False)
    except OSError:
        job["streamable"] = False
        return
    job["procs"].append(proc)
    job["live_file"] = out
    job["live_kind"] = kind
    job["live_transcoded"] = transcoding
    threading.Thread(target=read_progress, args=(job, proc.stdout),
                     daemon=True).start()
    threading.Thread(target=feed_live, args=(job, raw_dir, proc), daemon=True).start()
    threading.Thread(target=watch_live,
                     args=(job, raw_dir, kind, proc, out, transcoding),
                     daemon=True).start()


def read_progress(job, stream, key="encode_speed", total_s=None, pct_key=None):
    """ffmpeg's own -progress output: speed, and position if we know the length.

    Speed below 1.0 means it is losing to realtime, which the health readout
    needs in order to tell 'slow swarm' from 'slow machine'.
    """
    try:
        for raw in iter(stream.readline, b""):
            line = raw.decode("utf-8", "replace").strip()
            k, _, val = line.partition("=")
            if k == "speed":
                try:
                    job[key] = float(val.strip().rstrip("x"))
                except ValueError:
                    pass
            elif k == "out_time_us" and pct_key and total_s:
                try:
                    job[pct_key] = round(min(100.0,
                                             int(val) / 1e6 / total_s * 100), 1)
                except (ValueError, ZeroDivisionError):
                    pass
    except Exception:
        pass


def sweep_live(job, delay=LIVE_GRACE):
    """Drop the live copy once the player has had time to swap to the seekable
    one. Keeping both forever would double what every item costs in cache."""
    def go():
        time.sleep(delay)
        lf = job.get("live_file")
        job["live_file"] = None
        job["live_ready"] = False
        if lf and os.path.exists(lf):
            try:
                os.remove(lf)
            except OSError:
                pass
    threading.Thread(target=go, daemon=True).start()


def run_with_progress(job, cmd, total_s):
    """Run a conversion while reporting how far along it is.

    A stream copy is effectively instant, but a real re-encode runs at close to
    realtime, so a long file means minutes. Silence there is indistinguishable
    from a hang.
    """
    job["conv_pct"] = 0.0
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    except OSError as e:
        class R:
            returncode = 1
            stderr = str(e)
        return R()
    job["procs"].append(proc)
    reader = threading.Thread(target=read_progress,
                              args=(job, proc.stdout, "conv_speed", total_s,
                                    "conv_pct"), daemon=True)
    reader.start()
    err = proc.stderr.read().decode("utf-8", "replace")
    proc.wait()
    reader.join(1.0)
    job["conv_pct"] = None
    job["conv_speed"] = None

    class R:
        returncode = proc.returncode
        stderr = err
    return R()


def run_job(job):
    drive_id = job["drive_id"]
    raw_dir = os.path.join(DL, job["id"] + "_raw")

    def cleanup():
        shutil.rmtree(raw_dir, ignore_errors=True)

    def stopped():
        if not job["cancel"].is_set():
            return False
        cleanup()
        if job.get("overflow"):
            fail(job, "Stopped — cache is full. Raise the limit or remove items.")
        else:
            job["status"] = cancel_status(job)
        return True

    if stopped():
        return
    if not has_rclone():
        return fail(job, "No rclone remote named 'gdrive'. Run: rclone config")
    if not has_ffmpeg():
        return fail(job, "ffmpeg and ffprobe are required. Install both, then retry.")

    os.makedirs(raw_dir, exist_ok=True)

    def find_raw():
        return newest_file(raw_dir)

    def consider_live(raw):
        """Decide once whether this file can play before it finishes."""
        verdict = can_stream_live(raw)
        if verdict is None:
            # Unknown container. ffprobe may still make sense of the head; if not,
            # keep waiting until enough has landed to stop guessing.
            if stream_kind(raw):
                verdict = True
            elif job["received"] >= LIVE_GIVEUP:
                verdict = False
            else:
                return False                    # undecided, ask again later
        job["streamable"] = verdict
        v, a, vh, hdr, br, dur, pix = probe_media(raw)
        if job.get("bitrate") is None:
            job["bitrate"], job["duration"] = br, dur
        if not verdict:
            job["live_note"] = "index at end of file; needs the full download"
        # By name, before the download finishes -- same reasoning as the torrent
        # path. The hook after conversion re-runs it with the file's hash.
        start_subs(job, None, name=os.path.basename(raw))
        if verdict:
            kind = "audio" if (a and not v) else "video"
            job["kind"] = kind
            start_live(job, raw_dir, kind, vcodec=v, height=vh, hdr=hdr, pix=pix)
        return True

    try:
        # ---- download -------------------------------------------------------
        job["status"] = "downloading"
        proc = subprocess.Popen(
            ["rclone", "backend", "copyid", "gdrive:", drive_id, raw_dir + os.sep],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        job["proc"] = proc

        # Drain stderr on its own thread; a full pipe would otherwise deadlock
        # a chatty rclone before it ever exits.
        errbuf = []
        drain = threading.Thread(target=lambda: errbuf.append(proc.stderr.read()),
                                 daemon=True)
        drain.start()

        decided = False
        while proc.poll() is None:
            if job["cancel"].is_set():
                proc.kill()
                break
            raw = find_raw()
            if raw:
                note_progress(job, disk_bytes(raw))
                if not decided and job["received"] >= LIVE_HEAD:
                    decided = consider_live(raw)
                lf = job.get("live_file")
                if lf and not job.get("live_ready"):
                    try:
                        if os.path.getsize(lf) >= LIVE_OPEN:
                            job["live_ready"] = True   # playable from here on
                    except OSError:
                        pass
            time.sleep(0.4)
        proc.wait()
        job["proc"] = None
        job["dl_done"] = True                   # releases the live feeder's loop
        if stopped():
            return

        # rclone can exit before the drain thread has appended; wait for it or
        # the error message is lost and every failure looks generic.
        drain.join(3.0)
        rerr = "".join(x for x in errbuf if x)
        raw = find_raw()
        if proc.returncode != 0 or not raw or os.path.getsize(raw) == 0:
            cleanup()
            return fail(job, tail(rerr) or
                        "rclone couldn't fetch that file. Check the link and your access.")

        # Drive's own filename is the nicest title we get.
        real = os.path.basename(raw)
        job["title"] = os.path.splitext(real)[0]
        safe = re.sub(r"[^\w.\- ]", "_", real)[:110]
        stem = os.path.splitext(safe)[0]
        base = f"{job['id']}__{drive_id}__{stem}"

        job["total"] = os.path.getsize(raw)
        job["received"] = job["total"]

        # Hashed from the raw download, which is the release someone uploaded
        # subtitles for. The converted file below is reel's own remux and hashes
        # to nothing anyone has ever seen, so this has to happen here -- before
        # cleanup() removes the raw copy.
        start_subs(job, raw, name=real)

        # ---- convert, if it's actually needed --------------------------------
        if is_audio_only(raw):
            job["kind"] = "audio"
            out = os.path.join(DL, base + ".mp3")
            if raw.lower().endswith(".mp3"):
                shutil.move(raw, out)
            else:
                job["status"] = "converting"
                r = subprocess.run(
                    ["ffmpeg", "-nostdin", "-y", "-i", raw, "-vn",
                     "-c:a", "libmp3lame", "-q:a", "2", out],
                    capture_output=True, text=True)
                if r.returncode != 0:
                    cleanup()
                    return fail(job, tail(r.stderr) or "Audio conversion failed.")
        elif browser_ready(raw):
            # Nothing to do: hand the file over exactly as it arrived. No
            # 'converting' stage, because there is no conversion.
            job["kind"] = "video"
            out = os.path.join(DL, base + os.path.splitext(safe)[1].lower())
            shutil.move(raw, out)
            job["note"] = "played as downloaded, no conversion needed"
        else:
            job["kind"] = "video"
            job["status"] = "converting"
            out = os.path.join(DL, base + ".mp4")
            # Don't re-encode audio that's already fine; it costs time and quality.
            _v, _a, _h, _hdr, _b2, _d2, _pix = probe_media(raw)
            # Normalised to AAC even when the video is copied. AC3 and DTS are
            # what x265 rips usually carry, and a device that decodes the video
            # may still have no idea what to do with the sound. Audio is cheap to
            # encode, so this costs seconds and makes the file universally
            # playable for anything that can handle the picture.
            acodec = ["-c:a", "copy"] if _a in BROWSER_AUDIO else ["-c:a", "aac"]
            _dur = job.get("duration") or _d2
            # The whole file is here by now, so its true average rate is simply
            # size over duration. Nothing extra is read to learn it, and the
            # live phase is long since started, so this costs no startup time.
            src_bps = None
            try:
                if _dur and _dur > 0:
                    src_bps = os.path.getsize(raw) * 8 / _dur
            except OSError:
                pass
            # Native first: keep the source video stream whenever MP4 can carry
            # it, whatever this particular client can decode. Copying is seconds
            # of I/O against ten minutes of encoding, and the result is smaller
            # than the source rather than larger. Anything that cannot decode it
            # asks for a compat rendition, which is made once and kept.
            # The exact key matters: a Main 10 stream is "hevc10", and asking
            # only whether "hevc" is carryable would send every 10-bit rip --
            # which is most x265 rips -- down the re-encode path.
            caps = ({codec_key(_v, _pix)} | MP4_VIDEO) if _v in MP4_VIDEO else set()
            vargs, vfilter, vnote = video_args(_v, _h, _hdr, live=False, pix=_pix,
                                               src_bps=src_bps, caps=caps)
            copying = "copy" in vargs
            if copying:
                job["note"] = (job.get("note", "") +
                               f"; {_v} kept as-is, remuxed to mp4").strip("; ")
            elif vnote:
                job["note"] = (job.get("note", "") + "; " + vnote).strip("; ")
            r = run_with_progress(
                job, ["ffmpeg", "-nostdin", "-y", "-progress", "pipe:1", "-nostats",
                      "-i", raw,
                      # Only the streams we mean to keep. Left to itself ffmpeg
                      # drags along whatever else the MKV had -- the stray
                      # bin_data track that turned up in the last conversion.
                      "-map", "0:v:0", "-map", "0:a:0?",
                      *vfilter, *vargs, *acodec,
                      "-movflags", "+faststart", out], _dur)
            if r.returncode != 0:
                # Fall back to a plain software encode.
                r = subprocess.run(
                    ["ffmpeg", "-nostdin", "-y", "-i", raw, "-c:v", "libx264",
                     "-preset", "veryfast", "-crf", "23", "-pix_fmt", "yuv420p",
                     *acodec, "-movflags", "+faststart", out],
                    capture_output=True, text=True)
                if r.returncode != 0:
                    cleanup()
                    return fail(job, tail(r.stderr) or "Conversion failed.")

        if stopped():
            try:
                os.remove(out)
            except OSError:
                pass
            return

        if not (os.path.exists(out) and os.path.getsize(out) > 0):
            cleanup()
            return fail(job, "Conversion produced an empty file.")

        job["path"] = out
        job["total"] = os.path.getsize(out)
        job["received"] = job["total"]
        job["status"] = "done"
        # What the finished file actually holds, so a client can tell before it
        # presses play whether it needs the compat rendition instead.
        ov, _oa, _oh, _ohdr, _ob, _od, opix = probe_media(out)
        job["vcodec"], job["vpix"] = ov, opix
        job["play_key"] = codec_key(ov, opix)
        cleanup()
        if job.get("live_file"):
            sweep_live(job)
        enforce_cache_cap()
    except Exception as e:
        cleanup()
        fail(job, f"{type(e).__name__}: {e}")


# ---- torrents ----------------------------------------------------------------

def bdecode(data, i=0):
    """Minimal bencode reader, enough for a .torrent's info dict."""
    c = data[i:i + 1]
    if c == b"i":
        j = data.index(b"e", i)
        return int(data[i + 1:j]), j + 1
    if c == b"l":
        out, i = [], i + 1
        while data[i:i + 1] != b"e":
            v, i = bdecode(data, i)
            out.append(v)
        return out, i + 1
    if c == b"d":
        out, i = {}, i + 1
        while data[i:i + 1] != b"e":
            k, i = bdecode(data, i)
            v, i = bdecode(data, i)
            out[k] = v
        return out, i + 1
    j = data.index(b":", i)
    n = int(data[i:j])
    return data[j + 1:j + 1 + n], j + 1 + n


def torrent_infohash(path):
    """SHA1 of the raw info dict -- the torrent's real identity.

    Taken from the original bytes rather than re-encoded, since re-encoding can
    reorder keys and change the hash. Preferable to trusting the magnet's xt,
    because the server keys its urls on this.
    """
    try:
        with open(path, "rb") as f:
            data = f.read()
        i = data.find(b"4:info")
        if i < 0:
            return ""
        start = i + 6
        _, end = bdecode(data, start)
        return hashlib.sha1(data[start:end]).hexdigest()
    except Exception:
        return ""


def torrent_files(path):
    """Exact file list from a .torrent: real paths, real sizes, no parsing of
    console output and no guessing at directory structure."""
    try:
        with open(path, "rb") as f:
            meta, _ = bdecode(f.read())
        info = meta[b"info"]
        root = info[b"name"].decode("utf-8", "replace")
    except Exception:
        return []
    out = []
    if b"files" in info:
        for i, fe in enumerate(info[b"files"]):
            parts = [p.decode("utf-8", "replace") for p in fe[b"path"]]
            out.append({"index": i, "name": "/".join([root] + parts),
                        "size": int(fe[b"length"]), "rel": "/".join(parts)})
    else:
        out.append({"index": 0, "name": root, "size": int(info.get(b"length", 0)),
                    "rel": root})
    return out


def fetch_metadata(job, magnet, port, limit):
    """Grab the .torrent once via downloadmeta.

    Worth it because the streaming run can then be handed a local .torrent and
    skip metadata discovery entirely -- otherwise every item pays for peer
    discovery twice, serially, which is most of the wait before playback.
    """
    meta_dir = os.path.join(DL, job["id"] + "_meta")
    os.makedirs(meta_dir, exist_ok=True)
    cmd = ["webtorrent", "downloadmeta", magnet, "--out", meta_dir,
           "--port", str(port)]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
    except Exception:
        return None, None, ""
    job["procs"].append(proc)
    lines = []
    threading.Thread(target=lambda: [lines.append(l) for l in
                                     iter(proc.stdout.readline, "")],
                     daemon=True).start()

    def found():
        for root, _d, fs in os.walk(meta_dir):
            for f in fs:
                if f.lower().endswith(".torrent"):
                    return os.path.join(root, f)
        return None

    deadline = time.time() + limit
    while time.time() < deadline and not job["cancel"].is_set():
        t = found()
        if t and os.path.getsize(t) > 0:
            files = torrent_files(t)
            if files:
                job["wt_ih"] = torrent_infohash(t)
                if proc.poll() is None:
                    try:
                        proc.kill()
                    except Exception:
                        pass
                return files, t, ANSI.sub(" ", "".join(lines)).strip()
        if proc.poll() is not None:
            break
        time.sleep(0.3)
    if proc.poll() is None:
        try:
            proc.kill()
        except Exception:
            pass
    return None, None, ANSI.sub(" ", "".join(lines)).strip()


def parse_file_list(text):
    """webtorrent prints an index and a name per file when --select is bare.

    Format has shifted between versions, so match loosely: any line that starts
    with a number and contains something file-shaped.
    """
    files = []
    for line in (text or "").splitlines():
        line = line.strip()
        m = re.match(r"^\[?(\d+)\]?[\s:.)-]+(.+?)\s*$", line)
        if not m:
            continue
        idx, name = int(m.group(1)), m.group(2).strip()
        size = 0
        sm = re.search(r"\(?([\d.]+)\s*([KMGT]?i?B)\)?\s*$", name, re.I)
        if sm:
            mult = {"B": 1, "KB": 1e3, "KIB": 1024, "MB": 1e6, "MIB": 1024**2,
                    "GB": 1e9, "GIB": 1024**3, "TB": 1e12, "TIB": 1024**4}
            size = int(float(sm.group(1)) * mult.get(sm.group(2).upper(), 1))
            name = name[:sm.start()].strip(" -\t")
        if name:
            files.append({"index": idx, "name": name, "size": size})
    return files


def fan_out(job, magnet, files, extras):
    """Queue the rest of a pack as items of their own.

    Each sibling is an ordinary torrent job pinned to one file index, so it goes
    through the same download, probe, convert and subtitle path as anything
    else, and the scheduler decides when it starts -- which is what keeps a
    twelve-episode pack from opening twelve webtorrent processes at once.
    """
    made = []
    for f in extras:
        sib = new_job(None, source="torrent", magnet=magnet,
                      caps=job.get("caps"), wt_index=f["index"],
                      title=os.path.splitext(os.path.basename(f["name"]))[0])
        sib["total"] = f.get("size") or 0
        sib["wt_files"] = len(files)
        record(sib, "queued from a pack: file %d of %d, %s (%.2f GB)"
               % (f["index"], len(files), f["name"][:120],
                  (f.get("size") or 0) / GB))
        with LOCK:
            JOBS[sib["id"]] = sib
        made.append(sib["id"])
    if made:
        record(job, "pack of %d: queued %d more file(s) as their own items"
               % (len(extras) + 1, len(made)))
    return made


def pack_files(files):
    """Every file in a torrent worth queueing as its own item, in play order.

    Empty for an ordinary single-film torrent, which is the common case and must
    stay exactly as it was. A pack is only recognised when two or more files
    look like features -- judged against the biggest, since "big enough" means
    nothing without something to compare to: a 200 MB extra beside a 12 GB
    remux and a 200 MB episode beside a 300 MB one are different things.

    Ordered by index rather than size, because for a season the order that
    matters is the one they were meant to be watched in.
    """
    vids = [f for f in (files or [])
            if (f.get("name") or "").lower().endswith(VIDEO_EXT)
            and not PACK_EXTRAS.search(f.get("name") or "")]
    if len(vids) < 2:
        return []
    biggest = max((f.get("size") or 0) for f in vids)
    bar = max(PACK_MIN_BYTES, biggest * PACK_MIN_SHARE)
    keep = [f for f in vids if (f.get("size") or 0) >= bar]
    if len(keep) < 2:
        return []
    keep.sort(key=lambda f: f["index"])
    return keep[:PACK_MAX]


def pick_file(files):
    """Biggest video, else biggest audio, else biggest anything. Samples and
    extras are always smaller than the feature, so size is a good proxy."""
    for exts in (VIDEO_EXT, AUDIO_EXT, None):
        pool = [f for f in files
                if exts is None or f["name"].lower().endswith(exts)]
        if pool:
            return max(pool, key=lambda f: (f["size"], -f["index"]))
    return None


def probe_url(url, timeout=8):
    """Does this URL serve bytes that look like media, and honour ranges?

    'returned something' is not good enough: an index page is a perfectly valid
    non-empty response, and handing that to ffmpeg yields the useless
    "Error opening input file".
    """
    try:
        req = urllib.request.Request(safe_url(url), headers={"Range": "bytes=0-4095"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            body = r.read(4096)
            ctype = (r.headers.get("Content-Type") or "").lower()
            html = ("html" in ctype or "json" in ctype or "xml" in ctype
                    or body[:200].lstrip()[:1] in (b"<",))
            return {"ok": bool(body) and not html, "status": r.status,
                    "ranges": r.status == 206, "ctype": ctype, "html": html,
                    "length": r.headers.get("Content-Range") or r.headers.get("Content-Length")}
    except Exception as e:
        return {"ok": False, "status": None, "ranges": False, "ctype": "",
                "html": False, "error": str(e)[:80], "length": None}


def safe_url(u):
    """Percent-encode a url's path so it can actually be requested.

    webtorrent's index lists files under their real names, and release names are
    full of spaces and brackets: "Some Film (2021) [1080p] [BluRay]/file.mp4".
    urllib refuses a url containing a raw space outright -- InvalidURL, raised
    before a single byte goes out -- so every candidate found on the index page
    failed for reasons that had nothing to do with the server.

    Unquoted before quoting, so an href that already escaped its spaces doesn't
    come back double-escaped as %2520.
    """
    try:
        p = urllib.parse.urlsplit(u)
        path = urllib.parse.quote(urllib.parse.unquote(p.path),
                                  safe="/:@!$&'()*+,;=~")
        return urllib.parse.urlunsplit((p.scheme, p.netloc, path, p.query,
                                        p.fragment))
    except ValueError:
        return u


STILL_CODECS = {"mjpeg", "png", "bmp", "gif", "webp", "tiff", "jpeg2000", "apng"}
MIN_STREAM_SECONDS = 30.0


def validate_stream_url(url, want_bytes=0):
    """Is this really the film, or just something a decoder happens to accept?

    "ffprobe read it" is a much weaker test than it looks. Torrents ship cover
    art, and mjpeg is a genuine video codec, so a single JPEG passes it -- one
    such torrent had reel transcoding WWW.YIFY-TORRENTS.COM.jpg to h264 at
    3 Mbps and reporting it as The Matrix, duration 0.04 seconds.

    want_bytes is the size of the file we actually chose, when it is known;
    anything dramatically smaller is not that file whatever it decodes as.
    """
    got = probe_media(url, timeout=20)
    v, a, _h, _hdr, _br, dur, _pix = got
    if v is None and a is None:
        return None
    if v in STILL_CODECS and a is None:
        return None                       # cover art, not a film
    # A real feature is minutes long. A stub, a sample, or a still frame is not,
    # and accepting one means silently playing the wrong thing.
    if dur is not None and dur < MIN_STREAM_SECONDS and a is None:
        return None
    if want_bytes:
        length = url_length(url)
        if length and length < want_bytes * 0.5:
            return None                   # far too small to be the chosen file
    return got


def url_length(url, timeout=6):
    """Total size behind a url, from Content-Range or Content-Length."""
    info = probe_url(url, timeout=timeout)
    raw = info.get("length") or ""
    m = re.search(r"/(\d+)\s*$", str(raw))          # "bytes 0-4095/1992052865"
    if m:
        return int(m.group(1))
    try:
        return int(raw)
    except (TypeError, ValueError):
        return None


def discover_links(base, timeout=5):
    """Pull hrefs out of an index page and resolve them correctly.

    The trailing slash is load-bearing. urljoin treats a base without one as a
    *file* and replaces its last segment, so resolving a relative href against
    ".../webtorrent/<infohash>" silently drops the infohash and every derived
    url 404s. Resolve against ".../<infohash>/" instead.
    """
    try:
        with urllib.request.urlopen(safe_url(base), timeout=timeout) as r:
            if "html" not in (r.headers.get("Content-Type") or "html"):
                return []
            body = r.read(200000).decode("utf-8", "replace")
    except Exception:
        return []
    resolve_base = base if base.endswith("/") else base + "/"
    out = []
    for href in re.findall(r'href\s*=\s*["\']([^"\']+)["\']', body):
        href = href.strip()
        if not href or href.startswith(("#", "?", "javascript:")) or href in ("/", "..", "./"):
            continue
        # Encoded here rather than at the point of use: this url is stored on the
        # job and later handed to ffmpeg and to the range proxy, both of which
        # want something requestable.
        out.append(safe_url(urllib.parse.urljoin(resolve_base, href)))
    return out


def find_wt_url(job, port, chosen):
    """webtorrent's server layout has moved between versions, so try the
    documented shapes rather than assuming one."""
    ih = job.get("wt_ih") or infohash(job.get("magnet", ""))
    name = (chosen or {}).get("name", "")
    idx = (chosen or {}).get("index", 0)
    base = f"http://127.0.0.1:{port}"
    # Multi-file torrents nest everything inside a folder named after the
    # torrent, which the file listing doesn't always show, so try that too.
    folder = urllib.parse.unquote(
        (re.search(r"[?&]dn=([^&]+)", job.get("magnet", "") or "") or [None, ""])[1]
        .replace("+", " "))
    q = lambda t: urllib.parse.quote(t, safe="/[]()!$&'*+,;=:@~")
    guesses = []
    rel = (chosen or {}).get("rel")
    cands = [name, f"{folder}/{name}" if folder and name else None]
    if rel and rel != name:
        cands.insert(0, rel)
    for n in [x for x in cands if x]:
        guesses += [f"{base}/webtorrent/{ih}/{q(n)}",
                    f"{base}/webtorrent/{ih}/{urllib.parse.quote(n)}"]
    guesses += [f"{base}/{idx}", f"{base}/webtorrent/{ih}/{idx}", f"{base}/"]
    # trailing slashes matter: see discover_links
    indexes = [f"{base}/webtorrent/{ih}/", f"{base}/webtorrent/{ih}",
               f"{base}/webtorrent/", base + "/"]
    media = VIDEO_EXT + AUDIO_EXT
    tried = {}
    # The size of the file pick_file() settled on, when the .torrent gave us one.
    # Any candidate far smaller than this is not that file, whatever it decodes
    # as -- which is how a 100 KB cover image was accepted for a 1.99 GB film.
    want_bytes = int((chosen or {}).get("size") or 0)
    stalled = []                # right-looking urls with no data behind them yet
    deadline = time.time() + WT_SERVER_WAIT
    while time.time() < deadline and not job["cancel"].is_set():
        # whatever the server actually publishes beats any guess of mine
        found = []
        for ix in indexes:
            links = discover_links(ix)
            found += links
            # /webtorrent/ lists torrents by hash; follow one level so the file
            # can be reached even if our idea of the hash is wrong
            for sub in links[:4]:
                if not sub.lower().endswith(media):
                    found += discover_links(sub if sub.endswith("/") else sub + "/")
        ranked = ([u for u in found if u.lower().endswith(media)] +
                  [u for u in found if not u.lower().endswith(media)])
        seen_once = []
        for u in ranked + guesses:
            if u not in seen_once:
                seen_once.append(u)
        for url in seen_once:
            if tried.get(url) == "media":
                continue
            info = probe_url(url, timeout=4)
            if not info["ok"]:
                err = str(info.get("error") or "")
                if "timed out" in err or "timeout" in err.lower():
                    # The server accepted the path and then had nothing to send:
                    # this is almost certainly the right file, waiting on pieces.
                    # Treating it as wrong is what sent one job onto a cover
                    # image instead. Remember it and come back.
                    tried[url] = "timed out (likely right, no data yet)"
                    stalled.append(url)
                else:
                    tried[url] = ("html/index" if info.get("html")
                                  else "http %s" % (info.get("status") or err))
                continue
            # It serves bytes. Now check they are the *chosen* file and not, say,
            # the cover art sitting next to it in the same folder.
            probed = validate_stream_url(url, want_bytes=want_bytes)
            if not probed:
                tried[url] = "not the chosen file (still image, stub, or too small)"
                continue
            tried[url] = "media"
            job["url_log"] = "; ".join(f"{u} -> {why}" for u, why in tried.items())[:1200]
            job["wt_ranges"] = bool(info["ranges"])
            job["wt_probe"] = probed
            if url in ranked:
                job["note"] = (job.get("note", "") + "; found via index").strip("; ")
            return url
        time.sleep(1.0)
    job["url_log"] = "; ".join(f"{u} -> {why}" for u, why in tried.items())[:1200]
    # Out of time, but a url that accepted the request and then stalled is the
    # file waiting on its first pieces -- worth far more than giving up and
    # falling back to piping, which costs seeking. Prefer one that looks like
    # media, and let ffmpeg wait for the data the way a player would.
    for url in ([u for u in stalled if u.lower().endswith(media)] + stalled):
        job["wt_ranges"] = True         # it answered a ranged request to stall
        job["note"] = (job.get("note", "") +
                       "; endpoint found, waiting on peers").strip("; ")
        return url
    return None


def list_torrent_files(job, magnet, port, limit):
    """Ask webtorrent what's inside, without depending on it ever exiting.

    `download` is a long-running command: some builds print the file list and
    carry on seeding. Waiting for exit therefore hides the very output we want,
    so read incrementally and stop the moment the list is parseable. It also
    needs its own port -- the default is 8000, which is us.
    """
    # --out matters even here: without it webtorrent uses the current working
    # directory, so it verifies and writes torrent data next to the script.
    probe_dir = os.path.join(DL, job["id"] + "_probe")
    os.makedirs(probe_dir, exist_ok=True)
    cmd = ["webtorrent", "download", magnet, "--select",
           "--port", str(port), "--out", probe_dir]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, bufsize=1)
    except Exception as e:
        return [], f"couldn't start webtorrent: {e}"
    job["procs"].append(proc)
    lines = []

    def read():
        try:
            for line in iter(proc.stdout.readline, ""):
                lines.append(line)
                del lines[:-200]
        except Exception:
            pass
    threading.Thread(target=read, daemon=True).start()

    files = []
    deadline = time.time() + limit
    while time.time() < deadline and not job["cancel"].is_set():
        files = parse_file_list(ANSI.sub(" ", "".join(lines)))
        if files:
            break
        if proc.poll() is not None:
            time.sleep(0.4)                     # let the reader drain
            files = parse_file_list(ANSI.sub(" ", "".join(lines)))
            break
        time.sleep(0.4)
    if proc.poll() is None:
        try:
            proc.kill()
        except Exception:
            pass
    shutil.rmtree(probe_dir, ignore_errors=True)
    return files, ANSI.sub(" ", "".join(lines)).strip()


def run_torrent(job):
    magnet = job["magnet"]
    out_dir = os.path.join(DL, job["id"] + "_wt")

    def cleanup():
        shutil.rmtree(out_dir, ignore_errors=True)

    if not has_webtorrent():
        return fail(job, "webtorrent not found. Install it with: "
                         "npm install -g webtorrent-cli")
    if not has_ffmpeg():
        return fail(job, "ffmpeg and ffprobe are required.")

    port = free_port()
    if port is None:
        return fail(job, "No free port for webtorrent's server.")
    job["wt_port"] = port
    probe_port = free_port_excluding({port}) or port
    os.makedirs(out_dir, exist_ok=True)

    # ---- 1. what's in it -----------------------------------------------------
    job["status"] = "fetching metadata"
    t_meta = time.time()
    # Preferred: fetch the .torrent once and read it locally. The streaming run
    # can then be given the file instead of the magnet, so peer discovery and
    # metadata transfer happen once rather than twice.
    files, tfile, log = fetch_metadata(job, magnet, probe_port, WT_META_TIMEOUT)
    source = tfile or magnet
    if files:
        job["note"] = "from .torrent"
    else:
        # older builds may not have downloadmeta; fall back to the listing
        files, log2 = list_torrent_files(job, magnet, probe_port, WT_META_TIMEOUT)
        log = (log + "\n" + log2).strip()
        source = magnet
    job["timings"] = {"metadata": round(time.time() - t_meta, 1)}
    job["probe_log"] = tail(log, 12, 900)
    record(job, "metadata in %.1fs, %d file(s)%s"
           % (time.time() - t_meta, len(files or []),
              " (from .torrent)" if tfile else ""))
    if job["cancel"].is_set():
        cleanup()
        job["status"] = cancel_status(job)
        return

    # A sibling created by a fan-out is pinned to its own file and must never
    # fan out again, or a three-file pack would breed one queue item per file
    # per file.
    pinned = job.get("wt_index")
    pack = [] if pinned is not None else pack_files(files)
    if pinned is not None:
        chosen = next((f for f in files if f["index"] == pinned), None) or pick_file(files)
    elif pack:
        # The first file, not the biggest: for a season the useful order is the
        # one they were meant to be watched in.
        chosen = pack[0]
    else:
        chosen = pick_file(files)

    if chosen:
        job["title"] = os.path.splitext(os.path.basename(chosen["name"]))[0]
        job["total"] = chosen["size"] or 0
        job["wt_files"] = len(files)
        job["wt_index"] = chosen["index"]
        job["note"] = (job.get("note", "") +
                       f"; file {chosen['index']} of {len(files)}").strip("; ")
        record(job, "picked file %d of %d: %s (%.2f GB)"
               % (chosen["index"], len(files), chosen["name"][:120],
                  (chosen["size"] or 0) / GB))
        if pack:
            fan_out(job, magnet, files, pack[1:])
    elif re.search(r"EADDRINUSE|address already in use", log, re.I):
        cleanup()
        return fail(job, "webtorrent couldn't open a port: " + tail(log, 2, 140))
    elif not log:
        # genuinely nothing came back
        cleanup()
        return fail(job, "No response from webtorrent in %ds -- no peers found "
                         "for that magnet yet." % WT_META_TIMEOUT)
    else:
        # It said something we couldn't parse. Carry on with the first file
        # rather than refusing outright, and keep the output for diagnosis.
        chosen = {"index": 0, "name": "", "size": 0}
        job["note"] = "couldn't read the file list; using file 0"

    # ---- 2. start it streaming ----------------------------------------------
    job["status"] = "starting"
    # A note of what this directory is for. Without it a restart leaves the
    # partial download orphaned -- bytes counted against the cap that nothing
    # can reach or resume.
    try:
        with open(os.path.join(out_dir, ".reel.json"), "w") as f:
            _json.dump({"magnet": magnet, "index": chosen["index"],
                        "title": job["title"], "total": job["total"]}, f)
    except OSError:
        pass

    t_start = time.time()
    cmd = ["webtorrent", "download", source, "--out", out_dir,
           "--select", str(chosen["index"]), "--port", str(port),
           "--keep-seeding"]
    # A prefetch gets a rate cap so it can never outbid the stream.
    if job.get("prefetch") and PREFETCH_KBPS:
        cmd += ["--download-limit", str(PREFETCH_KBPS)]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
    except Exception as e:
        cleanup()
        return fail(job, f"Couldn't start webtorrent: {e}")
    job["procs"].append(proc)
    job["wt_proc"] = proc
    # Both pipes must be drained continuously. Without --quiet webtorrent draws a
    # redrawing UI, and an unread pipe would eventually block the process dead.
    errbuf = []
    tailbuf = []

    def drain(stream, keep):
        try:
            for line in iter(stream.readline, ""):
                keep.append(line)
                del keep[:-40]
                got = parse_stats(line)
                if "peers" in got:
                    job["peers"] = got["peers"]
                if "uploaded" in got:
                    job["uploaded"] = got["uploaded"]
                if "up_rate" in got:
                    job["up_rate"] = got["up_rate"]
                # keep the raw shape available: if the patterns above miss, this
                # shows what the client actually printed
                job["wt_tail"] = tail(ANSI.sub(" ", "".join(keep)), 6, 400)
        except Exception:
            pass
    threading.Thread(target=drain, args=(proc.stderr, errbuf), daemon=True).start()
    threading.Thread(target=drain, args=(proc.stdout, tailbuf), daemon=True).start()

    job["status"] = "connecting"
    t_connect = time.time()
    job["timings"]["spawn"] = round(t_connect - t_start, 1)
    url = find_wt_url(job, port, chosen)
    job["timings"]["find_url"] = round(time.time() - t_connect, 1)
    if job["cancel"].is_set():
        cleanup()
        job["status"] = cancel_status(job)
        return
    if not url:
        # No usable endpoint. Rather than give up, fall back to piping the file
        # out of webtorrent sequentially -- documented, and independent of
        # whatever url layout this build uses. Costs seeking, not playback.
        rc = proc.poll()
        job["note"] = (job.get("note", "") + "; no http endpoint, piping instead").strip("; ")
        for pr in list(job["procs"]):
            if pr.poll() is None:
                try:
                    pr.kill()
                except Exception:
                    pass
        if run_torrent_pipe(job, magnet, chosen, out_dir):
            return
        detail = tail(ANSI.sub(" ", "".join(errbuf + tailbuf)), 4, 200)
        cleanup()
        return fail(job, ("webtorrent exited (code %s). %s" % (rc, detail)) if rc is not None
                    else "No playable endpoint on port %d and piping failed. %s"
                         % (port, detail))

    job["wt_url"] = url

    # Wait for the swarm to actually deliver something before asking anything to
    # read this url. The endpoint can be correct while entirely empty -- that is
    # what find_wt_url's stalled-url fallback returns -- and probing an empty
    # stream wastes 20s, then encoding one wastes another 90s, and the job ends
    # blaming ffmpeg for a swarm that never connected.
    t_wait = time.time()
    while time.time() - t_wait < WT_DATA_WAIT and not job["cancel"].is_set():
        note_progress(job, tree_bytes(out_dir))
        if job["received"] >= WT_DATA_MIN or job.get("wt_done"):
            break
        if proc.poll() is not None:
            break
        time.sleep(0.5)
    job["timings"]["first_bytes"] = round(time.time() - t_wait, 1)
    if job["received"] < WT_DATA_MIN and not job.get("wt_done"):
        stop_procs(job)
        if not tree_bytes(out_dir):
            cleanup()          # nothing worth keeping, and it counts against the cap
        peers = job.get("peers")
        return fail(job, "No data from the swarm in %ds%s. The endpoint was found, "
                         "so this is the torrent, not reel -- try one with more "
                         "seeders." % (WT_DATA_WAIT,
                                       "" if peers is None else " (%d peers)" % peers))

    t_probe = time.time()

    # ---- 3. proxy directly, or convert on the fly ---------------------------
    probed = job.get("wt_probe") or probe_media(url, timeout=20)
    v, a, vh, hdr, br, dur, pix = probed
    # A probe run while the swarm is still starved comes back empty -- not because
    # the file is unreadable, but because the pieces holding its header have not
    # arrived yet. That answer used to be final: the file was declared un-direct
    # and transcoded for its whole length. Seen on an h264/aac mp4 that needed no
    # conversion at all -- 871 MB of live encode beside 864 MB of download, with
    # ffmpeg at 61%, producing what the browser would have played as it arrived.
    # So when the probe learns nothing, wait for the download to be moving and ask
    # again before committing to an encode that cannot be undone.
    if v is None and a is None and not job["cancel"].is_set():
        for _ in range(int(WT_REPROBE_WAIT / 2)):
            if job["cancel"].is_set():
                break
            note_progress(job, tree_bytes(out_dir))
            if job["received"] >= WT_REPROBE_MIN or job.get("wt_done"):
                break
            time.sleep(2.0)
        again = probe_media(url, timeout=25)
        if again[0] is not None or again[1] is not None:
            probed = again
            v, a, vh, hdr, br, dur, pix = probed
            job["wt_probe"] = probed
            job["note"] = (job.get("note", "") + "; codecs identified on a "
                           "second look").strip("; ")
    job["bitrate"], job["duration"] = br, dur
    job["kind"] = "audio" if (a and not v) else "video"
    # The container matters as much as the codecs, and only the Drive path was
    # checking it (browser_ready does; this did not). No browser can demux
    # Matroska whatever is inside it, so an h264/AAC .mkv served straight
    # through was marked seekable, skipped finalizing, and then simply refused
    # to play -- silent failure, which is worse than an unnecessary remux.
    ext = os.path.splitext(urllib.parse.unquote(
        urllib.parse.urlparse(url).path))[1].lower()
    if not ext:
        ext = os.path.splitext((chosen or {}).get("name") or "")[1].lower()
    direct = (job.get("wt_ranges") and ext in BROWSER_CONTAINERS
              and (v is None or (v in BROWSER_VIDEO and pix_ok(pix)))
              and (a in BROWSER_AUDIO or a is None)
              and (v is not None or a is not None))
    job["wt_codecs"] = f"{v or '-'}/{a or '-'}"
    job["timings"]["probe"] = round(time.time() - t_probe, 1)
    # The whole verdict on one line, because every part of it is a reason the
    # file might refuse to play and each was previously reported somewhere else.
    record(job, "probed in %.1fs: %s/%s %s %s, ranges=%s -> %s"
           % (time.time() - t_probe, v or "-", a or "-", pix or "-",
              ext or "no ext", bool(job.get("wt_ranges")),
              "direct stream" if direct else "needs conversion"))

    # Look for subtitles now, by name, rather than waiting for the download to
    # land. Nothing here reads the file, so it costs one request -- and waiting
    # meant a two-hour film had none until it had finished arriving, which is
    # exactly when they stop being useful. The hooks at completion still run and
    # will upgrade this to an exact hash match if one exists.
    start_subs(job, None, name=(chosen or {}).get("name") or job.get("title"))
    if direct:
        # Best case: hand the browser webtorrent's own ranged stream. Seeking
        # works immediately and no transcode happens at all.
        job["wt_direct"] = True
        job["streamable"] = True
        job["live_ready"] = True
        job["status"] = "streaming"
        job["timings"]["total"] = round(time.time() - t_meta, 1)
        job["note"] = (job.get("note", "") + "; direct stream, seekable").strip("; ")
    else:
        # Codec or container the browser won't take. ffmpeg reads the *seekable*
        # http url, so where the index sits no longer matters.
        job["streamable"] = True
        job["status"] = "downloading"
        # Nothing to preview when every byte is already here -- a restored
        # torrent, or one that finished while the endpoint was being found.
        # Finalizing goes straight to a seekable file and, because the video is
        # only copied, takes seconds; the live encode it replaces re-encoded the
        # whole film at about realtime and wrote several GB to say the same
        # thing. This is what made a fully-downloaded film look stuck for hours.
        already = bool(job["total"]) and tree_bytes(out_dir) >= job["total"] * 0.999
        if already:
            job["wt_done"] = True
            job["note"] = (job.get("note", "") +
                           "; already downloaded, finalizing").strip("; ")
        else:
            start_live_from_url(job, url, job["kind"], v, vh, hdr, pix)
            deadline = time.time() + 90
            while time.time() < deadline and not job["cancel"].is_set():
                lf = job.get("live_file")
                if lf and os.path.exists(lf) and os.path.getsize(lf) >= LIVE_OPEN:
                    job["live_ready"] = True
                    job["status"] = "streaming"
                    job["timings"]["total"] = round(time.time() - t_meta, 1)
                    break
                if job.get("live_done"):
                    break
                time.sleep(0.4)
            if not job.get("live_ready"):
                # Stop the encoder first. Without this it outlives the job and
                # keeps reading a webtorrent server that has already gone, which
                # left a stray ffmpeg running minutes after the row said failed.
                stop_procs(job)
                if not tree_bytes(out_dir):
                    cleanup()      # keep any real bytes so a retry can resume
                return fail(job, "Couldn't convert the torrent stream from %s -- %s"
                            % (url, tail(job.get("live_note", ""), 3, 220)
                               or "ffmpeg produced nothing"))

    # ---- 4. follow progress -------------------------------------------------
    while not job["cancel"].is_set():
        if proc.poll() is not None and not job.get("wt_done"):
            job["wt_done"] = True
        note_progress(job, tree_bytes(out_dir))
        if job["total"] and job["received"] >= job["total"] * 0.999:
            job["wt_done"] = True
        if job.get("wt_done"):
            break
        time.sleep(1.0)

    if job["cancel"].is_set():
        cleanup()
        job["status"] = cancel_status(job)
        return
    job["status"] = "streaming"

    # A direct stream never finalizes, so it never reaches the hook below. Its
    # download is the release itself and stays on disk, which makes this the
    # only place to hash it.
    if job.get("wt_direct"):
        done_src = locate_downloaded_file(out_dir, chosen)
        if done_src:
            start_subs(job, done_src, name=os.path.basename(done_src))

    # ---- 5. finalize into a seekable file, if this one needed transcoding ---
    # A direct stream is already seekable -- webtorrent's own ranged proxy,
    # unmodified. Everything else only ever had the fragmented live copy,
    # which plays start to finish but can never be scrubbed, for as long as
    # the item exists. This is what closes that gap.
    if not job.get("wt_direct"):
        finalize_torrent(job, out_dir, chosen)


def locate_downloaded_file(out_dir, chosen):
    """Where the picked file actually landed on disk.

    Usually known exactly, from the .torrent's own file list. The one case it
    isn't is the fallback where that list couldn't be parsed at all (chosen
    ends up {"index": 0, "name": "", "size": 0} -- see run_torrent) and the
    only way left to find the file is to look for it.
    """
    name = (chosen or {}).get("name")
    if name:
        p = os.path.join(out_dir, name)
        if os.path.isfile(p):
            return p
    best, best_size = None, -1
    media = VIDEO_EXT + AUDIO_EXT
    for root, _dirs, files in os.walk(out_dir):
        for f in files:
            if not f.lower().endswith(media):
                continue
            p = os.path.join(root, f)
            try:
                size = os.path.getsize(p)
            except OSError:
                continue
            if size > best_size:
                best, best_size = p, size
    return best


def adopt_finalized(job, out_dir, src, out):
    """Make `out` the item's finished file and clear away everything it replaces.

    Shared by both finalize paths so they cannot drift: the one that converts,
    and the one that discovers no conversion was needed.
    """
    # The live encode is now redundant: the player will swap to this file, and
    # left alone that process keeps re-encoding the whole film to write a
    # preview nobody will watch. sweep_live() only ever deleted its file, and
    # only after a delay -- it never stopped the writer.
    lp = job.get("live_proc")
    if lp and lp.poll() is None:
        try:
            lp.kill()
        except Exception:
            pass
        job["live_done"] = True

    # Stop seeding and reclaim the raw download: the finished file replaces it
    # entirely, the same trade a Drive item makes when its _raw folder goes.
    # Unlike Drive's _raw, this one was also serving uploads, so it has to be
    # stopped before it can be removed.
    wp = job.get("wt_proc")
    if wp and wp.poll() is None:
        try:
            wp.kill()
        except Exception:
            pass
    # Hashed before the folder goes: subtitles are matched against the release
    # as downloaded, and once this is a remux it matches nothing upstream.
    start_subs(job, src if os.path.isfile(src) else out,
               name=os.path.basename(src))
    shutil.rmtree(out_dir, ignore_errors=True)
    try:
        with open(os.path.join(DL, job["id"] + ".magnet"), "w") as f:
            f.write(job.get("magnet") or "")
    except OSError:
        pass

    job["path"] = out
    job["total"] = os.path.getsize(out)
    job["received"] = job["total"]
    job["status"] = "done"
    # What the finished file actually holds, so a client can tell before it
    # presses play whether it needs the compat rendition instead -- the same
    # fields run_job() sets for a Drive conversion.
    ov, _oa, _oh, _ohdr, _ob, _od, opix = probe_media(out)
    job["vcodec"], job["vpix"] = ov, opix
    job["play_key"] = codec_key(ov, opix)
    if job.get("live_file"):
        sweep_live(job)
    enforce_cache_cap()


def finalize_torrent(job, out_dir, chosen):
    """Convert a fully-downloaded torrent into a seekable file, the same way
    run_job() finalizes a Drive download -- reading the local copy rather than
    the network, so ffmpeg can seek and re-read it freely instead of taking a
    single realtime pass over a streamed URL.

    Native-first, exactly like Drive's conversion: the source codec is kept
    whenever MP4 can carry it, regardless of whether today's viewer can decode
    it -- a device that can't asks for the compat rendition on demand (see
    start_compat()), same as a Drive item. This is also why an HEVC/EAC3
    torrent finalizes quickly rather than taking as long as the live encode
    did: the video is only copied, not re-encoded -- just the audio, which no
    browser decodes natively, needs transcoding.

    Failure here is not fatal. The live fragment stream this replaces was
    already working; a failed finalize should leave that playable, not break it.
    """
    src = locate_downloaded_file(out_dir, chosen)
    if not src or not os.path.isfile(src):
        job["note"] = (job.get("note", "") + "; no local file to finalize").strip("; ")
        return

    # Ask again before converting anything. The verdict that this file needed
    # converting was reached when wt_direct came out False, and that can be a
    # probe which learned nothing because the swarm had not delivered the header
    # yet -- not a real judgement about the file. The whole thing is here now,
    # so the question is finally answerable.
    #
    # Worth the check even beyond the wasted pass: a remux holds the source and
    # its output at once, and that doubling is what pushed the folder over the
    # cache cap and got a conversion killed mid-run. A move needs neither.
    if browser_ready(src):
        ext = os.path.splitext(src)[1].lower() or ".mp4"
        stem = re.sub(r"[^\w.\- ]", "_", job["title"])[:110]
        out = os.path.join(DL, f"{job['id']}__torrent__{stem}{ext}")
        job["note"] = (job.get("note", "") +
                       "; played as downloaded, no conversion needed").strip("; ")
        try:
            shutil.move(src, out)
        except OSError as e:
            fail(job, "Couldn't keep the downloaded file: %s" % e)
            return
        adopt_finalized(job, out_dir, src, out)
        return

    job["status"] = "converting"
    v, a, h, hdr, _br, dur, pix = probe_media(src)
    dur = job.get("duration") or dur
    acodec = ["-c:a", "copy"] if a in BROWSER_AUDIO else ["-c:a", "aac"]
    caps = ({codec_key(v, pix)} | MP4_VIDEO) if v in MP4_VIDEO else set()
    vargs, vfilter, vnote = video_args(v, h, hdr, live=False, pix=pix, caps=caps)
    if vnote:
        job["note"] = (job.get("note", "") + "; " + vnote).strip("; ")
    safe_title = re.sub(r"[^\w.\- ]", "_", job["title"])[:110]
    out = os.path.join(DL, f"{job['id']}__torrent__{safe_title}.mp4")
    r = run_with_progress(
        job, ["ffmpeg", "-nostdin", "-y", "-progress", "pipe:1", "-nostats",
              "-i", src, "-map", "0:v:0", "-map", "0:a:0?",
              *vfilter, *vargs, *acodec, "-movflags", "+faststart", out], dur)

    if job["cancel"].is_set():
        try:
            os.remove(out)
        except OSError:
            pass
        # drop() and enforce_cache_cap() already update the job's status
        # themselves before this notices. The janitor's overflow fallback does
        # not -- it only sets this flag -- so without an explicit transition
        # here the job is left stranded at 'converting' forever, with nothing
        # left running to finish it. fail() gives that specific case the same
        # message run_job() already uses for the identical situation; anything
        # else (evicted/removed) just confirms what the canceller already set.
        if job.get("overflow") and not job.get("evicted"):
            fail(job, "Stopped -- cache is full. Raise the limit or remove items.")
        else:
            job["status"] = cancel_status(job)
        return

    if r.returncode != 0 or not os.path.exists(out) or os.path.getsize(out) == 0:
        try:
            os.remove(out)
        except OSError:
            pass
        # Only claim it's still watchable if a live copy actually exists. When
        # the live phase was skipped because the download was already complete,
        # this is the only path to playback, so a failure here is a real failure
        # and saying otherwise would leave a dead row looking fine.
        if job.get("live_file") and job.get("live_ready"):
            job["status"] = "streaming"
            job["note"] = (job.get("note", "") +
                           "; couldn't finalize a seekable copy, still playable "
                           "live: " + tail(r.stderr, 2, 160)).strip("; ")
        else:
            fail(job, "Couldn't convert the downloaded file: "
                      + (tail(r.stderr, 2, 200) or "ffmpeg produced nothing"))
        return

    adopt_finalized(job, out_dir, src, out)


def run_torrent_pipe(job, magnet, chosen, out_dir):
    """webtorrent --stdout | ffmpeg -i pipe:0 -> fragmented mp4.

    The fallback when no http endpoint can be validated. Sequential, so there's
    no seeking until it finishes, but it depends on nothing but a documented flag.
    """
    port = free_port() or 8899
    wt = ["webtorrent", "download", magnet, "--select", str(chosen["index"]),
          "--out", out_dir, "--port", str(port), "--stdout", "--quiet"]
    try:
        src = subprocess.Popen(wt, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except Exception as e:
        job["live_note"] = f"pipe fallback: {e}"
        return False
    job["procs"].append(src)
    job["wt_proc"] = src

    # Give the on-disk copy a moment so the codecs can be identified; without
    # that we'd have to guess whether the video needs transcoding.
    v = a = h = None
    hdr = False
    for _ in range(40):
        f = newest_file(out_dir)
        if f and disk_bytes(f) > 512 * 1024:
            v, a, h, hdr = codecs_of(f)
            if v or a:
                break
        if job["cancel"].is_set() or src.poll() is not None:
            break
        time.sleep(0.5)
    job["kind"] = "audio" if (a and not v) else "video"
    vargs, vfilter, vnote = video_args(v, h, hdr)
    if vnote:
        job["note"] = (job.get("note", "") + "; " + vnote).strip("; ")

    if job["kind"] == "audio":
        out = os.path.join(DL, job["id"] + ".live.mp3")
        ff = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
              "-progress", "pipe:1", "-nostats", "-i", "pipe:0", "-vn",
              "-c:a", "libmp3lame", "-q:a", "4", "-flush_packets", "1",
              "-f", "mp3", out]
    else:
        out = os.path.join(DL, job["id"] + ".live.mp4")
        ff = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
              "-progress", "pipe:1", "-nostats", "-i", "pipe:0", *vfilter, *vargs,
              "-c:a", "aac", "-ac", "2", "-f", "mp4",
              "-movflags", "+frag_keyframe+empty_moov+default_base_moof",
              "-frag_duration", "1500000", "-flush_packets", "1", out]
    try:
        enc = subprocess.Popen(ff, stdin=src.stdout, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True)
    except Exception as e:
        job["live_note"] = f"pipe fallback ffmpeg: {e}"
        return False
    src.stdout.close()               # ffmpeg owns the read end now
    job["procs"].append(enc)
    job["live_file"] = out
    job["live_kind"] = job["kind"]
    job["wt_ranges"] = False
    job["wt_direct"] = False

    def watch():
        try:
            for line in iter(enc.stdout.readline, ""):
                k, _, val = line.strip().partition("=")
                if k == "speed":
                    try:
                        job["encode_speed"] = float(val.strip().rstrip("x"))
                    except ValueError:
                        pass
        except Exception:
            pass
        enc.wait()
        job["live_done"] = True
        size = os.path.getsize(out) if os.path.exists(out) else 0
        if enc.returncode != 0 or size < LIVE_OPEN:
            err = enc.stderr.read() if enc.stderr else ""
            job["live_note"] = "pipe rc=%s %s bytes; %s" % (enc.returncode, size,
                                                            tail(err, 3, 200))
    threading.Thread(target=watch, daemon=True).start()

    deadline = time.time() + 120
    while time.time() < deadline and not job["cancel"].is_set():
        if os.path.exists(out) and os.path.getsize(out) >= LIVE_OPEN:
            job["live_ready"] = True
            job["streamable"] = True
            job["status"] = "streaming"
            threading.Thread(target=follow_pipe_progress, args=(job, out_dir),
                             daemon=True).start()
            return True
        if job.get("live_done"):
            break
        time.sleep(0.4)
    return False


def follow_pipe_progress(job, out_dir):
    while not job["cancel"].is_set():
        note_progress(job, tree_bytes(out_dir))
        if job["total"] and job["received"] >= job["total"] * 0.999:
            job["wt_done"] = True
            break
        time.sleep(1.0)


def start_live_from_url(job, url, kind, vcodec=None, height=None, hdr=False,
                        pix=None):
    """Same fragmented output as the Drive path, but reading a seekable URL."""
    if kind == "audio":
        out = os.path.join(DL, job["id"] + ".live.mp3")
        cmd = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
               "-i", url, "-vn", "-c:a", "libmp3lame", "-q:a", "4",
               "-flush_packets", "1", "-f", "mp3", out]
    else:
        out = os.path.join(DL, job["id"] + ".live.mp4")
        vargs, vfilter, vnote = video_args(vcodec, height, hdr, pix=pix)
        if vnote:
            job["note"] = (job.get("note", "") + "; " + vnote).strip("; ")
        cmd = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
               "-progress", "pipe:1", "-nostats",
               "-i", url, *vfilter, *vargs, "-c:a", "aac", "-ac", "2", "-f", "mp4",
               "-movflags", "+frag_keyframe+empty_moov+default_base_moof",
               "-frag_duration", "1500000", "-flush_packets", "1", out]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
    except OSError as e:
        job["live_note"] = str(e)
        return
    job["procs"].append(proc)
    # Kept separately from procs so finalize_torrent can stop just this one.
    # Left running, it re-encodes the entire film to produce a preview of
    # something already superseded by the finalized file.
    job["live_proc"] = proc
    job["live_file"] = out
    job["live_kind"] = kind

    def progress():
        """ffmpeg reports speed=N.NNx; below 1.0 it is losing to realtime."""
        try:
            for line in iter(proc.stdout.readline, ""):
                k, _, val = line.strip().partition("=")
                if k == "speed":
                    try:
                        job["encode_speed"] = float(val.strip().rstrip("x"))
                    except ValueError:
                        pass
                elif k == "out_time_us":
                    try:
                        job["encoded_s"] = int(val) / 1e6
                    except ValueError:
                        pass
        except Exception:
            pass
    threading.Thread(target=progress, daemon=True).start()

    def watch():
        proc.wait()
        err = proc.stderr.read() if proc.stderr else ""
        job["live_done"] = True
        size = os.path.getsize(out) if os.path.exists(out) else 0
        if proc.returncode != 0 or size < LIVE_OPEN:
            job["live_note"] = "rc=%s, %s bytes; %s" % (proc.returncode, size,
                                                        tail(err, 3, 200))
    threading.Thread(target=watch, daemon=True).start()


def compat_path_for(job):
    """Two files, the same two phases the live path uses: fragments that can be
    served while they are written, then a faststart copy that can be seeked."""
    return (os.path.join(DL, job["id"] + ".compat.live.mp4"),
            os.path.join(DL, job["id"] + ".compat.mp4"))


def finalize_compat(job, frag, seekable):
    """Turn the finished fragments into a seekable file. A stream copy, so it
    costs seconds -- without it a client on the fallback path could play but
    never scrub, which is worse than what this replaced."""
    r = subprocess.run(
        ["ffmpeg", "-nostdin", "-y", "-hide_banner", "-loglevel", "error",
         "-i", frag, "-c", "copy", "-movflags", "+faststart", seekable],
        capture_output=True)
    if r.returncode == 0 and os.path.exists(seekable) and os.path.getsize(seekable):
        job["compat_path"] = seekable
        record(job, "compatibility copy finished, seekable (%.2f GB)"
               % (os.path.getsize(seekable) / GB))
        sweep_file(frag, LIVE_GRACE)     # let anyone mid-stream finish first
    else:
        job["compat_note"] = tail(r.stderr.decode("utf-8", "replace"), 2, 160)
        record(job, "compatibility copy failed: " + job["compat_note"][:160])


def sweep_file(path, delay):
    def go():
        time.sleep(delay)
        try:
            os.remove(path)
        except OSError:
            pass
    threading.Thread(target=go, daemon=True).start()


def start_compat(job):
    """Make an H264/AAC copy of a finished item, for a client that can't decode
    what we kept.

    Written as fragments so it can be served while it is still being produced --
    the same trick the live phase uses. Waiting for a ten-minute encode before
    the first frame would be worse than the transcode-everything behaviour this
    replaces.
    """
    src = job.get("path")
    if not src or not os.path.isfile(src):
        return False
    with LOCK:
        if job.get("compat_proc") or job.get("compat_path"):
            return True                      # already running, or already there
        out, seekable = compat_path_for(job)
        job["compat_file"] = out
        job["compat_seekable_path"] = seekable
        job["compat_done"] = False
        job["compat_pct"] = 0.0
    _v, _a, _h, _hdr, _br, dur, _pix = probe_media(src)
    acodec = ["-c:a", "copy"] if _a in BROWSER_AUDIO else ["-c:a", "aac", "-ac", "2"]
    vargs, vfilter, _n = video_args(_v, _h, _hdr, pix=_pix, caps=set(BROWSER_VIDEO))
    cmd = ["ffmpeg", "-nostdin", "-hide_banner", "-loglevel", "error",
           "-progress", "pipe:1", "-nostats", "-i", src,
           "-map", "0:v:0", "-map", "0:a:0?", *vfilter, *vargs, *acodec,
           "-f", "mp4",
           "-movflags", "+frag_keyframe+empty_moov+default_base_moof",
           "-frag_duration", "1500000", "-flush_packets", "1", out]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=False)
    except OSError as e:
        job["compat_note"] = str(e)[:200]
        return False
    job["procs"].append(proc)
    job["compat_proc"] = proc
    threading.Thread(target=read_progress,
                     args=(job, proc.stdout, "compat_speed", dur, "compat_pct"),
                     daemon=True).start()

    def watch():
        proc.wait()
        err = proc.stderr.read().decode("utf-8", "replace") if proc.stderr else ""
        size = os.path.getsize(out) if os.path.exists(out) else 0
        job["compat_proc"] = None
        if proc.returncode == 0 and size >= LIVE_OPEN:
            job["compat_ready"] = True       # a short file can finish before the
            job["compat_done"] = True        # poller below ever sees it exist
            finalize_compat(job, out, seekable)
        else:
            job["compat_done"] = True
            job["compat_ready"] = False
            job["compat_note"] = "rc=%s, %s bytes; %s" % (proc.returncode, size,
                                                          tail(err, 3, 200))
        enforce_cache_cap()
    threading.Thread(target=watch, daemon=True).start()

    # Ready to serve as soon as there is a fragment to send. Checks the size
    # once more after the encoder exits, so a file that finished between two
    # polls is still noticed.
    def open_when_playable():
        deadline = time.time() + 300
        while time.time() < deadline and not job["cancel"].is_set():
            done = job.get("compat_done")
            try:
                if os.path.getsize(out) >= LIVE_OPEN:
                    job["compat_ready"] = True
                    return
            except OSError:
                pass
            if done:
                return
            time.sleep(0.3)
    threading.Thread(target=open_when_playable, daemon=True).start()
    return True


def worker():
    while True:
        jid = WORK_Q.get()
        with LOCK:
            job = JOBS.get(jid)
        if job and not job["cancel"].is_set():
            try:
                if job.get("source") == "torrent":
                    run_torrent(job)
                else:
                    run_job(job)
            except Exception as e:
                fail(job, str(e))
        WORK_Q.task_done()


def drop(jid, delete_file=True):
    with LOCK:
        job = JOBS.pop(jid, None)
    if not job:
        return
    job["cancel"].set()
    stop_procs(job)
    for d in job_dirs(jid):
        shutil.rmtree(d, ignore_errors=True)
    targets = ([job.get("live_file"), job.get("compat_file"),
                job.get("compat_path"), os.path.join(DL, jid + ".magnet"),
                subs_path_for(jid, job.get("subs_lang"))]
               + ([job.get("path")] if delete_file else []))
    for f in targets:
        if f:
            try:
                os.remove(f)
            except OSError:
                pass


# ---- http --------------------------------------------------------------------

class H(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "reel"

    def log_message(self, *a):
        pass

    def handle(self):
        """Swallow client disconnects for the whole keep-alive loop.

        The common one is a reset arriving while an idle connection waits on the
        next request line, which http.server lets escape as an exception. Doing
        this here rather than only in the server's handle_error means it holds
        however the handler is served.
        """
        try:
            super().handle()
        except GONE:
            self.close_connection = True

    def finish(self):
        try:
            super().finish()
        except GONE:
            pass

    def _json(self, code, body):
        b = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)

    def _local_origin(self):
        """Browsers can't send application/json cross-origin without a preflight,
        but reject stray origins anyway so another page can't drive this server.

        Same-origin is checked against the Host the browser actually used rather
        than a fixed list: on a phone that's the LAN address, and hard-coding
        loopback would refuse every device except this one.
        """
        o = self.headers.get("Origin")
        if not o:
            return True
        h = urllib.parse.urlparse(o).hostname
        mine = urllib.parse.urlparse("//" + (self.headers.get("Host") or "")).hostname
        return h in ("localhost", "127.0.0.1", "::1") or (h and h == mine)

    def do_GET(self):
        p = urllib.parse.urlparse(self.path).path
        if p == "/":
            b = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Security-Policy",
                             "default-src 'none'; media-src 'self'; "
                             "style-src 'unsafe-inline'; script-src 'unsafe-inline'; "
                             "connect-src 'self'")
            self.send_header("Content-Length", str(len(b)))
            self.end_headers()
            self.wfile.write(b)
        elif p == "/jobs":
            with LOCK:
                self._json(200, [public(j) for j in JOBS.values()])
        elif p.startswith("/log/"):
            # Fetched on demand rather than ridden along with /jobs, which is
            # polled every second.
            jid = urllib.parse.unquote(p[len("/log/"):])
            with LOCK:
                job = JOBS.get(jid)
                events = list(job.get("log") or ()) if job else None
            if events is None:
                self._json(404, {"error": "no such job"})
            else:
                self._json(200, {"id": jid, "events": events})
        elif p == "/debug":
            def jsonable(v):
                try:
                    _json.dumps(v)
                    return True
                except (TypeError, ValueError):
                    return False   # Events, Popen handles, etc.
            with LOCK:
                rows = [{k: v for k, v in j.items() if jsonable(v)}
                        for j in JOBS.values()]
            try:
                listing = sorted(
                    (f, os.path.getsize(os.path.join(DL, f)))
                    for f in os.listdir(DL) if os.path.isfile(os.path.join(DL, f)))
            except OSError:
                listing = []
            self._json(200, {"jobs": rows, "files": listing,
                             "ffmpeg": shutil.which("ffmpeg"),
                             "ffprobe": shutil.which("ffprobe"),
                             "python": sys.version.split()[0],
                             "tunables": {"LIVE_HEAD": LIVE_HEAD, "LIVE_OPEN": LIVE_OPEN,
                                          "LIVE_GIVEUP": LIVE_GIVEUP}})
        elif p == "/sys":
            self._json(200, {"rclone": has_rclone(), "ffmpeg": has_ffmpeg(),
                             "webtorrent": has_webtorrent(),
                             "cap_gb": CACHE_CAP_GB,
                             "used_gb": round(folder_size_bytes() / GB, 3),
                             # null tells the client there's nothing to scan:
                             # REEL_HOST=127.0.0.1, or no active network.
                             "lan_url": lan_url() if has_qrcode() else None})
        elif p == "/qr":
            self._qr()
        elif p.startswith("/subs/"):
            self._subs(p.split("/subs/", 1)[1].split("?")[0])
        elif p.startswith("/stream/"):
            q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            self._stream(p.split("/stream/", 1)[1].split("?")[0],
                         compat=q.get("compat", ["0"])[0] == "1")
        elif p.startswith("/live/"):
            self._live(p.split("/live/", 1)[1].split("?")[0])
        else:
            self._json(404, {"error": "not found"})

    def do_POST(self):
        if not self._local_origin():
            return self._json(403, {"error": "forbidden"})
        p = urllib.parse.urlparse(self.path).path
        n = int(self.headers.get("Content-Length", 0) or 0)
        try:
            body = json.loads(self.rfile.read(n).decode()) if n else {}
        except Exception:
            body = {}

        if p == "/caps":
            # The browser reports what it can actually decode. Asked of the
            # browser rather than guessed from the user agent, which is wrong
            # often enough to matter -- HEVC support in particular varies by
            # device and by whether hardware decoding is present.
            note_caps(body.get("client"), body.get("caps"))
            return self._json(200, {"ok": True})

        if p == "/search":
            # Nothing is started here -- this only looks. The chosen magnet
            # comes back through /add like any other, so the download path is
            # the existing one, unchanged.
            results, err, dropped, per = search_torrents(body.get("q"))
            return self._json(200, {"results": results, "error": err,
                                    "dropped": dropped, "sources": per})

        if p == "/feed":
            # Nothing starts here either -- this only suggests. Chosen rows go
            # through /add exactly like a search result or a pasted magnet.
            shelves, err, per = recommendations(force=bool(body.get("force")))
            with LOCK:
                have = {infohash(j["magnet"]) for j in JOBS.values() if j.get("magnet")}
            # Shown as "already queued" rather than hidden: a familiar film
            # missing from the list looks like a bad recommendation engine,
            # where a greyed-out one explains itself.
            out = [dict(s, films=[dict(f, queued=f["infohash"] in have)
                                  for f in s["films"]]) for s in shelves]
            return self._json(200, {"shelves": out, "error": err, "sources": per})

        if p == "/add":
            magnets, ids, bad = split_sources(body.get("links"))
            caps = sorted(caps_of(body.get("client")))
            added = []
            for uri in magnets:
                job = new_job(None, source="torrent", magnet=uri, caps=caps,
                              title="magnet " + infohash(uri)[:8])
                record(job, "added as a torrent: " + infohash(uri)[:12])
                with LOCK:
                    JOBS[job["id"]] = job
                added.append(job["id"])      # scheduler decides when it starts
            for did in ids:
                job = new_job(did, caps=caps)
                record(job, "added as a Drive file: " + str(did)[:60])
                with LOCK:
                    JOBS[job["id"]] = job
                added.append(job["id"])
            self._json(200, {"added": added, "bad": bad,
                             "torrents": len(magnets), "links": len(ids)})

        elif p == "/retry":
            # Re-fetch an evicted or failed row, keeping its place in the queue.
            jid = body.get("id")
            with LOCK:
                job = JOBS.get(jid)
                ok = bool(job and (job.get("drive_id") or job.get("magnet"))
                          and job["status"] in ("error", "evicted", "removed"))
                if ok:
                    job.update(status="queued", error="", received=0, total=0,
                               path=None, overflow=False, streamable=None,
                               live_file=None, live_ready=False, live_done=False,
                               live_kind=None, live_note="", dl_done=False,
                               procs=[], wt_url=None, wt_direct=False,
                               wt_done=False, wt_proc=None, uploaded=None,
                               up_rate=None, rate=None, headroom=None,
                               evicted=False)
                    job["cancel"] = threading.Event()
            if ok:
                with LOCK:
                    job["hold"] = False
                WORK_Q.put(jid)
            self._json(200, {"ok": ok})

        elif p == "/start":
            jid = body.get("id")
            with LOCK:
                job = JOBS.get(jid)
                ok = bool(job and job.get("hold"))
                if ok:
                    job["prefetch"] = False    # asked for deliberately
                    job["note"] = "started by hand"
                    release(job)
            self._json(200, {"ok": ok})

        elif p == "/playing":
            jid = body.get("id")
            try:
                at = float(body.get("at") or 0)
            except (TypeError, ValueError):
                at = 0.0
            # Falls back to the peer address so a client that predates the id --
            # or one with localStorage turned off -- still counts as a viewer
            # rather than silently sharing a slot with everyone else.
            note_playing(body.get("client") or self.client_address[0], jid, at)
            with LOCK:
                job = JOBS.get(jid)
                if job:
                    job["last_played"] = time.time()
                    job["prefetch"] = False    # it's the feature now, not a prefetch
                    if not job.get("caps") and body.get("client"):
                        # Whoever is actually watching decides how the live phase
                        # is produced: copied for a device that can decode the
                        # source, encoded for one that cannot.
                        job["caps"] = sorted(caps_of(body.get("client")))
                    if job.get("paused"):
                        pause_proc(job.get("wt_proc") or job.get("proc"), False)
                        job["paused"] = False
                    if job.get("hold") and job["status"] == "queued":
                        release(job)           # clicked something not started yet
            self._json(200, {"ok": True})

        elif p == "/remove":
            drop(body.get("id"))
            self._json(200, {"ok": True})

        elif p == "/setcap":
            global CACHE_CAP_GB
            try:
                val = float(body.get("cap_gb", CACHE_CAP_GB))
                if 1 <= val <= 2000:
                    with CAP_LOCK:
                        CACHE_CAP_GB = round(val, 1)
                    enforce_cache_cap()
            except (TypeError, ValueError):
                pass
            self._json(200, {"cap_gb": CACHE_CAP_GB,
                             "used_gb": round(folder_size_bytes() / GB, 3)})
        else:
            self._json(404, {"error": "not found"})

    def _subs(self, jid):
        """Serve the WebVTT sidecar. The id may arrive with the .vtt suffix the
        <track> element requests, or without."""
        jid = jid[:-4] if jid.endswith(".vtt") else jid
        with LOCK:
            job = JOBS.get(jid)
        if not job:
            return self._json(404, {"error": "unknown item"})
        path = subs_path_for(jid, job.get("subs_lang"))
        if not os.path.isfile(path):
            return self._json(404, {"error": "no subtitles"})
        try:
            with open(path, "rb") as f:
                body = f.read()
        except OSError:
            return self._json(404, {"error": "no subtitles"})
        self.send_response(200)
        self.send_header("Content-Type", "text/vtt; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _qr(self):
        """A QR for the LAN address, so a phone can scan its way in instead of
        typing an IP. 404s (rather than erroring) when qrcode isn't installed
        or there's nothing on the LAN to share -- both are normal states, not
        failures, matching /stream and /live's use of an ordinary response code
        for "nothing to serve yet."""
        if not has_qrcode():
            return self._json(404, {"error": "qrcode not installed"})
        url = lan_url()
        if not url:
            return self._json(404, {"error": "no LAN address to share"})
        svg = qr_svg(url)
        self.send_response(200)
        self.send_header("Content-Type", "image/svg+xml")
        self.send_header("Content-Length", str(len(svg)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(svg)

    def _live(self, jid, live_file=None, ready_key="live_ready",
              done_key="live_done"):
        """Serve the fragmented copy while ffmpeg is still writing it.

        No Content-Length and no ranges — the length isn't known yet, so the
        response runs until the writer finishes and the connection closes.

        The compat rendition is written exactly the same way, so it is served
        through here too rather than duplicating the loop.
        """
        with LOCK:
            job = JOBS.get(jid)
        if not job:
            return self._json(404, {"error": "unknown item"})
        lf = live_file or job.get("live_file")
        if not (job.get(ready_key) and lf and os.path.isfile(lf)):
            self.send_response(503)
            self.send_header("Retry-After", "1")
            self.send_header("Content-Length", "0")
            self.end_headers()
            return

        job["last_played"] = time.time()
        with STREAM_LOCK:
            STREAMING[jid] = STREAMING.get(jid, 0) + 1
        self.close_connection = True
        try:
            self.send_response(200)
            self.send_header("Content-Type",
                             "audio/mpeg" if lf.endswith(".mp3") else "video/mp4")
            self.send_header("Accept-Ranges", "none")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()

            idle = 0.0
            with open(lf, "rb") as f:
                while True:
                    chunk = f.read(65536)
                    if chunk:
                        idle = 0.0
                        try:
                            self.wfile.write(chunk)
                        except (BrokenPipeError, ConnectionResetError):
                            return
                        continue
                    try:
                        at_end = f.tell() >= os.fstat(f.fileno()).st_size
                    except OSError:
                        return
                    if job.get(done_key) and at_end:
                        return                       # writer finished; so are we
                    if job["cancel"].is_set() or idle >= LIVE_IDLE:
                        return
                    time.sleep(0.2)
                    idle += 0.2
        finally:
            with STREAM_LOCK:
                STREAMING[jid] = max(0, STREAMING.get(jid, 1) - 1)

    def _proxy(self, jid, job, upstream):
        """Pass the browser's Range straight through to webtorrent and relay the
        reply. It already prioritises the pieces covering the requested bytes,
        so seeking works before the torrent has finished."""
        headers = {}
        rng = self.headers.get("Range")
        if rng:
            headers["Range"] = rng
        job["last_played"] = time.time()
        with STREAM_LOCK:
            STREAMING[jid] = STREAMING.get(jid, 0) + 1
        try:
            req = urllib.request.Request(upstream, headers=headers)
            with urllib.request.urlopen(req, timeout=30) as up:
                self.send_response(up.status)
                for h in ("Content-Type", "Content-Length", "Content-Range",
                          "Accept-Ranges"):
                    v = up.headers.get(h)
                    if v:
                        self.send_header(h, v)
                if not up.headers.get("Content-Type"):
                    self.send_header("Content-Type", ctype_for(
                        job.get("wt_url") or ".mp4"))
                if not up.headers.get("Accept-Ranges"):
                    self.send_header("Accept-Ranges", "bytes")
                self.end_headers()
                while True:
                    chunk = up.read(262144)
                    if not chunk:
                        break
                    try:
                        self.wfile.write(chunk)
                    except GONE:
                        return
        except GONE:
            return
        except Exception:
            # upstream vanished mid-stream; tell the player to retry
            try:
                self.send_response(503)
                self.send_header("Retry-After", "1")
                self.send_header("Content-Length", "0")
                self.end_headers()
            except Exception:
                pass
        finally:
            with STREAM_LOCK:
                STREAMING[jid] = max(0, STREAMING.get(jid, 1) - 1)

    def _stream(self, jid, compat=False):
        with LOCK:
            job = JOBS.get(jid)
            path = job.get("path") if job else None
        if not job:
            return self._json(404, {"error": "unknown item"})
        if compat:
            # This client can't decode what we kept. Build the H264 copy if it
            # isn't there yet and stream it as it is written, so playback still
            # starts in seconds rather than after the whole encode.
            cp = job.get("compat_path")
            if cp and os.path.isfile(cp):
                path = cp                      # finished: seekable, ranges below
            else:
                start_compat(job)
                # Hold the request until there is a first fragment to send,
                # rather than bouncing the player off a 503 and relying on it to
                # come back. The encoder only needs a second or two to get that
                # far, and a media element that gives up retrying stays broken.
                deadline = time.time() + COMPAT_WAIT
                while (time.time() < deadline and not job.get("compat_ready")
                       and not job.get("compat_done")
                       and not job["cancel"].is_set()):
                    time.sleep(0.25)
                return self._live(jid, live_file=job.get("compat_file"),
                                  ready_key="compat_ready",
                                  done_key="compat_done")
        if not path and job.get("wt_direct") and job.get("wt_url"):
            return self._proxy(jid, job, job["wt_url"])
        if not path or not os.path.isfile(path):
            self.send_response(503)
            self.send_header("Retry-After", "1")
            self.send_header("Content-Length", "0")
            self.end_headers()
            return

        job["last_played"] = time.time()  # keeps it safe from eviction
        with STREAM_LOCK:
            STREAMING[jid] = STREAMING.get(jid, 0) + 1
        try:
            size = os.path.getsize(path)
            rng = self.headers.get("Range")
            start, end = 0, size - 1
            if rng:
                m = re.match(r"bytes=(\d+)-(\d*)", rng)
                if m:
                    start = min(int(m.group(1)), max(size - 1, 0))
                    if m.group(2):
                        end = int(m.group(2))
            end = min(end, size - 1)
            length = max(end - start + 1, 0)

            self.send_response(206 if rng else 200)
            self.send_header("Content-Type", ctype_for(path))
            self.send_header("Accept-Ranges", "bytes")
            self.send_header("Content-Length", str(length))
            if rng:
                self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
            self.end_headers()
            with open(path, "rb") as f:
                f.seek(start)
                left = length
                while left > 0:
                    chunk = f.read(min(262144, left))
                    if not chunk:
                        break
                    try:
                        self.wfile.write(chunk)
                    except GONE:
                        return
                    left -= len(chunk)
        finally:
            with STREAM_LOCK:
                STREAMING[jid] = max(0, STREAMING.get(jid, 1) - 1)


PAGE = r"""<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>reel</title>
<style>
  :root{
    --ink:#101214; --panel:#171A1D; --raise:#1D2126; --rule:#262B31;
    --text:#DDE1E5; --dim:#8C939B; --faint:#585F67;
    --brass:#C6A265; --live:#7FA98A; --warn:#C08A4A; --bad:#C4756A;
    --mono:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,monospace;
    --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Inter,system-ui,sans-serif;
  }
  *{box-sizing:border-box;margin:0;padding:0}
  html{-webkit-text-size-adjust:100%}
  body{background:var(--ink);color:var(--text);font-family:var(--sans);
    font-size:13.5px;line-height:1.5;-webkit-font-smoothing:antialiased;
    display:flex;justify-content:center;padding:0 20px 72px}
  .wrap{width:100%;max-width:760px}
  ::selection{background:rgba(198,162,101,.25)}
  :focus-visible{outline:1px solid var(--brass);outline-offset:2px}

  .eyebrow{font:500 10.5px/1 var(--mono);letter-spacing:.14em;
    text-transform:uppercase;color:var(--faint)}

  /* masthead */
  header{display:flex;align-items:baseline;gap:14px;
    padding:26px 0 12px;border-bottom:1px solid var(--rule)}
  header .mark{font:500 15px/1 var(--mono);letter-spacing:.06em;color:var(--text)}
  header .state{margin-left:auto;display:flex;align-items:center;gap:8px;
    font:400 11.5px/1 var(--mono);color:var(--dim)}
  .led{width:6px;height:6px;border-radius:50%;background:var(--faint);flex:none}
  .led.on{background:var(--live)}
  /* only shown once /sys confirms there's an address worth sharing */
  .qrbtn{height:24px;padding:0 10px;font:500 10.5px/1 var(--mono);
    letter-spacing:.1em;border-radius:4px;background:var(--raise);
    border:1px solid var(--rule);color:var(--dim)}
  .qrbtn:hover{color:var(--text);border-color:#3B434C}
  /* Compact and out of the way: it is a thing you glance at once to pair a
     phone, not part of the interface you use. */
  .qrpop{margin:10px 0 0 auto;padding:9px;background:var(--panel);
    border:1px solid var(--rule);border-radius:6px;display:flex;
    align-items:center;gap:10px;width:max-content;max-width:100%}
  .qrimg{width:96px;height:96px;background:#fff;border-radius:3px;
    padding:5px;display:flex;flex:none}
  .qrimg svg{width:100%;height:100%;display:block}
  .qrurl{font:400 11px/1.4 var(--mono);color:var(--dim);word-break:break-all}

  /* intake */
  form{display:flex;gap:8px;align-items:flex-start;margin:20px 0 0}
  textarea{flex:1;background:var(--panel);border:1px solid var(--rule);
    border-radius:5px;color:var(--text);font-family:var(--mono);font-size:12.5px;
    line-height:1.65;padding:10px 12px;resize:none;min-height:40px;max-height:132px;
    transition:border-color .12s}
  textarea::placeholder{color:var(--faint);font-family:var(--sans);font-size:13px}
  textarea:focus{outline:none;border-color:#39414A}
  button{font-family:var(--sans);font-size:12.5px;cursor:pointer;
    background:var(--raise);color:var(--text);border:1px solid var(--rule);
    border-radius:5px;padding:0 16px;height:40px;white-space:nowrap;
    transition:border-color .12s,color .12s,background .12s}
  button:hover:not(:disabled){border-color:#3B434C;background:#22272C}
  button:disabled{color:var(--faint);cursor:default}

  /* search results */
  .results{margin-top:10px;background:var(--panel);border:1px solid var(--rule);
    border-radius:5px;padding:6px;max-height:340px;overflow-y:auto;
    font-size:12.5px;color:var(--dim)}
  .rhead{font:400 10.5px/1 var(--mono);letter-spacing:.08em;color:var(--faint);
    text-transform:uppercase;padding:8px 8px 10px}
  .rrow{display:flex;flex-direction:column;align-items:flex-start;gap:4px;
    width:100%;height:auto;text-align:left;padding:9px 8px;background:none;
    border:none;border-radius:4px;border-bottom:1px solid var(--rule)}
  .rrow:hover:not(:disabled){background:var(--raise);border-color:var(--rule)}
  .rrow:last-child{border-bottom:none}
  .rtitle{font-size:12.5px;color:var(--text);word-break:break-word;
    white-space:normal;line-height:1.45}
  .rmeta{font:400 11px/1.4 var(--mono);color:var(--faint);
    font-variant-numeric:tabular-nums;white-space:normal}
  .rrow.toobig .rtitle{color:var(--dim)}
  .rrow.toobig .rmeta{color:var(--warn)}
  .rrow:disabled{opacity:.5}

  /* picks */
  .pickbtn{font:500 10.5px/1 var(--mono);letter-spacing:.1em;text-transform:uppercase;
    color:var(--faint);background:none;border:1px solid var(--rule);border-radius:4px;
    padding:4px 8px}
  .pickbtn:hover{color:var(--text);border-color:var(--dim)}
  .picks{margin-top:8px;background:var(--panel);border:1px solid var(--rule);
    border-radius:5px;padding:6px;max-height:420px;overflow-y:auto;
    font-size:12.5px;color:var(--dim)}
  /* every shelf but the first gets a rule above it, so the sections read as
     sections rather than as one long list with headings in it */
  .picks .rhead:not(:first-child){border-top:1px solid var(--rule);
    margin-top:8px;padding-top:16px}
  .picks .rhead{color:var(--brass)}
  .rrank{font:500 11px/1 var(--mono);color:var(--faint);letter-spacing:.06em}
  .rwhy{font:400 10.5px/1.4 var(--mono);color:var(--dim);white-space:normal}
  .rrow .rscore{color:var(--live)}

  /* stage */
  .stage{margin-top:16px;position:relative;aspect-ratio:16/9;background:#000;
    border:1px solid var(--rule);border-radius:5px;overflow:hidden}
  .stage video{position:absolute;inset:0;width:100%;height:100%;display:block}
  .slate{position:absolute;inset:0;display:grid;place-content:center;
    justify-items:center;gap:9px;text-align:center;padding:20px}
  .slate .bars{display:flex;gap:3px;align-items:flex-end;height:16px}
  .slate .bars i{width:3px;background:#2A3037;display:block}
  .slate p{font:400 11.5px/1.6 var(--mono);color:#3E454D;letter-spacing:.05em}
  .flag{position:absolute;left:12px;top:11px;z-index:2;display:none;
    font:500 10px/1 var(--mono);letter-spacing:.14em;text-transform:uppercase;
    color:var(--faint);background:rgba(16,18,20,.82);border:1px solid var(--rule);
    border-radius:3px;padding:5px 8px}

  /* transport */
  .transport{display:flex;align-items:center;gap:8px;margin-top:12px}
  .transport button{height:32px;padding:0 12px;font-size:12px}
  .cue{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;
    font-size:12.5px;color:var(--dim);padding-left:4px}
  .cue.none{color:var(--faint)}
  .toggle{display:flex;align-items:center;gap:7px;font-size:12px;color:var(--dim);
    cursor:pointer;white-space:nowrap;user-select:none}
  .toggle input{accent-color:var(--brass);width:14px;height:14px;cursor:pointer}

  /* swarm health for whatever is playing */
  .wire{display:flex;align-items:center;gap:9px;margin-top:11px;padding:9px 11px;
    background:var(--panel);border:1px solid var(--rule);border-radius:5px}
  .lamp{width:6px;height:6px;border-radius:50%;background:var(--faint);flex:none}
  .lamp.ok{background:var(--live)}
  .lamp.tight{background:var(--warn)}
  .lamp.behind{background:var(--bad)}
  .verdict{font-size:12.5px;color:var(--dim)}
  .figures{margin-left:auto;font:400 11.5px/1 var(--mono);color:var(--faint);
    font-variant-numeric:tabular-nums;text-align:right}

  /* queue */
  .section{display:flex;align-items:baseline;gap:10px;margin:30px 0 2px}
  .section .count{font:400 11px/1 var(--mono);color:var(--faint)}
  ul{list-style:none}
  li.row{display:grid;grid-template-columns:26px 1fr auto 26px;align-items:center;
    gap:12px;padding:11px 4px;border-bottom:1px solid var(--rule);cursor:pointer;
    transition:background .1s}
  li.row:hover{background:var(--panel)}
  /* the log lives inside the row's grid, spanning it, so opening one does not
     disturb the columns */
  .logbtn{font:400 10px/1 var(--mono);letter-spacing:.08em;color:var(--faint);
    background:none;border:1px solid var(--rule);border-radius:3px;padding:3px 5px}
  .logbtn:hover{color:var(--text);border-color:var(--dim)}
  .logbtn.on{color:var(--brass);border-color:var(--brass)}
  .logpanel{grid-column:1/-1;margin:8px 0 2px;padding:8px 10px;
    background:var(--ink);border:1px solid var(--rule);border-radius:4px;
    max-height:230px;overflow-y:auto;font:400 11px/1.6 var(--mono);
    color:var(--dim);white-space:normal}
  .logline{display:flex;gap:10px;align-items:baseline}
  .logat{color:var(--faint);flex:0 0 auto;min-width:46px;text-align:right;
    font-variant-numeric:tabular-nums}
  li.row.live{background:var(--panel)}
  li.row.live .n{color:var(--brass)}
  li.row.live .title{color:var(--text)}
  .n{font:400 11px/1 var(--mono);color:var(--faint);text-align:right;
    font-variant-numeric:tabular-nums}
  .body{min-width:0}
  .title{font-size:13px;color:var(--dim);overflow:hidden;text-overflow:ellipsis;
    white-space:nowrap}
  .track{height:2px;margin-top:7px;background:var(--rule);border-radius:1px;
    overflow:hidden;display:none}
  .track.show{display:block}
  .track i{display:block;height:100%;width:0;background:var(--brass);
    transition:width .3s linear}
  .track.busy i{width:34%;animation:slide 1.15s ease-in-out infinite}
  @keyframes slide{0%{transform:translateX(-110%)}100%{transform:translateX(330%)}}
  .note.quiet{color:var(--faint)}
  .note{font-size:11.5px;color:var(--bad);margin-top:6px;
    white-space:pre-wrap;word-break:break-word}
  .flags{display:flex;align-items:center;gap:10px}
  .kind{font:400 10px/1 var(--mono);letter-spacing:.1em;color:var(--faint);
    text-transform:uppercase}
  .kind.now{color:var(--brass)}
  /* only appears when more than this device is on the item */
  .eyes{font:400 10px/1 var(--mono);letter-spacing:.08em;color:var(--live);
    border:1px solid rgba(127,169,138,.35);border-radius:3px;padding:3px 5px;
    white-space:nowrap;display:none}
  .eyes.on{display:inline-block}
  .cc{font:500 9.5px/1 var(--mono);letter-spacing:.1em;color:var(--faint);
    border:1px solid var(--rule);border-radius:3px;padding:3px 4px;display:none}
  .cc.on{display:inline-block}
  .cc.found{color:var(--brass);border-color:rgba(198,162,101,.4)}
  .cc.rough{color:var(--warn);border-color:rgba(192,138,74,.4)}
  .stat{font:400 11.5px/1 var(--mono);color:var(--dim);
    font-variant-numeric:tabular-nums;text-align:right;min-width:74px}
  .stat.ready{color:var(--live)}
  .stat.bad{color:var(--bad)}
  .stat.idle{color:var(--faint)}
  .kill{background:none;border:none;height:auto;padding:4px;color:var(--faint);
    font-size:15px;line-height:1;border-radius:4px}
  .kill:hover{background:none;border:none;color:var(--bad)}
  .blank{padding:26px 4px;font-size:12.5px;color:var(--faint)}

  /* capacity — the meter is the one flourish: 48 ticks, like a level readout */
  .cache{margin-top:32px;padding-top:16px;border-top:1px solid var(--rule)}
  .cache .head{display:flex;align-items:baseline;gap:10px;margin-bottom:11px}
  .cache .read{margin-left:auto;font:400 11.5px/1 var(--mono);color:var(--text);
    font-variant-numeric:tabular-nums}
  .cache .read span{color:var(--faint)}
  .meter{display:flex;gap:2px;height:14px;align-items:stretch}
  .meter i{flex:1;background:var(--rule);border-radius:1px;
    transition:background .35s}
  .meter i.f{background:var(--brass)}
  .meter i.f.hot{background:var(--warn)}
  .limit{display:flex;align-items:center;gap:8px;margin-top:13px}
  .limit label{font-size:12px;color:var(--dim)}
  .limit input{width:62px;height:30px;background:var(--panel);
    border:1px solid var(--rule);border-radius:4px;color:var(--text);
    font-family:var(--mono);font-size:12px;padding:0 8px;text-align:right}
  .limit input:focus{outline:none;border-color:#39414A}
  .limit .u{font:400 11.5px/1 var(--mono);color:var(--faint)}
  .limit button{margin-left:auto;height:30px;padding:0 12px;font-size:12px}

  @media (max-width:600px){
    .transport{flex-wrap:wrap}
    .cue{order:3;flex-basis:100%;padding:0}
    li.row{grid-template-columns:20px 1fr auto 20px;gap:9px}
    .stat{min-width:0}
    .flags{flex-direction:column;align-items:flex-end;gap:3px}
  }
  @media (prefers-reduced-motion:reduce){
    *{animation:none!important;transition:none!important}
  }
</style></head><body>
<div class="wrap">
  <header>
    <span class="mark">reel</span>
    <button class="qrbtn" id="qrbtn" type="button" hidden aria-label="Show QR code for this address">QR</button>
    <span class="state"><i class="led" id="led"></i><span id="statetext">checking</span></span>
  </header>
  <div class="qrpop" id="qrpop" hidden>
    <div class="qrimg" id="qrimg"></div>
    <span class="qrurl" id="qrurl"></span>
  </div>

  <form id="intake" autocomplete="off">
    <textarea id="links" rows="1" placeholder="Search by name, or paste Drive links / magnet URIs"></textarea>
    <button type="submit">Add</button>
  </form>
  <div class="results" id="results" hidden></div>

  <div class="stage">
    <span class="flag" id="flag">audio only</span>
    <div class="slate" id="slate">
      <span class="bars" id="bars"></span>
      <p>nothing playing</p>
    </div>
    <video id="v" controls playsinline hidden></video>
  </div>

  <div class="transport">
    <button id="prev" disabled>Previous</button>
    <button id="next" disabled>Next</button>
    <span class="cue none" id="cue">Queue is empty</span>
    <label class="toggle"><input type="checkbox" id="auto" checked> Play next automatically</label>
  </div>

  <div class="wire" id="wire" hidden>
    <span class="lamp" id="lamp"></span>
    <span class="verdict" id="verdict"></span>
    <span class="figures" id="figures"></span>
  </div>

  <div class="section">
    <span class="eyebrow">Queue</span><span class="count" id="qcount"></span>
  </div>
  <ul id="list"><li class="blank">Paste a Drive link above to get started.</li></ul>

  <div class="section">
    <span class="eyebrow">Picks</span><span class="count" id="pcount"></span>
    <button class="pickbtn" id="picktog" type="button" aria-expanded="false">Show</button>
    <button class="pickbtn" id="pickref" type="button" hidden>Refresh</button>
  </div>
  <div class="picks" id="picks" hidden></div>

  <div class="cache">
    <div class="head">
      <span class="eyebrow">Cache</span>
      <span class="read" id="read">— <span>of — GB</span></span>
    </div>
    <div class="meter" id="meter"></div>
    <div class="limit">
      <label for="cap">Keep at most</label>
      <input type="number" id="cap" min="1" max="2000" step="1" aria-label="Cache limit in gigabytes">
      <span class="u">GB</span>
      <button id="savecap">Update limit</button>
    </div>
  </div>
</div>
<script>
const TICKS = 48;
const $ = id => document.getElementById(id);
const v = $('v'), slate = $('slate'), flag = $('flag'), cue = $('cue');
let jobs = [], order = [], cur = -1, retries = 0, live = false, wantPlay = false;
let subsOn = false;   // whether a track is currently attached

// decorative slate bars + capacity meter ticks
(() => {
  const h = [7,12,16,10,14,6,11,15,9,13];
  $('bars').innerHTML = h.map(n => `<i style="height:${n}px"></i>`).join('');
  $('meter').innerHTML = Array.from({length: TICKS}, () => '<i></i>').join('');
})();

const api = async (u, b) => {
  const r = await fetch(u, b ? {method:'POST', headers:{'Content-Type':'application/json'},
                                body: JSON.stringify(b)} : {});
  return r.json();
};
const bytes = n => {
  if (!n) return '0 B';
  const u = ['B','KB','MB','GB']; let i = 0;
  while (n >= 1024 && i < 3) { n /= 1024; i++; }
  return (i >= 2 ? n.toFixed(1) : Math.round(n)) + ' ' + u[i];
};
const byId = id => jobs.find(j => j.id === id);
let reported = 0;
function reportPlaying(force) {
  if (cur < 0 || !order[cur]) return;
  const now = Date.now();
  if (!force && now - reported < 3000) return;
  reported = now;
  api('/playing', {id: order[cur], at: v.currentTime || 0,
                   client: clientId}).catch(() => {});
}
v.addEventListener('timeupdate', () => reportPlaying(false));
// 'done' plays the seekable file; 'live' plays the fragments as they're written
const canPlay = j => !!j && (j.status === 'done' || j.status === 'streaming' || j.live);

/* What this device can actually decode ------------------------------------
   Asked of the browser, never inferred from the user agent: HEVC support turns
   on hardware that a string cannot tell you about. canPlayType answers
   'probably', 'maybe' or '' — only 'probably' is a real yes. */
const CODEC_TESTS = {
  h264:   'video/mp4; codecs="avc1.640028"',
  h264_10:'video/mp4; codecs="avc1.6e0028"',
  hevc:   'video/mp4; codecs="hvc1.1.6.L120.90"',
  hevc10: 'video/mp4; codecs="hvc1.2.4.L120.90"',
  vp9:    'video/mp4; codecs="vp09.00.10.08"',
  av1:    'video/mp4; codecs="av01.0.08M.08"',
};
// server-side names: codec_key() appends '10' for a 10-bit stream
const CAP_NAME = {h264:'h264', h264_10:'h26410', hevc:'hevc', hevc10:'hevc10',
                  vp9:'vp9', av1:'av1'};
const myCaps = (() => {
  const probe = document.createElement('video'), out = [];
  for (const k in CODEC_TESTS) {
    if (probe.canPlayType(CODEC_TESTS[k]) === 'probably') out.push(CAP_NAME[k]);
  }
  if (!out.includes('h264')) out.push('h264');   // every browser we support
  return out;
})();
let clientId = localStorage.getItem('reel.cid');
if (!clientId) {
  clientId = Math.random().toString(36).slice(2) + Date.now().toString(36);
  localStorage.setItem('reel.cid', clientId);
}
api('/caps', {client: clientId, caps: myCaps}).catch(() => {});

// True when this device can decode what the server kept for an item.
const playsHere = j => !j.play_key || myCaps.includes(j.play_key);
// Needs the H264 rendition, and it isn't seekable yet: still fragments.
const onCompatFragments = j => !playsHere(j) && !j.compat_seekable;
// a torrent served straight from webtorrent is seekable, so it uses /stream
const srcOf = j => {
  if (j.status === 'done' || j.seekable) {
    // Can't decode the native file: ask for the H264 rendition instead. It is
    // built on demand and streamed while it is written, so this still starts
    // in seconds rather than after a full encode.
    return '/stream/' + j.id + (playsHere(j) ? '' : '?compat=1');
  }
  return '/live/' + j.id;
};

/* intake ------------------------------------------------------------------ */
const ta = $('links');
const grow = () => { ta.style.height = 'auto';
                     ta.style.height = Math.min(ta.scrollHeight, 130) + 'px'; };
ta.addEventListener('input', grow);
/* Anything that looks like a link or a magnet is added, as before. Anything
   else is treated as something to search for, which is why typing a film's
   name now finds it instead of reporting that it wasn't a Drive link. */
const looksLikeSource = t => {
  const s = t.trim();
  if (/magnet:\?|drive\.google\.|docs\.google\.|[?&]id=|\/file\/d\//i.test(s)) return true;
  if (/^[0-9a-fA-F]{40}$/.test(s)) return true;             // bare infohash
  // A bare Drive id is 20+ characters, which a long run-together title also
  // is: "harrypotterandthegobletoffire" would otherwise be fetched as an id
  // and fail. Real ids always mix case or carry a digit / - / _; a title
  // typed as one lowercase word never does.
  return /^[a-zA-Z0-9_-]{20,}$/.test(s) && /[A-Z0-9_-]/.test(s);
};

$('intake').addEventListener('submit', async e => {
  e.preventDefault();
  const text = ta.value.trim();
  if (!text) return;
  if (!looksLikeSource(text)) return runSearch(text);
  const r = await api('/add', {links: text, client: clientId});
  (r.added || []).forEach(id => { if (!order.includes(id)) order.push(id); });
  ta.value = ''; grow();
  if (r.bad) {
    cue.textContent = r.bad + (r.bad === 1 ? ' link' : ' links') + " didn't look like Drive links";
    cue.classList.add('none');
  }
  refresh();
});

/* search ------------------------------------------------------------------- */
const fmtSize = n => !n ? '?' : (n >= 1e9 ? (n/1e9).toFixed(1)+' GB' : Math.round(n/1e6)+' MB');

async function runSearch(q) {
  const box = $('results');
  box.hidden = false;
  box.textContent = 'Searching for ' + q + '…';
  let r;
  try { r = await api('/search', {q}); }
  catch (e) { box.textContent = 'Search failed.'; return; }
  box.textContent = '';
  if (r.error) { box.textContent = r.error; return; }
  const rows = r.results || [];
  if (!rows.length) { box.textContent = 'Nothing found for ' + q + '.'; return; }

  const head = document.createElement('div');
  head.className = 'rhead';
  // Say what was withheld: silently returning 6 of 19 rows looks like a thin
  // index rather than a deliberate filter.
  const srcs = r.sources ? Object.entries(r.sources)
        .filter(([,v]) => typeof v === 'number' && v > 0).map(([k]) => k) : [];
  head.textContent = rows.length + ' results for "' + q + '" · most seeded first'
      + (srcs.length ? ' · ' + srcs.length + ' sources' : '')
      + (r.dropped ? ' · ' + r.dropped + ' with no seeders hidden' : '');
  box.append(head);

  rows.forEach(res => {
    const row = document.createElement('button');
    row.className = 'rrow';
    row.type = 'button';
    if (!res.fits || res.weak) row.classList.add('toobig');

    const title = document.createElement('span');
    title.className = 'rtitle';
    // The index truncates its own name field mid-word, so prefer the real
    // filename when the lookup found one -- it's complete, and it carries the
    // codec and release group the truncated version loses.
    title.textContent = res.real_name || res.name;   // textContent, never HTML

    const meta = document.createElement('span');
    meta.className = 'rmeta';
    /* A tilde means the count came from an indexer's cache rather than from the
       trackers. Worth distinguishing: those caches were out by 2x across the
       board, and by 50x on one row -- 203 claimed against 4 real. */
    const seedTxt = (res.verified ? '' : '~') + res.seeders + ' seed'
                  + (res.weak ? ' — too few to stream' : '');
    const bits = [seedTxt, fmtSize(res.size)];
    if (res.res) bits.push(res.res);
    // Worth saying when the title shown is one file out of several -- a
    // trilogy pack would otherwise look like a single film.
    if (res.files > 1) bits.push(res.files + ' files');
    // The genuinely useful hint, and the one no torrent site can give you,
    // because it depends on this machine rather than on the file.
    bits.push(res.direct ? 'plays directly' :
              res.codec === 'hevc' ? 'needs remux' :
              res.codec ? res.codec + ', may need remux' : 'unknown codec');
    if (res.hdr) bits.push('HDR');
    if (!res.fits) bits.push('≠ needs ~' + fmtSize(res.peak) + ', over your cache cap');
    meta.textContent = bits.join('  ·  ');

    row.append(title, meta);
    row.addEventListener('click', async () => {
      row.disabled = true;
      title.textContent = 'Adding: ' + res.name;
      const add = await api('/add', {links: res.magnet, client: clientId});
      (add.added || []).forEach(id => { if (!order.includes(id)) order.push(id); });
      box.hidden = true; box.textContent = '';
      ta.value = ''; grow();
      refresh();
    });
    box.append(row);
  });
}

/* picks --------------------------------------------------------------------
   A shelf rather than a search: what to watch, when you don't already know.
   Collapsed by default and only fetched when opened, so the page costs nothing
   extra to load and nothing is requested on your behalf until you ask. */
let picksLoaded = false;

function pickRow(res) {
  const row = document.createElement('button');
  row.className = 'rrow';
  row.type = 'button';
  if (!res.fits || res.weak || res.queued) row.classList.add('toobig');
  if (res.queued) row.disabled = true;

  const title = document.createElement('span');
  title.className = 'rtitle';
  title.textContent = res.title + (res.year ? ' (' + res.year + ')' : '');

  const meta = document.createElement('span');
  meta.className = 'rmeta';
  const bits = [];
  // The rating is the reason this is a recommendation rather than a listing,
  // so it leads -- and says outright when there isn't one, since an absent
  // rating and a bad one should never look the same.
  bits.push(res.rating ? '★ ' + res.rating.toFixed(1)
                       + (res.votes ? ' (' + res.votes.toLocaleString() + ')' : '')
                       : 'no rating');
  bits.push((res.verified ? '' : '~') + res.seeders + ' seed'
            + (res.weak ? ' — too few to stream' : ''));
  bits.push(fmtSize(res.size));
  if (res.res) bits.push(res.res);
  bits.push(res.direct ? 'plays directly' :
            res.codec === 'hevc' ? 'needs remux' :
            res.codec ? res.codec + ', may need remux' : 'unknown codec');
  if (res.hdr) bits.push('HDR');
  if (!res.fits) bits.push('needs ~' + fmtSize(res.peak) + ', over your cache cap');
  if (res.queued) bits.push('already in your queue');
  meta.textContent = bits.join('  ·  ');

  // Why this one was picked, in the same words the ranking used -- a list of
  // suggestions with no stated reason is just an ordering you have to trust.
  const why = document.createElement('span');
  why.className = 'rwhy';
  why.textContent = (res.why || []).join(' · ');

  row.append(title, meta);
  if (why.textContent) row.append(why);
  if (!res.queued) row.addEventListener('click', async () => {
    row.disabled = true;
    title.textContent = 'Adding: ' + res.title;
    const add = await api('/add', {links: res.magnet, client: clientId});
    (add.added || []).forEach(id => { if (!order.includes(id)) order.push(id); });
    meta.textContent = 'added to your queue';
    row.classList.add('toobig');
    refresh();
  });
  return row;
}

async function loadPicks(force) {
  const box = $('picks');
  box.textContent = force ? 'Refreshing…' : 'Finding something worth watching…';
  let r;
  try { r = await api('/feed', force ? {force: true} : {}); }
  catch (e) { box.textContent = 'Could not load picks.'; return; }
  box.textContent = '';
  picksLoaded = true;
  if (r.error) { box.textContent = r.error; return; }
  const shelves = r.shelves || [];
  const total = shelves.reduce((n, s) => n + s.films.length, 0);
  $('pcount').textContent = total ? total + ' films' : '';
  if (!total) { box.textContent = 'Nothing to suggest right now.'; return; }

  // A film sits on exactly one shelf, so these read as sections of a list
  // rather than as four rankings of the same few titles.
  shelves.forEach(shelf => {
    const head = document.createElement('div');
    head.className = 'rhead';
    head.textContent = shelf.name + ' — ' + shelf.note;
    box.append(head);
    shelf.films.forEach(res => box.append(pickRow(res)));
  });
}

$('picktog').addEventListener('click', () => {
  const box = $('picks'), open = box.hidden;
  box.hidden = !open;
  $('pickref').hidden = !open;
  $('picktog').textContent = open ? 'Hide' : 'Show';
  $('picktog').setAttribute('aria-expanded', open ? 'true' : 'false');
  if (open && !picksLoaded) loadPicks(false);
});
$('pickref').addEventListener('click', () => loadPicks(true));

/* subtitles ----------------------------------------------------------------
   v.load() discards any existing text tracks, so this is re-applied after each
   one rather than set up once. Late arrivals need no special case: the poll
   below calls it again, so a subtitle found after playback started simply
   appears. */
function applySubs(j) {
  [...v.querySelectorAll('track')].forEach(t => t.remove());
  if (!j || !j.subs) return;
  const t = document.createElement('track');
  t.kind = 'subtitles';
  t.label = (j.subs_lang || 'en').toUpperCase();
  t.srclang = (j.subs_lang || 'eng').slice(0, 2);
  t.src = '/subs/' + j.id + '.vtt';
  t.default = true;
  v.append(t);
  // Chrome ignores the default attribute on a track added after load, so the
  // mode is set explicitly once the element registers it.
  setTimeout(() => { try { if (v.textTracks[0]) v.textTracks[0].mode = 'showing'; }
                     catch (e) {} }, 0);
}

/* playback ---------------------------------------------------------------- */
function setFlag(j) {
  if (live) { flag.textContent = 'live \u00b7 still downloading'; flag.style.display = 'block'; }
  else if (j && j.kind === 'audio') { flag.textContent = 'audio only'; flag.style.display = 'block'; }
  else flag.style.display = 'none';
}

function play(i) {
  if (i < 0 || i >= order.length) return;
  const id = order[i], j = byId(id);
  if (!canPlay(j)) return;
  cur = i; retries = 0;
  subsOn = !!j.subs;
  // 'live' means "what's playing can't be seeked yet, watch for a better copy".
  // True while downloading, and also while a fallback client is watching the
  // H264 rendition as fragments before its seekable form exists.
  live = j.status !== 'done' || onCompatFragments(j);
  v.hidden = false; slate.style.display = 'none';
  setFlag(j);
  v.src = srcOf(j);
  v.load();
  applySubs(j);
  v.play().catch(() => {});
  cue.textContent = j.title;
  cue.classList.remove('none');
  reportPlaying(true);
  paint();
}

v.addEventListener('play', () => { wantPlay = true; });
v.addEventListener('pause', () => { if (!v.ended) wantPlay = false; });

/* Phase 1 -> 2. The live fragments and the finished file share one timeline
   (video is stream-copied), so the timestamp carries straight across.
   Resume on intent rather than on v.paused: the live stream reaching its end
   coincides with the download finishing, so the element is often already
   paused here even though the viewer never asked it to stop. */
function swapToSeekable(j) {
  const at = v.currentTime;
  const resume = wantPlay;
  live = false;
  setFlag(j);
  v.src = srcOf(j);          // may be the compat rendition on this device
  v.load();
  applySubs(j);
  const once = () => {
    v.removeEventListener('loadedmetadata', once);
    if (at > 0.25 && isFinite(at)) { try { v.currentTime = at; } catch (e) {} }
    if (resume) v.play().catch(() => {});
  };
  v.addEventListener('loadedmetadata', once);
}
v.addEventListener('error', () => {
  // the file may still be landing; back off a few times before giving up
  if (cur < 0 || retries >= 4) return;
  retries++;
  const j = byId(order[cur]);
  if (!j) return;
  setTimeout(() => { v.src = srcOf(j) + '?r=' + Date.now(); v.load();
                     v.play().catch(() => {}); }, 900 * retries);
});
v.addEventListener('ended', () => {
  if (live) return;              // reached the end of what's downloaded so far
  if (!$('auto').checked) return;
  for (let i = cur + 1; i < order.length; i++) {
    if (canPlay(byId(order[i]))) return play(i);
  }
});
function stopPlayback() {
  live = false;
  v.pause(); v.removeAttribute('src'); v.load();
  v.hidden = true; slate.style.display = 'grid'; flag.style.display = 'none';
  cur = -1; cue.textContent = order.length ? 'Nothing playing' : 'Queue is empty';
  cue.classList.add('none');
}
const step = d => {
  for (let i = cur + d; i >= 0 && i < order.length; i += d) {
    if (canPlay(byId(order[i]))) { play(i); return true; }
  }
  return false;
};
$('prev').onclick = () => step(-1);
$('next').onclick = () => step(1);

function ready(dir) {
  for (let i = cur + dir; i >= 0 && i < order.length; i += dir) {
    if (canPlay(byId(order[i]))) return true;
  }
  return false;
}

/* rows: built once, updated in place — no innerHTML for server-supplied text */
const rows = new Map();

function makeRow(id) {
  const li = document.createElement('li');
  li.className = 'row';
  li.innerHTML = '<span class="n"></span>' +
    '<span class="body"><span class="title"></span>' +
    '<span class="track"><i></i></span><span class="note"></span></span>' +
    '<span class="flags"><span class="cc"></span><span class="eyes"></span>' +
    '<button class="logbtn" type="button" hidden aria-label="Show this item\'s log">log</button>' +
    '<span class="kind"></span><span class="stat"></span></span>' +
    '<button class="kill" type="button" aria-label="Remove">&times;</button>' +
    '<div class="logpanel" hidden></div>';
  const el = {li, n: li.querySelector('.n'), title: li.querySelector('.title'),
              track: li.querySelector('.track'), fill: li.querySelector('.track i'),
              note: li.querySelector('.note'), kind: li.querySelector('.kind'),
              eyes: li.querySelector('.eyes'), cc: li.querySelector('.cc'),
              stat: li.querySelector('.stat'), kill: li.querySelector('.kill'),
              logbtn: li.querySelector('.logbtn'),
              logpanel: li.querySelector('.logpanel')};
  el.logbtn.addEventListener('click', ev => {
    ev.stopPropagation();                 // the row itself means "play"
    const open = el.logpanel.hidden;
    el.logpanel.hidden = !open;
    el.logbtn.classList.toggle('on', open);
    if (open) loadLog(id, el);
  });
  li.addEventListener('click', ev => {
    if (ev.target === el.kill) return;
    const i = order.indexOf(id), j = byId(id);
    if (!j) return;
    if (canPlay(j)) play(i);
    else if (j.queued) api('/start', {id}).then(refresh);
    else if (j.status === 'evicted' || j.status === 'error') api('/retry', {id}).then(refresh);
  });
  el.kill.addEventListener('click', ev => { ev.stopPropagation(); remove(id); });
  rows.set(id, el);
  return el;
}

/* Timestamps are relative to the first event, because what matters when
   reading one of these is how long a step took, not the wall clock. */
function logStamp(t, t0) {
  const d = Math.max(0, t - t0);
  const m = Math.floor(d / 60), s = Math.floor(d % 60);
  return (m ? m + 'm' : '') + (m ? String(s).padStart(2, '0') : s) + 's';
}

async function loadLog(id, el) {
  let r;
  try { r = await api('/log/' + encodeURIComponent(id)); }   // no body -> GET
  catch (e) { el.logpanel.textContent = 'Could not load the log.'; return; }
  const ev = r.events || [];
  el.logShown = ev.length;
  el.logpanel.textContent = '';
  if (!ev.length) { el.logpanel.textContent = 'Nothing recorded yet.'; return; }
  const t0 = ev[0].t;
  ev.forEach(e => {
    const line = document.createElement('div');
    line.className = 'logline';
    const at = document.createElement('span');
    at.className = 'logat';
    at.textContent = logStamp(e.t, t0);
    at.title = new Date(e.t * 1000).toLocaleTimeString();
    const msg = document.createElement('span');
    msg.textContent = e.m;               // textContent, never HTML
    line.append(at, msg);
    el.logpanel.append(line);
  });
  el.logpanel.scrollTop = el.logpanel.scrollHeight;
}

const LABEL = {queued: 'waiting', converting: 'converting', evicted: 'evicted',
               removed: 'stopped', error: 'failed', 'fetching metadata': 'finding peers',
               starting: 'starting', connecting: 'connecting', streaming: 'ready'};

function paint() {
  const L = $('list');
  $('qcount').textContent = order.length ? String(order.length).padStart(2, '0') : '';
  if (!order.length) {
    rows.clear();
    L.innerHTML = '<li class="blank">Paste a Drive link above to get started.</li>';
    $('prev').disabled = $('next').disabled = true;
    return;
  }
  if (L.firstElementChild && L.firstElementChild.className === 'blank') L.innerHTML = '';

  order.forEach((id, i) => {
    const j = byId(id) || {status: 'queued', received: 0, total: 0, title: '…', kind: 'video'};
    const el = rows.get(id) || makeRow(id);
    if (el.li.parentNode !== L || L.children[i] !== el.li) {
      L.insertBefore(el.li, L.children[i] || null);
    }
    el.li.classList.toggle('live', i === cur);
    el.n.textContent = String(i + 1).padStart(2, '0');
    el.title.textContent = j.title || '…';          // textContent, not innerHTML
    el.kind.textContent = (j.status === 'streaming' || j.live) ? 'live'
                          : j.source === 'torrent' ? 'tor'
                          : j.kind === 'audio' ? 'aud' : 'vid';
    el.kind.classList.toggle('now', j.status === 'streaming' || !!j.live);
    /* Only worth showing when it isn't just this device. The count includes
       us, so 2 means one other screen is on the same thing. */
    const others = (j.viewers || 0) - (i === cur ? 1 : 0);
    el.eyes.textContent = others > 0
        ? (i === cur ? '+' + others + ' watching' : others + ' watching') : '';
    el.eyes.classList.toggle('on', others > 0);
    /* CC means an exact file match, so the timings are the file's own. CC? means
       the best available guess for a different release -- playable, but it can
       drift, and saying so beats letting someone wonder why it slides. */
    el.cc.textContent = j.subs ? (j.subs_exact ? 'CC' : 'CC?')
                      : (j.subs_status === 'searching' ? '…' : '');
    el.cc.classList.toggle('on', !!j.subs || j.subs_status === 'searching');
    el.cc.classList.toggle('found', !!j.subs && !!j.subs_exact);
    el.cc.classList.toggle('rough', !!j.subs && !j.subs_exact);
    el.cc.title = j.subs
        ? (j.subs_exact ? 'subtitles matched to this exact file: ' + (j.subs_name || '')
                        : 'closest match, may drift: ' + (j.subs_name || '')
                          + (j.subs_why ? ' (' + j.subs_why + ')' : ''))
        : j.subs_status === 'searching' ? 'looking for subtitles'
        : j.subs_status === 'unavailable' ? (j.subs_note || 'no subtitles found') : '';
    el.logbtn.hidden = !j.log_n;
    // Refresh an open panel as the job goes on, so a stall can be watched
    // rather than reopened.
    if (!el.logpanel.hidden && el.logShown !== j.log_n) loadLog(id, el);
    el.note.textContent = j.error || (j.paused ? j.note : '');
    el.note.classList.toggle('quiet', !j.error && !!j.paused);
    el.note.style.display = j.error ? 'block' : 'none';
    const again = (j.status === 'evicted' || j.status === 'error') && j.replayable;
    el.li.title = again ? 'Click to fetch this again'
      : j.queued ? (j.prefetch ? 'Queued next — click to start it now'
                               : 'Waiting so the stream keeps up — click to start it now')
      : j.live ? 'Click to play now — still downloading, no seeking yet'
      : j.status === 'done' ? 'Click to play'
      : j.needs_full ? "This file's index is at the end, so it plays once the download finishes"
      : '';

    let label, cls = '';
    if (j.status === 'downloading') { label = j.pct != null ? j.pct.toFixed(0) + '%' : bytes(j.received); }
    else if (j.status === 'converting' && j.conv_pct != null) {
      label = 'conv ' + j.conv_pct.toFixed(0) + '%';
    }
    else if (j.status === 'done') { label = 'ready'; cls = 'ready'; }
    else if (j.status === 'streaming') {
      label = j.complete ? 'seeding' : (j.pct != null ? j.pct.toFixed(0) + '%' : bytes(j.received));
      cls = 'ready';
    }
    else if (j.status === 'error') { label = 'failed'; cls = 'bad'; }
    else if (j.queued) { label = j.prefetch ? 'next up' : 'waiting'; cls = 'idle'; }
    else { label = LABEL[j.status] || j.status;
           cls = (j.status === 'evicted' || j.status === 'removed') ? 'idle' : ''; }
    if (j.paused) { label = 'held'; cls = 'idle'; }
    el.stat.textContent = label;
    el.stat.className = 'stat ' + cls;

    /* A torrent knows its exact size from the .torrent, so it gets a real bar.
       rclone's copyid reports no total up front, so those stay indeterminate
       rather than showing a percentage that would be invented. */
    const moving = j.status === 'downloading' || j.status === 'converting'
                || (j.status === 'streaming' && !j.complete);
    const known = j.status === 'converting' && j.conv_pct != null
                ? true : (j.pct != null && !j.complete);
    el.track.classList.toggle('show', moving || known);
    el.track.classList.toggle('busy', moving && !known);
    el.fill.style.width = !known ? ''
        : (j.status === 'converting' ? j.conv_pct : j.pct) + '%';
  });

  for (const [id, el] of rows) {
    if (!order.includes(id)) { el.li.remove(); rows.delete(id); }
  }
  $('prev').disabled = !ready(-1);
  $('next').disabled = !ready(1);
}

async function remove(id) {
  const wasPlaying = order[cur] === id;
  const at = order.indexOf(id);
  await api('/remove', {id});
  order = order.filter(x => x !== id);
  jobs = jobs.filter(j => j.id !== id);
  if (wasPlaying) {
    stopPlayback();
    cur = Math.min(at, order.length - 1) - 1;
    if (!step(1)) paint();
  } else {
    if (at < cur) cur--;
    paint();
  }
  refresh();
}

/* capacity ---------------------------------------------------------------- */
const rateStr = n => !n ? '' : (n >= 1e6 ? (n/1e6).toFixed(1)+' MB/s'
                                          : Math.round(n/1e3)+' KB/s');
const gb = n => !n ? '0' : (n >= 1e9 ? (n/1e9).toFixed(2)+' GB'
                                     : (n/1e6).toFixed(0)+' MB');
const clock = s => {
  if (s == null) return '';
  s = Math.max(0, Math.round(s));
  const m = Math.floor(s/60);
  return m >= 60 ? Math.floor(m/60)+'h'+String(m%60).padStart(2,'0')
       : m > 0 ? m+'m'+String(s%60).padStart(2,'0') : s+'s';
};

function showWire() {
  const wire = $('wire');
  const j = cur >= 0 ? byId(order[cur]) : null;
  // nothing to say about a file that's already local
  const seeding = j && j.complete && j.status === 'streaming';
  const converting = j && j.status === 'converting';
  const shared = j && (j.viewers || 0) > 1;
  // A finished item normally has nothing to report, but who else is on it is
  // worth saying even then.
  if (!j || (!shared && j.status === 'done')
         || (!seeding && !converting && !shared && !j.health && !j.rate)) {
    wire.hidden = true; return;
  }
  if (shared && j.status === 'done') {
    $('lamp').className = 'lamp ok';
    $('verdict').textContent = 'Also playing on ' + (j.viewers - 1) +
        (j.viewers - 1 === 1 ? ' other device' : ' other devices');
    $('figures').textContent = '';
    wire.hidden = false;
    return;
  }
  wire.hidden = false;
  const h = j.health || 'unknown';
  $('lamp').className = 'lamp ' + h;
  const buf = j.buffered != null ? clock(j.buffered) : null;
  $('verdict').textContent =
      converting ? (h === 'behind' ? 'This machine can\u2019t convert it fast enough'
                                    : 'Converting for playback') :
      seeding ? 'Downloaded \u00b7 seeding' :
      h === 'ok' ? 'Streaming comfortably' :
      h === 'tight' ? 'Keeping up, only just' :
      h === 'behind' ? (j.encode_speed != null && j.encode_speed < 1
            ? 'This machine can\u2019t transcode it fast enough — expect stalling'
            : 'Arriving slower than it plays — expect a stall') :
      'Measuring…';
  const bits = [];
  if (converting) {
    if (j.conv_pct != null) bits.push(j.conv_pct.toFixed(0) + '% converted');
    if (j.conv_speed != null) bits.push(j.conv_speed.toFixed(2) + 'x');
    if (j.duration && j.conv_pct != null && j.conv_speed) {
      const remain = j.duration * (100 - j.conv_pct) / 100 / j.conv_speed;
      bits.push(clock(remain) + ' left');
    }
  } else {
    if (j.pct != null && j.total) bits.push(gb(j.received) + ' / ' + gb(j.total));
    if (j.rate) bits.push(rateStr(j.rate));
    if (j.bitrate) bits.push('needs ' + rateStr(j.bitrate / 8));
    if (j.peers != null) bits.push(j.peers + ' peers');
    if (j.uploaded) bits.push('\u2191 ' + gb(j.uploaded) + ' seeded');
    else if (j.up_rate) bits.push('\u2191 ' + rateStr(j.up_rate));
    if (j.encode_speed != null) bits.push('encoding ' + j.encode_speed.toFixed(2) + 'x');
    if (buf) bits.push(buf + ' buffered');
    if (j.eta) bits.push(clock(j.eta) + ' left');
  }
  if (shared) bits.push((j.viewers - 1) + ' other watching');
  $('figures').textContent = bits.join('  \u00b7  ');
}

function showCache(s) {
  if (!s || s.cap_gb == null) return;
  const cap = s.cap_gb, used = s.used_gb || 0;
  const pct = Math.min(1, used / cap);
  $('read').innerHTML = '';
  $('read').append(document.createTextNode(used.toFixed(2) + ' '));
  const span = document.createElement('span');
  span.textContent = 'of ' + cap + ' GB';
  $('read').append(span);
  const lit = Math.round(pct * TICKS), hot = pct >= 0.85;
  [...$('meter').children].forEach((t, i) => {
    t.classList.toggle('f', i < lit);
    t.classList.toggle('hot', hot);
  });
  const box = $('cap');
  if (document.activeElement !== box) box.value = cap;
}
$('savecap').onclick = async () => {
  const val = parseFloat($('cap').value);
  if (val >= 1) showCache(await api('/setcap', {cap_gb: val}));
};
$('cap').addEventListener('keydown', e => { if (e.key === 'Enter') $('savecap').click(); });

/* polling ----------------------------------------------------------------- */
async function refresh() {
  try {
    jobs = await api('/jobs');
    jobs.forEach(j => { if (!order.includes(j.id)) order.push(j.id); });   // survives restarts
    order = order.filter(id => byId(id));
    if (cur >= 0 && !byId(order[cur])) stopPlayback();
    if (live && cur >= 0) {
      const j = byId(order[cur]);
      // A fallback client waits for the H264 rendition to become seekable;
      // everyone else waits for the download to finish.
      if (j && !playsHere(j)) { if (j.compat_seekable) swapToSeekable(j); }
      else if (j && (j.status === 'done' || j.seekable)) swapToSeekable(j);
    }
    /* Subtitles are found in the background and can land after playback began.
       Attaching only when the count changes avoids rebuilding the track — and
       resetting its mode — on every poll. */
    if (cur >= 0) {
      const j = byId(order[cur]);
      if (j && !!j.subs !== subsOn) { subsOn = !!j.subs; applySubs(j); }
    }
    /* Nothing playing yet: start the first item that can play. canPlay() counts
       a live item, so this fires seconds after a paste rather than waiting for
       the whole download — which is the entire point of the live phase. */
    if (cur === -1) {
      const i = order.findIndex(id => canPlay(byId(id)));
      if (i >= 0) play(i);
    }
    paint();
    showWire();
  } catch (e) {}
}
async function pollSys() {
  try {
    const s = await api('/sys');
    const ok = s.rclone && s.ffmpeg;
    $('led').classList.toggle('on', ok);
    $('statetext').textContent = ok ? (s.webtorrent ? 'ready' : 'ready \u00b7 no webtorrent')
      : !s.rclone ? 'rclone remote missing' : 'ffmpeg missing';
    showCache(s);
    // Only shown once there's an address worth sharing: qrcode installed,
    // and this isn't a loopback-only server with nothing on the LAN to scan.
    $('qrbtn').hidden = !s.lan_url;
    lanUrl = s.lan_url || null;
    if (!lanUrl) { $('qrpop').hidden = true; qrLoaded = false; }
  } catch (e) {
    $('led').classList.remove('on');
    $('statetext').textContent = 'server offline';
  }
}

/* QR pairing --------------------------------------------------------------
   Fetched via fetch(), not <img src>: the page's CSP has no img-src, only
   connect-src 'self', so an <img> pointed at /qr would be silently blocked --
   fetching the SVG text and inserting it avoids that entirely. */
let lanUrl = null, qrLoaded = false;
$('qrbtn').addEventListener('click', async () => {
  const pop = $('qrpop');
  pop.hidden = !pop.hidden;
  if (pop.hidden || qrLoaded || !lanUrl) return;
  try {
    const r = await fetch('/qr');
    if (r.ok) {
      $('qrimg').innerHTML = await r.text();   // server-generated SVG, not user input
      $('qrurl').textContent = lanUrl;
      qrLoaded = true;
    }
  } catch (e) {}
});
refresh(); setInterval(refresh, 1000);
pollSys(); setInterval(pollSys, 2500);
</script></body></html>"""


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True  # so Ctrl+C doesn't hang on an open stream

    def handle_error(self, request, client_address):
        """Media elements abandon connections constantly — seeking, swapping
        from live to seekable, closing a tab. None of that deserves a traceback
        on the terminal."""
        if isinstance(sys.exc_info()[1], GONE):
            return
        super().handle_error(request, client_address)


def main():
    restore()
    for _ in range(WORKERS):
        threading.Thread(target=worker, daemon=True).start()
    threading.Thread(target=janitor, daemon=True).start()
    threading.Thread(target=scheduler, daemon=True).start()
    with Server((HOST, PORT), H) as s:
        print(f"\n  reel  ->  http://localhost:{PORT}")
        lan = lan_ip()
        if lan and HOST != "127.0.0.1":
            print(f"  on this wifi  ->  http://{lan}:{PORT}")
        print(f"  rclone gdrive: {has_rclone()}   ffmpeg+ffprobe: {has_ffmpeg()}")
        print(f"  cache: {DL}  (cap {CACHE_CAP_GB:g} GB, {len(JOBS)} restored)\n")
        try:
            s.serve_forever()
        except KeyboardInterrupt:
            print("\n  stopped\n")


if __name__ == "__main__":
    main()

