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
import json as _json
import uuid
import shutil
import hashlib
import threading
import subprocess
import time

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
VIDEO_EXT = (".mp4", ".mkv", ".avi", ".mov", ".m4v", ".webm", ".ts", ".flv", ".wmv",
             ".mpg", ".mpeg", ".m2ts")
AUDIO_EXT = (".mp3", ".m4a", ".flac", ".wav", ".aac", ".ogg", ".opus")

# Search. One indexer to begin with, behind a normalising layer so another can
# be added without the caller noticing. These endpoints go dark without warning
# -- yts.mx already refuses the requests this was first written against -- so a
# dead source has to read as "no results", never as a broken feature.
SEARCH_URL = "https://apibay.org/q.php"
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
# Appended to every magnet we build, since the indexer hands back a bare
# infohash. DHT finds most peers on its own; these only speed up the start.
# Tracker liveness drifts too: the dead ones in that Spider-Man magnet
# (coppersurfer, leechers-paradise, rarbg) are why it took 150s to find
# metadata the first time.
SEARCH_TRACKERS = (
    "udp://tracker.opentrackr.org:1337/announce",
    "udp://open.stealth.si:80/announce",
    "udp://tracker.torrent.eu.org:451/announce",
    "udp://exodus.desync.com:6969/announce",
)

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
    ext = os.path.splitext(name or "")[1].lower()
    container_ok = (ext in BROWSER_CONTAINERS) if ext else True
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


def search_torrents(query, limit=SEARCH_LIMIT):
    """Find magnets by name. Returns (results, error).

    Ranked by seeders above all else, because a dead swarm is the one failure
    no amount of local cleverness recovers from -- the 2-peer magnet earlier
    found its endpoint correctly and still could not stream a byte.
    """
    q = (query or "").strip()
    if not q:
        return [], "nothing to search for"
    url = SEARCH_URL + "?" + urllib.parse.urlencode({"q": q, "cat": 200})
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "reel/1.0"})
        with urllib.request.urlopen(req, timeout=SEARCH_TIMEOUT) as r:
            rows = _json.loads(r.read().decode("utf-8", "replace"))
    except Exception as e:
        # A dead or blocked indexer is an expected state, not a crash: say so
        # plainly and leave the rest of the app alone.
        return [], "couldn't reach the search index (%s)" % str(e)[:60]
    if not isinstance(rows, list):
        return [], "unexpected response from the search index"

    out = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        ih = (row.get("info_hash") or "").strip()
        # The no-results sentinel: one row, id 0, an all-zero infohash. Left
        # unfiltered it would offer a magnet that can never resolve.
        if row.get("id") in ("0", 0) or not re.fullmatch(r"[0-9a-fA-F]{40}", ih):
            continue
        if set(ih) == {"0"}:
            continue
        name = (row.get("name") or "").strip()
        if not name:
            continue

        def num(key):
            try:
                return int(row.get(key) or 0)
            except (TypeError, ValueError):
                return 0
        size = num("size")
        out.append({"name": name, "infohash": ih.lower(), "id": str(row.get("id") or ""),
                    "magnet": build_magnet(ih, name),
                    "seeders": num("seeders"), "leechers": num("leechers"),
                    "size": size, "files": num("num_files")})

    out.sort(key=lambda r: (-r["seeders"], r["size"]))
    out = out[:limit]

    # Fill in the real filename for the rows most likely to be chosen, in
    # parallel: ten sequential lookups would add ten round-trips to a search.
    def enrich(res):
        real = search_real_name(res["id"]) if res["id"] else None
        if real:
            res["real_name"] = real
    threads = [threading.Thread(target=enrich, args=(r,), daemon=True)
               for r in out[:SEARCH_DETAIL]]
    for t in threads:
        t.start()
    for t in threads:
        t.join(SEARCH_TIMEOUT)

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
        res.update(info)
    return out, None


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


def lan_ip():
    """This machine's address on the local network, for the startup banner.

    Nothing is sent: a connected UDP socket only makes the OS pick the route it
    would use, which is how you learn which interface faces the wifi.
    """
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("192.168.1.1", 9))
            return s.getsockname()[0]
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
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


def new_job(drive_id, jid=None, **extra):
    job = {"id": jid or uuid.uuid4().hex[:12], "drive_id": drive_id,
           "path": None, "total": 0, "received": 0, "status": "queued",
           "error": "", "title": drive_id or "recovered", "kind": "video",
           "cancel": threading.Event(), "proc": None, "procs": [],
           "last_played": None, "overflow": False,
           # live phase: streamable is None until the header has been read
           "hold": True, "prefetch": False, "paused": False, "rate": None,
           "bitrate": None, "duration": None, "headroom": None, "eta": None,
           "peers": None, "uploaded": None, "up_rate": None,
           "source": "drive", "magnet": None, "wt_port": None, "wt_url": None,
           "wt_proc": None, "wt_done": False, "wt_ranges": False,
           "wt_codecs": "", "wt_files": 0, "wt_direct": False,
           "caps": None, "vcodec": None, "vpix": None, "play_key": None,
           "live_proc": None,
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
    job["status"] = "error"
    job["error"] = msg[:300]


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


def validate_stream_url(url):
    """The definitive test: can a decoder actually read streams from it?

    Returns the full probe so callers never have to ask the network twice.
    """
    got = probe_media(url, timeout=20)
    if got[0] is None and got[1] is None:
        return None
    return got


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
                tried[url] = ("html/index" if info.get("html")
                              else "http %s" % (info.get("status") or info.get("error")))
                continue
            # it serves bytes; now make sure a decoder can read them
            probed = validate_stream_url(url)
            if not probed:
                tried[url] = "not decodable"
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
    if job["cancel"].is_set():
        cleanup()
        job["status"] = cancel_status(job)
        return

    chosen = pick_file(files)
    if chosen:
        job["title"] = os.path.splitext(os.path.basename(chosen["name"]))[0]
        job["total"] = chosen["size"] or 0
        job["wt_files"] = len(files)
        job["note"] = (job.get("note", "") +
                       f"; file {chosen['index']} of {len(files)}").strip("; ")
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
    t_probe = time.time()

    # ---- 3. proxy directly, or convert on the fly ---------------------------
    probed = job.get("wt_probe") or probe_media(url, timeout=20)
    v, a, vh, hdr, br, dur, pix = probed
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
                cleanup()
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

    # Stop seeding and reclaim the raw download: the seekable file replaces it
    # entirely, the same trade a Drive item makes when its _raw folder is
    # deleted post-conversion. Unlike Drive's _raw, this one was also serving
    # uploads, so it has to be stopped before it can go.
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

    wp = job.get("wt_proc")
    if wp and wp.poll() is None:
        try:
            wp.kill()
        except Exception:
            pass
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
        sweep_file(frag, LIVE_GRACE)     # let anyone mid-stream finish first
    else:
        job["compat_note"] = tail(r.stderr.decode("utf-8", "replace"), 2, 160)


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
                job.get("compat_path"), os.path.join(DL, jid + ".magnet")]
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
            results, err = search_torrents(body.get("q"))
            return self._json(200, {"results": results, "error": err})

        if p == "/add":
            magnets, ids, bad = split_sources(body.get("links"))
            caps = sorted(caps_of(body.get("client")))
            added = []
            for uri in magnets:
                job = new_job(None, source="torrent", magnet=uri, caps=caps,
                              title="magnet " + infohash(uri)[:8])
                with LOCK:
                    JOBS[job["id"]] = job
                added.append(job["id"])      # scheduler decides when it starts
            for did in ids:
                job = new_job(did, caps=caps)
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
  head.textContent = rows.length + ' results for "' + q + '" · most seeded first';
  box.append(head);

  rows.forEach(res => {
    const row = document.createElement('button');
    row.className = 'rrow';
    row.type = 'button';
    if (!res.fits) row.classList.add('toobig');

    const title = document.createElement('span');
    title.className = 'rtitle';
    // The index truncates its own name field mid-word, so prefer the real
    // filename when the lookup found one -- it's complete, and it carries the
    // codec and release group the truncated version loses.
    title.textContent = res.real_name || res.name;   // textContent, never HTML

    const meta = document.createElement('span');
    meta.className = 'rmeta';
    const bits = [res.seeders + ' seed', fmtSize(res.size)];
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
  // 'live' means "what's playing can't be seeked yet, watch for a better copy".
  // True while downloading, and also while a fallback client is watching the
  // H264 rendition as fragments before its seekable form exists.
  live = j.status !== 'done' || onCompatFragments(j);
  v.hidden = false; slate.style.display = 'none';
  setFlag(j);
  v.src = srcOf(j);
  v.load();
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
    '<span class="flags"><span class="eyes"></span><span class="kind"></span>' +
    '<span class="stat"></span></span>' +
    '<button class="kill" type="button" aria-label="Remove">&times;</button>';
  const el = {li, n: li.querySelector('.n'), title: li.querySelector('.title'),
              track: li.querySelector('.track'), fill: li.querySelector('.track i'),
              note: li.querySelector('.note'), kind: li.querySelector('.kind'),
              eyes: li.querySelector('.eyes'),
              stat: li.querySelector('.stat'), kill: li.querySelector('.kill')};
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

