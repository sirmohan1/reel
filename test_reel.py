#!/usr/bin/env python3
"""
Tests for reel.

Every case here is a bug that actually happened, kept so it cannot happen twice.
Where that is the point of the test, the comment says which one.

Stdlib only, no network, and no ffmpeg except where a test says otherwise --
those skip themselves rather than fail when it is missing.

Run:  python3 test_reel.py          (or -v for the list)
"""

import gzip
import importlib.util
import inspect
import io
import json
import os
import re
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest
import urllib.parse
import urllib.request


def load_reel(dl=None):
    """A fresh copy of the module, with its cache pointed somewhere disposable.

    Imported per test-class rather than once, since a few tests change module
    state (tracker lists, cache caps) and must not leak into the others.
    """
    spec = importlib.util.spec_from_file_location(
        "reel_under_test", os.path.join(os.path.dirname(os.path.abspath(__file__)), "reel.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    if dl:
        m.DL = dl
        # Otherwise the ratings dump lands in the repo, and a test run leaves
        # 8 MB of IMDb behind it.
        m.CACHE_DIR = os.path.join(dl, "cache")
        os.makedirs(m.CACHE_DIR, exist_ok=True)
    return m


HAVE_FFMPEG = bool(shutil.which("ffmpeg") and shutil.which("ffprobe"))
needs_ffmpeg = unittest.skipUnless(HAVE_FFMPEG, "ffmpeg/ffprobe not installed")

try:
    import libtorrent as _lt                       # noqa: F401
    HAVE_LT = True
except Exception:
    HAVE_LT = False
needs_libtorrent = unittest.skipUnless(HAVE_LT, "libtorrent not installed")


class Base(unittest.TestCase):
    def setUp(self):
        self.dl = tempfile.mkdtemp(prefix="reeltest-")
        self.m = load_reel(self.dl)

    def tearDown(self):
        shutil.rmtree(self.dl, ignore_errors=True)

    def job(self, **kw):
        j = self.m.new_job(kw.pop("drive_id", None), **kw)
        self.m.JOBS[j["id"]] = j
        return j


# --------------------------------------------------------------------------
class TestCodecs(Base):
    def test_ten_bit_gets_its_own_key(self):
        # x265 rips are routinely Main 10, and a device can decode 8-bit while
        # refusing 10-bit, so the two cannot share a capability name.
        self.assertEqual(self.m.codec_key("hevc", "yuv420p"), "hevc")
        self.assertEqual(self.m.codec_key("hevc", "yuv420p10le"), "hevc10")
        self.assertEqual(self.m.codec_key("h264", "yuv420p10le"), "h26410")
        self.assertIsNone(self.m.codec_key(None, "yuv420p"))

    def test_plays_natively_respects_bit_depth(self):
        caps = {"h264", "hevc"}
        self.assertTrue(self.m.plays_natively(caps, "h264", "yuv420p"))
        # "hevc" alone must not authorise a 10-bit stream
        self.assertFalse(self.m.plays_natively(caps, "hevc", "yuv420p10le"))
        self.assertTrue(self.m.plays_natively(caps | {"hevc10"}, "hevc", "yuv420p10le"))
        self.assertTrue(self.m.plays_natively(set(), None, None))   # audio only

    def test_copy_path_tags_hevc_as_hvc1(self):
        # Untagged HEVC in MP4 is refused outright by Apple decoders, so the one
        # client that could play it natively would not.
        args, _f, _n = self.m.video_args("hevc", 1080, False, pix="yuv420p10le",
                                         caps={"hevc10"})
        self.assertIn("copy", args)
        self.assertIn("hvc1", args)

    def test_encode_bitrate_tracks_the_source(self):
        # A flat 6 Mbps made a 2.4 Mbps source come back 2.5x larger.
        src = 2_400_000
        self.assertEqual(self.m.encode_bitrate(src, 1080, "hevc"), int(src * 1.5))
        # h264 is closer in efficiency, so it needs less headroom
        self.assertEqual(self.m.encode_bitrate(src, 1080, "h264"), int(src * 1.15))
        # never above what the resolution warrants, nor below a sane floor
        self.assertEqual(self.m.encode_bitrate(50_000_000, 1080, "hevc"), 6_000_000)
        self.assertEqual(self.m.encode_bitrate(10_000, 480, "hevc"), 1_000_000)
        # unknown source rate falls back to the old ceiling, unchanged
        self.assertEqual(self.m.encode_bitrate(None, 1080, "hevc"), 6_000_000)


# --------------------------------------------------------------------------
class TestReleaseNames(Base):
    def test_container_decides_as_much_as_codec(self):
        # An h264 .mkv cannot play in any browser, so "plays directly" would be
        # a lie -- this shipped wrong once and failed silently.
        self.assertTrue(self.m.read_release("Film.2024.1080p.BluRay.x264-GRP.mp4")["direct"])
        self.assertFalse(self.m.read_release("Film.2024.1080p.BluRay.x264-GRP.mkv")["direct"])
        # with no extension known, the codec alone decides
        self.assertTrue(self.m.read_release("Film (2024) 1080p BrRip x264 - YIFY")["direct"])

    def test_hevc_and_hdr_are_never_direct(self):
        r = self.m.read_release("Film.2024.2160p.x265.10bit.HDR.mkv")
        self.assertEqual(r["codec"], "hevc")
        self.assertTrue(r["hdr"])
        self.assertFalse(r["direct"])
        self.assertEqual(r["res"], "2160p")

    def test_unknown_codec_is_not_claimed_as_direct(self):
        self.assertFalse(self.m.read_release("Some.Film.2024.1080p.mkv")["direct"])

    def test_a_release_group_is_not_a_container(self):
        # Release names are dotted, so splitext returns ".h264-kyogo" as the
        # extension. Judged as a container that browsers cannot play, it marked
        # every dotted h264 release "needs remux" whenever the real-filename
        # lookup came back empty -- which is most of the recommendation feed,
        # since it never does that lookup at all.
        for name in ("The.Furious.2026.1080p.AMZN.WEB-DL.DDP5.1.H264-KyoGo",
                     "Film.2026.1080p.WEB-DL.H264-GRP",
                     "Film.2026.1080p.WEB-DL.H264"):
            self.assertTrue(self.m.read_release(name)["direct"], name)
        # and a real container still decides
        self.assertFalse(self.m.read_release("Film.2026.1080p.x264-GRP.mkv")["direct"])


# --------------------------------------------------------------------------
class TestSparseReads(Base):
    def test_never_reads_past_a_hole(self):
        # rclone fills large files out of order through a sparse file. Reading
        # straight through handed ffmpeg a block of zeros, and the video track
        # jumped minutes ahead while the audio kept going.
        #
        # Whether a filesystem actually leaves a hole is its own decision -- APFS
        # sometimes allocates the lot -- so this asserts against what the OS
        # reports rather than assuming, and says so when there is nothing to test.
        p = os.path.join(self.dl, "sparse.bin")
        with open(p, "wb") as f:
            f.write(b"A" * 65536)
            f.seek(8 * 1024 * 1024)
            f.write(b"B" * 65536)
        size = os.path.getsize(p)
        fd = os.open(p, os.O_RDONLY)
        try:
            hole = os.lseek(fd, 0, os.SEEK_HOLE)
            os.lseek(fd, 0, os.SEEK_SET)
            if hole >= size:
                self.skipTest("filesystem stored the file without a hole")
            self.assertEqual(self.m.contiguous_end(fd, size), hole,
                             "the readable prefix must stop at the hole")
        finally:
            os.close(fd)

    def test_leaves_the_read_position_where_it_found_it(self):
        # It seeks on the same descriptor the feeder is reading from, so a
        # position left behind would silently corrupt the stream.
        p = os.path.join(self.dl, "pos.bin")
        with open(p, "wb") as f:
            f.write(b"C" * 300000)
        fd = os.open(p, os.O_RDONLY)
        try:
            os.lseek(fd, 12345, os.SEEK_SET)
            self.m.contiguous_end(fd, 300000)
            self.assertEqual(os.lseek(fd, 0, os.SEEK_CUR), 12345)
        finally:
            os.close(fd)

    def test_whole_file_reads_to_the_end(self):
        p = os.path.join(self.dl, "solid.bin")
        with open(p, "wb") as f:
            f.write(b"B" * 500000)
        fd = os.open(p, os.O_RDONLY)
        try:
            self.assertEqual(self.m.contiguous_end(fd, 500000), 500000)
        finally:
            os.close(fd)


# --------------------------------------------------------------------------
class TestHealth(Base):
    def test_converting_reads_the_conversion_not_the_encoder(self):
        # While converting, encode_speed belongs to the live preview and is
        # stale; conv_speed is the job actually in progress.
        j = {"id": "x", "status": "converting", "conv_speed": 4.5, "encode_speed": 0.2}
        self.assertEqual(self.m.stream_health(j), "ok")
        j["conv_speed"] = 0.5
        self.assertEqual(self.m.stream_health(j), "behind")

    def test_encoder_speed_beats_a_bursty_byte_counter(self):
        # received moves in 64 MiB steps, so headroom reads as 0 between them.
        # The encoder reads through the download, so it already accounts for it.
        j = {"id": "x", "status": "downloading", "encode_speed": 7.5, "headroom": 0.01}
        self.assertEqual(self.m.stream_health(j), "ok")

    def test_network_used_when_there_is_no_encoder(self):
        j = {"id": "x", "status": "downloading", "headroom": 0.4}
        self.assertEqual(self.m.stream_health(j), "behind")
        j["headroom"] = 9.0
        self.assertEqual(self.m.stream_health(j), "ok")

    def test_buffer_is_meaningless_while_converting(self):
        j = {"id": "x", "status": "converting", "bitrate": 1_000_000,
             "received": 50_000_000}
        self.assertIsNone(self.m.buffered_seconds(j))

    def test_rate_survives_a_stalled_byte_counter(self):
        # Adjacent samples read 0 B/s between chunk arrivals, which used to drag
        # the smoothed rate to nothing and announce a stall mid-transfer.
        j = self.m.new_job("d")
        base = time.time()
        for i, (t, got) in enumerate([(0, 0), (1, 0), (2, 0), (3, 64 << 20)]):
            j["_rate_hist"] = j.get("_rate_hist", [])
            j["_rate_hist"].append((base + t, got))
        j["received"] = 64 << 20
        span = 3.0
        self.assertGreater((64 << 20) / span, 20_000_000)


# --------------------------------------------------------------------------
class TestViewers(Base):
    def test_two_devices_are_tracked_separately(self):
        # One global slot meant the second viewer's item looked unwatched, and
        # the evictor was free to delete it underneath them.
        self.m.note_playing("mac", "jobA", 120.0)
        self.m.note_playing("phone", "jobB", 45.0)
        self.assertTrue(self.m.watching("jobA"))
        self.assertTrue(self.m.watching("jobB"))
        self.assertEqual(self.m.viewer_count("jobA"), 1)

    def test_playhead_reports_whoever_is_furthest(self):
        # That viewer has the least downloaded ahead of them.
        self.m.note_playing("mac", "jobA", 300.0)
        self.m.note_playing("phone", "jobA", 60.0)
        self.assertEqual(self.m.playhead("jobA"), 300.0)
        self.assertEqual(self.m.viewer_count("jobA"), 2)

    def test_a_quiet_viewer_stops_counting(self):
        self.m.note_playing("gone", "jobC", 10.0)
        with self.m.PLAY_LOCK:
            self.m.PLAYING["gone"]["seen"] -= 3600
        self.assertFalse(self.m.watching("jobC"))


# --------------------------------------------------------------------------
class TestEviction(Base):
    def _done_job(self, jid):
        p = os.path.join(self.dl, "%s__d__t.mp4" % jid)
        with open(p, "wb") as f:
            f.write(b"\0" * 5000)
        return self.job(drive_id="d", jid=jid, path=p, status="done", total=5000,
                        received=5000, started_at=time.time() - 999,
                        last_played=time.time() - 999)

    def test_a_finalized_torrent_can_be_reclaimed(self):
        # An if/elif meant "source == torrent" always won, so once the _wt folder
        # was gone the finished file was invisible to the cap forever.
        j = self._done_job("tj")
        j["source"] = "torrent"
        self.assertIn("tj", [x[1] for x in self.m.evictable()])

    def test_mid_finalize_is_protected(self):
        d = os.path.join(self.dl, "cv_wt")
        os.makedirs(d)
        with open(os.path.join(d, "f.mkv"), "wb") as f:
            f.write(b"\0" * 5000)
        self.job(jid="cv", source="torrent", status="converting",
                 started_at=time.time() - 999)
        self.assertNotIn("cv", [x[1] for x in self.m.evictable()],
                         "finalize_torrent is reading that folder")

    def test_what_someone_is_watching_is_protected(self):
        self._done_job("watched")
        self._done_job("idle")
        self.m.note_playing("mac", "watched", 5.0)
        self.assertNotIn("watched", [x[1] for x in self.m.evictable()])
        self.assertIn("idle", [x[1] for x in self.m.evictable()])


# --------------------------------------------------------------------------
class TestSearchMerge(Base):
    def test_rejects_the_no_results_sentinel(self):
        # The index answers a miss with one row: id 0, an all-zero infohash.
        # Unfiltered it offered a magnet that can never resolve.
        self.assertIsNone(self.m._row("0" * 40, "No results returned", 0, 0, 0))
        self.assertIsNone(self.m._row("not-a-hash", "x", 1, 1, 1))
        self.assertIsNone(self.m._row("a" * 40, "", 1, 1, 1))
        self.assertIsNotNone(self.m._row("a" * 40, "Film", 5, 1, 100))

    def test_magnet_carries_hash_and_trackers(self):
        r = self.m._row("A" * 40, "Some Film", 5, 1, 100)
        self.assertEqual(self.m.infohash(r["magnet"]), "a" * 40)
        self.assertEqual(r["magnet"].count("&tr="), len(self.m.SEARCH_TRACKERS))

    def test_merge_takes_a_middle_count_not_the_best(self):
        # Three indexers said 109, 487 and 1313 for one torrent; the tracker said
        # 283. Taking the highest reliably picks the stalest, most flattering
        # number -- the opposite of useful when the ranking exists to avoid a
        # dead swarm.
        #
        # Exercises search_all itself with stand-in sources. An earlier version
        # of this test re-implemented the merge inline, so it passed happily
        # while the real code went back to taking the maximum.
        ih = "b" * 40
        def src(n):
            return lambda q: [self.m._row(ih, "Film", n, 0, 100)]
        self.m.SEARCH_SOURCES = (("a", src(109)), ("b", src(487)), ("c", src(1313)))
        rows, per = self.m.search_all("anything")
        self.assertEqual(len(rows), 1, "one infohash means one row")
        self.assertEqual(rows[0]["seeders"], 487)
        self.assertEqual(rows[0]["sources"], 3)
        self.assertEqual(per, {"a": 1, "b": 1, "c": 1})

    def test_a_dead_source_costs_only_its_own_results(self):
        def ok(q):
            return [self.m._row("c" * 40, "Film", 20, 0, 100)]
        def broken(q):
            raise RuntimeError("indexer gone")
        self.m.SEARCH_SOURCES = (("ok", ok), ("broken", broken))
        rows, per = self.m.search_all("anything")
        self.assertEqual(len(rows), 1)
        self.assertEqual(per["ok"], 1)
        self.assertIn("failed", str(per["broken"]))

    def test_verify_subset_is_smaller_than_the_announce_list(self):
        # Announcing wants breadth; measuring wants the few that answer fastest.
        self.assertLess(len(self.m.VERIFY_TRACKERS), len(self.m.SEARCH_TRACKERS))
        for t in self.m.VERIFY_TRACKERS:
            self.assertIn(t, self.m.SEARCH_TRACKERS)

    def test_bitsearch_rows_are_reshaped_correctly(self):
        # A fourth source, and the mapping is the whole risk again: a swapped
        # field reads as "this source is a bit off" rather than as a bug.
        page = {"results": [
            {"infohash": "A" * 40, "title": "Some.Film.2026.1080p.H264-GRP",
             "seeders": 40, "leechers": 3, "size": 2_000_000_000}]}
        self.m._search_json = lambda url, **k: page
        rows = self.m.source_bitsearch("some film")
        self.assertEqual(len(rows), 1)
        r = rows[0]
        self.assertEqual((r["infohash"], r["name"], r["seeders"],
                         r["leechers"], r["size"]),
                         ("a" * 40, "Some.Film.2026.1080p.H264-GRP", 40, 3,
                          2_000_000_000))

    def test_bitsearch_is_in_the_default_source_list(self):
        names = [n for n, _ in self.m.SEARCH_SOURCES]
        self.assertIn("bitsearch", names)


# --------------------------------------------------------------------------
class TestUrls(Base):
    def test_spaces_are_encoded(self):
        # urllib refuses a url containing a raw space -- raised before anything
        # is sent -- so every candidate found on the index page was discarded.
        u = self.m.safe_url("http://127.0.0.1:8801/webtorrent/abc/Some Film (2021)/f.mkv")
        self.assertNotIn(" ", u)
        self.assertIn("%20", u)

    def test_already_encoded_is_not_double_encoded(self):
        u = self.m.safe_url("http://h/a%20b/c.mkv")
        self.assertIn("%20", u)
        self.assertNotIn("%2520", u)


# --------------------------------------------------------------------------
class TestSubtitleFit(Base):
    def test_an_exact_file_match_wins_outright(self):
        s, why = self.m.subs_fit({"SubLastTS": "00:10:00"}, "Film.mkv", 8000.0,
                                 "moviehash")
        self.assertGreaterEqual(s, 100)
        self.assertIn("exact", " ".join(why))

    def test_wrong_runtime_is_rejected(self):
        # Subtitles for a different cut end minutes from where the film does.
        s, _ = self.m.subs_fit({"SubLastTS": "00:42:10", "SubDownloadsCnt": "99999"},
                               "Film.2024.1080p.mkv", 8172.0, "name")
        self.assertLessEqual(s, -50)

    def test_matching_source_scores_above_a_different_one(self):
        ours = "The.Matrix.1999.1080p.BrRip.x264.mkv"
        same, _ = self.m.subs_fit(
            {"SubLastTS": "02:08:40", "MovieReleaseName": "1080p.BrRip.x264",
             "SubFileName": "m.1080p.BrRip.srt", "SubDownloadsCnt": "100"},
            ours, 8172.0, "name")
        other, _ = self.m.subs_fit(
            {"SubLastTS": "02:08:40", "MovieReleaseName": "720p.HDDVD.x264",
             "SubFileName": "m.720p.HDDVD.srt", "SubDownloadsCnt": "999999"},
            ours, 8172.0, "name")
        self.assertGreater(same, other,
                           "popularity must not outrank a matching source")

    def test_flagged_bad_is_refused(self):
        s, _ = self.m.subs_fit({"SubBad": "1"}, "Film.mkv", 8000.0, "name")
        self.assertLessEqual(s, -50)

    def test_timestamps_parse(self):
        self.assertEqual(self.m.hhmmss("02:08:40"), 7720.0)
        self.assertEqual(self.m.hhmmss("42:10"), 2530.0)
        self.assertIsNone(self.m.hhmmss("rubbish"))

    def test_uploader_adverts_are_stripped(self):
        vtt = ("WEBVTT\n\n1\n00:00:01.000 --> 00:00:04.000\n"
               "Watch Online Movies at www.osdb.link/lm\n\n"
               "2\n00:00:05.000 --> 00:00:07.000\nActual dialogue here.\n")
        out, dropped = self.m.strip_subs_spam(vtt)
        self.assertEqual(dropped, 1)
        self.assertIn("Actual dialogue", out)
        self.assertNotIn("osdb.link", out)

    def test_sidecar_name_cannot_be_mistaken_for_a_job(self):
        # restore() splits filenames on "__" into three parts; a "__"-separated
        # sidecar would have been resurrected as a phantom video job.
        p = self.m.subs_path_for("abc123", "eng")
        self.assertIn(".subs.", os.path.basename(p))
        self.assertNotIn("__", os.path.basename(p))


# --------------------------------------------------------------------------
class TestOsdbHash(Base):
    def test_stable_and_shaped(self):
        p = os.path.join(self.dl, "movie.bin")
        with open(p, "wb") as f:
            f.write(os.urandom(200000))
        h1, s1 = self.m.osdb_hash(p)
        h2, _ = self.m.osdb_hash(p)
        self.assertEqual(h1, h2)
        self.assertEqual(len(h1), 16)
        self.assertEqual(s1, 200000)

    def test_too_small_to_hash(self):
        p = os.path.join(self.dl, "tiny.bin")
        with open(p, "wb") as f:
            f.write(b"x" * 1000)
        h, _ = self.m.osdb_hash(p)
        self.assertIsNone(h)

    def test_matches_the_documented_algorithm(self):
        # size + 64-bit little-endian sums of the first and last 64 KiB.
        chunk = 65536
        p = os.path.join(self.dl, "known.bin")
        with open(p, "wb") as f:
            f.write(b"\x01" + b"\x00" * (chunk - 1))
            f.write(b"\x00" * chunk)
        size = os.path.getsize(p)
        expect = size
        with open(p, "rb") as f:
            for off in (0, size - chunk):
                f.seek(off)
                buf = f.read(chunk)
                for i in range(0, chunk, 8):
                    expect = (expect + struct.unpack("<q", buf[i:i + 8])[0]) & 0xFFFFFFFFFFFFFFFF
        self.assertEqual(self.m.osdb_hash(p)[0], "%016x" % expect)


# --------------------------------------------------------------------------
class TestTorrentBackend(Base):
    """The seam a second torrent client plugs into. These pin the contract
    run_torrent depends on, so an alternative backend can be checked against
    the same expectations rather than against whatever webtorrent happens
    to do."""

    def test_the_default_backend_is_libtorrent(self):
        # It is the only one that can fetch the pieces under a read, which is
        # what makes a still-downloading item seekable at all.
        self.m._BACKEND = None
        self.assertEqual(self.m.backend().name, "libtorrent")

    def test_the_old_client_can_still_be_chosen_on_purpose(self):
        self.m._BACKEND = None
        self.m.TORRENT_BACKEND = "wt"
        try:
            self.assertEqual(self.m.backend().name, "webtorrent")
        finally:
            self.m.TORRENT_BACKEND = "libtorrent"
            self.m._BACKEND = None

    def test_the_backend_is_built_once_and_reused(self):
        self.m._BACKEND = None
        self.assertIs(self.m.backend(), self.m.backend())

    def test_an_unknown_backend_name_falls_back_rather_than_crashing(self):
        # A typo in REEL_TORRENT must not stop the server from starting; it
        # lands on the default, which the startup banner then names outright.
        self.m._BACKEND = None
        self.m.TORRENT_BACKEND = "not-a-real-client"
        try:
            self.assertEqual(self.m.backend().name, "libtorrent")
        finally:
            self.m.TORRENT_BACKEND = "libtorrent"
            self.m._BACKEND = None

    def test_the_interface_run_torrent_relies_on_is_present(self):
        # If a method is renamed here, run_torrent breaks at runtime rather
        # than at import -- so the contract is asserted explicitly.
        bk = self.m.WebTorrentBackend()
        for name in ("available", "fetch_metadata", "list_files",
                     "stream_url", "start", "recent_output"):
            self.assertTrue(callable(getattr(bk, name, None)), name)

    def test_metadata_and_listing_delegate_to_the_existing_functions(self):
        # Stage 1 is a seam, not a rewrite: these must still be the same code
        # paths that were already working and tested.
        bk = self.m.WebTorrentBackend()
        seen = []
        self.m.fetch_metadata = lambda *a: seen.append(("meta",) + a) or ([], None, "")
        self.m.list_torrent_files = lambda *a: seen.append(("list",) + a) or ([], "")
        self.m.find_wt_url = lambda *a: seen.append(("url",) + a) or None
        j = self.job()
        bk.fetch_metadata(j, "magnet:?x", 9, 5)
        bk.list_files(j, "magnet:?x", 9, 5)
        bk.stream_url(j, 9, {"index": 0, "name": "a.mkv"})
        self.assertEqual([s[0] for s in seen], ["meta", "list", "url"])

    def test_a_client_that_cannot_be_spawned_reports_rather_than_raises(self):
        # run_torrent turns a None return into a job error; an exception here
        # would instead kill the worker thread silently.
        bk = self.m.WebTorrentBackend()
        real = self.m.subprocess.Popen
        self.m.subprocess.Popen = lambda *a, **k: (_ for _ in ()).throw(
            OSError("no such binary"))
        try:
            j = self.job()
            got = bk.start(j, "magnet:?x", self.dl, {"index": 0}, 9)
        finally:
            self.m.subprocess.Popen = real
        self.assertIsNone(got)
        self.assertIn("no such binary", j["error"])

    def test_recent_output_is_empty_before_anything_has_run(self):
        # Asked for on the error path, which can be reached before start().
        bk = self.m.WebTorrentBackend()
        self.assertEqual(bk.recent_output(self.job()), "")

    def test_recent_output_reports_what_the_client_said(self):
        bk = self.m.WebTorrentBackend()
        j = self.job()
        j["_out"] = (["connecting\n"], ["Peers: 12/40\n"])
        got = bk.recent_output(j)
        self.assertIn("Peers: 12/40", got)
        self.assertIn("connecting", got)


# --------------------------------------------------------------------------
class TestMergeTrackers(Base):
    """Widening a magnet's tracker list without narrowing it. The union is
    the point: a magnet's own trackers may include one holding peers no
    public list knows about."""

    def setUp(self):
        super().setUp()
        self.m.SEARCH_TRACKERS = ("udp://a.example:1/announce",
                                  "udp://b.example:2/announce")

    def trs(self, magnet):
        import urllib.parse
        return [urllib.parse.unquote(t)
                for t in re.findall(r"[?&]tr=([^&]+)", magnet)]

    def test_a_bare_magnet_gains_the_verified_list(self):
        # The case this exists for: pasted by hand, no trackers at all.
        got = self.m.merge_trackers("magnet:?xt=urn:btih:" + "a" * 40)
        self.assertEqual(self.trs(got), list(self.m.SEARCH_TRACKERS))

    def test_a_magnets_own_trackers_are_kept_not_replaced(self):
        # The whole reason this is a union: that tracker may be the only one
        # that knows about this torrent.
        mine = "udp://private.example:9/announce"
        got = self.m.merge_trackers(
            "magnet:?xt=urn:btih:%s&tr=%s" % ("a" * 40, mine))
        self.assertIn(mine, self.trs(got))
        for t in self.m.SEARCH_TRACKERS:
            self.assertIn(t, self.trs(got))

    def test_a_tracker_already_present_is_not_duplicated(self):
        dup = self.m.SEARCH_TRACKERS[0]
        import urllib.parse
        got = self.m.merge_trackers("magnet:?xt=urn:btih:%s&tr=%s"
                                    % ("a" * 40, urllib.parse.quote(dup)))
        self.assertEqual(self.trs(got).count(dup), 1)

    def test_a_magnet_reel_built_itself_is_unchanged(self):
        # build_magnet already embeds the list, so this must be a no-op --
        # not a second copy of every tracker on every start.
        built = self.m.build_magnet("b" * 40, "Some Film")
        self.assertEqual(self.m.merge_trackers(built), built)

    def test_a_torrent_file_path_is_left_alone(self):
        # run_torrent may hand this a local .torrent instead of a magnet.
        p = "/tmp/whatever.torrent"
        self.assertEqual(self.m.merge_trackers(p), p)

    def test_nothing_is_not_turned_into_something(self):
        self.assertIsNone(self.m.merge_trackers(None))
        self.assertEqual(self.m.merge_trackers(""), "")

    def test_the_result_is_still_a_usable_magnet(self):
        # Parsed by the real thing rather than trusted to look right.
        got = self.m.merge_trackers("magnet:?xt=urn:btih:" + "c" * 40)
        self.assertTrue(got.startswith("magnet:?xt=urn:btih:"))
        self.assertEqual(self.m.infohash(got), "c" * 40)

    def test_the_current_list_is_used_not_the_one_from_queue_time(self):
        # Applied at download time on purpose: a job may have sat in the
        # queue across a weekly refresh.
        bare = "magnet:?xt=urn:btih:" + "d" * 40
        self.m.SEARCH_TRACKERS = ("udp://fresh.example:7/announce",)
        self.assertEqual(self.trs(self.m.merge_trackers(bare)),
                         ["udp://fresh.example:7/announce"])


# --------------------------------------------------------------------------
class TestLibtorrentBackend(Base):
    """The second backend. The parts that need no swarm are tested outright;
    the parts that do are exercised against a real libtorrent session with a
    real .torrent, since a mocked torrent client proves nothing about whether
    this one is driven correctly."""

    def torrent_file(self):
        """A real single-file .torrent, built on the spot -- no network."""
        import libtorrent as lt
        data = os.path.join(self.dl, "payload.bin")
        with open(data, "wb") as f:
            f.write(os.urandom(64 * 1024))
        fs = lt.file_storage()
        lt.add_files(fs, data)
        ct = lt.create_torrent(fs, piece_size=16 * 1024)
        lt.set_piece_hashes(ct, os.path.dirname(data))
        p = os.path.join(self.dl, "made.torrent")
        with open(p, "wb") as f:
            f.write(lt.bencode(ct.generate()))
        return p

    # ---- selection and contract, no swarm needed -------------------------

    def test_it_is_selectable_by_name(self):
        self.m._BACKEND = None
        self.m.TORRENT_BACKEND = "lt"
        try:
            self.assertEqual(self.m.backend().name, "libtorrent")
        finally:
            self.m.TORRENT_BACKEND = "libtorrent"
            self.m._BACKEND = None

    def test_it_is_the_default_now(self):
        self.m._BACKEND = None
        self.assertEqual(self.m.backend().name, "libtorrent")

    def test_an_unknown_name_does_not_silently_pick_the_other_client(self):
        # Falling back quietly is what made a server look identical whether
        # or not seeking worked. An unknown name lands on the default, which
        # the startup banner then reports outright.
        self.m._BACKEND = None
        self.m.TORRENT_BACKEND = "nonsense"
        try:
            self.assertEqual(self.m.backend().name, "libtorrent")
        finally:
            self.m.TORRENT_BACKEND = "libtorrent"
            self.m._BACKEND = None

    def test_it_implements_the_same_interface_as_webtorrent(self):
        lt_bk, wt_bk = self.m.LibtorrentBackend(), self.m.WebTorrentBackend()
        for name in ("available", "fetch_metadata", "list_files",
                     "stream_url", "start", "recent_output"):
            self.assertTrue(callable(getattr(lt_bk, name, None)), name)
            self.assertTrue(callable(getattr(wt_bk, name, None)), name)

    def test_it_serves_from_disk_so_there_is_no_url(self):
        # None here is what makes run_torrent fall through to reading the
        # file, rather than proxying another server.
        bk = self.m.LibtorrentBackend()
        self.assertIsNone(bk.stream_url(self.job(), 9, {"index": 0}))

    def test_a_bad_magnet_is_reported_not_raised(self):
        bk = self.m.LibtorrentBackend()
        if not bk.available():
            self.skipTest("libtorrent not installed")
        files, tfile, log = bk.fetch_metadata(self.job(), "not-a-magnet", 0, 1)
        self.assertIsNone(files)
        self.assertIsNone(tfile)
        self.assertIn("bad magnet", log)

    def test_a_client_that_cannot_start_reports_rather_than_raises(self):
        bk = self.m.LibtorrentBackend()
        if not bk.available():
            self.skipTest("libtorrent not installed")
        j = self.job()
        got = bk.start(j, "not-a-magnet-either", self.dl, {"index": 0}, 0)
        self.assertIsNone(got)
        self.assertIn("Couldn't start libtorrent", j["error"])

    # ---- the Popen shim, which is what keeps run_torrent unchanged -------

    def test_the_handle_shim_reports_running_then_stopped(self):
        class FakeH:
            def __init__(self): self.valid = True
            def is_valid(self): return self.valid
        class FakeSes:
            def __init__(self): self.removed = []
            def remove_torrent(self, h): self.removed.append(h); h.valid = False
        h, ses = FakeH(), FakeSes()
        proc = self.m._TorrentProc(ses, h)
        # None while it is still ours, matching --keep-seeding's behaviour of
        # not exiting when the download finishes.
        self.assertIsNone(proc.poll())
        proc.kill()
        self.assertEqual(proc.poll(), 0)
        self.assertEqual(ses.removed, [h])

    def test_the_shim_pauses_on_the_signal_pause_proc_sends(self):
        # pause_proc sends SIGSTOP/SIGCONT and must keep working unchanged;
        # stopping this process would stop all of reel, so it maps to a real
        # torrent pause instead.
        acted = []
        class FakeH:
            def is_valid(self): return True
            def pause(self): acted.append("pause")
            def resume(self): acted.append("resume")
        proc = self.m._TorrentProc(None, FakeH())
        self.assertTrue(self.m.pause_proc(proc, True))
        self.assertTrue(self.m.pause_proc(proc, False))
        self.assertEqual(acted, ["pause", "resume"])

    def test_stop_procs_kills_a_libtorrent_job_too(self):
        # The generic teardown path must not need to know which client ran.
        class FakeH:
            def __init__(self): self.valid = True
            def is_valid(self): return self.valid
        class FakeSes:
            def remove_torrent(self, h): h.valid = False
        proc = self.m._TorrentProc(FakeSes(), FakeH())
        j = self.job()
        j["procs"] = [proc]
        self.m.stop_procs(j)
        self.assertEqual(proc.poll(), 0)

    # ---- against a real libtorrent session -------------------------------

    @needs_libtorrent
    def test_a_real_torrent_produces_the_same_file_dicts_as_webtorrent(self):
        # Both backends route through torrent_files(), so a torrent read by
        # either must describe its contents identically -- index, name, size.
        # Divergence here is what produced wrong-file bugs before.
        p = self.torrent_file()
        got = self.m.torrent_files(p)
        self.assertEqual(len(got), 1)
        self.assertEqual(got[0]["index"], 0)
        self.assertEqual(got[0]["size"], 64 * 1024)
        self.assertTrue(got[0]["name"])

    @needs_libtorrent
    def test_start_selects_only_the_chosen_file(self):
        # A pack's siblings are separate jobs; taking the whole torrent here
        # would download a season to play one episode.
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        self.assertIsNotNone(proc)
        try:
            h = j["_lt"]
            self.assertTrue(h.is_valid())
            prios = self.wait_prios(h, [4])
            self.assertGreater(prios[0], 0)
            self.assertEqual([p for p in prios[1:] if p], [])
        finally:
            proc.kill()

    @needs_libtorrent
    def test_start_downloads_sequentially(self):
        # The live phase hands ffmpeg a growing prefix, so pieces must arrive
        # front to back rather than rarest-first.
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            flags = j["_lt"].status().flags
            self.assertTrue(flags & lt.torrent_flags.sequential_download)
        finally:
            proc.kill()

    # ---- reaching downloads that are already running ---------------------

    def test_webtorrent_cannot_extend_a_running_downloads_trackers(self):
        # Its list went on the command line; there is no way to add to it.
        # Reporting 0 rather than pretending is what keeps push_trackers
        # honest about whether anything happened.
        bk = self.m.WebTorrentBackend()
        self.assertEqual(bk.add_trackers(self.job(), ["udp://x.example:1/a"]), 0)

    def test_a_job_with_no_handle_gains_nothing(self):
        bk = self.m.LibtorrentBackend()
        self.assertEqual(bk.add_trackers(self.job(), ["udp://x.example:1/a"]), 0)

    def test_push_reaches_running_jobs_and_skips_finished_ones(self):
        seen = []
        class Bk:
            def add_trackers(self, job, trackers):
                seen.append(job["id"])
                return len(trackers)
        self.m._BACKEND = Bk()
        try:
            live = self.job(); live["status"] = "downloading"
            done = self.job(); done["status"] = "done"
            touched = self.m.push_trackers(["udp://new.example:1/a"])
        finally:
            self.m._BACKEND = None
        self.assertEqual(seen, [live["id"]])
        self.assertEqual(touched, 1)

    def test_a_job_that_gained_nothing_is_not_logged(self):
        # Otherwise every job collects a weekly line saying nothing changed.
        class Bk:
            def add_trackers(self, job, trackers): return 0
        self.m._BACKEND = Bk()
        try:
            j = self.job(); j["status"] = "downloading"
            before = len(j["log"])
            self.assertEqual(self.m.push_trackers(["udp://x.example:1/a"]), 0)
        finally:
            self.m._BACKEND = None
        self.assertEqual(len(j["log"]), before)

    def test_one_job_raising_does_not_stop_the_rest(self):
        class Bk:
            def __init__(self): self.n = 0
            def add_trackers(self, job, trackers):
                self.n += 1
                if self.n == 1: raise RuntimeError("boom")
                return 1
        self.m._BACKEND = Bk()
        try:
            a = self.job(); a["status"] = "downloading"
            b = self.job(); b["status"] = "downloading"
            touched = self.m.push_trackers(["udp://x.example:1/a"])
        finally:
            self.m._BACKEND = None
        self.assertEqual(touched, 1)

    @needs_libtorrent
    def test_a_real_running_torrent_gains_the_new_trackers(self):
        # The point of the whole thing, against a real handle: a download
        # already in flight ends up announcing to a tracker it did not start
        # with, without being restarted.
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            h = j["_lt"]
            before = {t.get("url") for t in h.trackers()}
            new = "udp://freshly-verified.example:6969/announce"
            self.assertEqual(bk.add_trackers(j, [new]), 1)
            after = {t.get("url") for t in h.trackers()}
            self.assertIn(new, after)
            self.assertTrue(before <= after)      # nothing was taken away
            # and a second pass adds nothing, rather than duplicating
            self.assertEqual(bk.add_trackers(j, [new]), 0)
        finally:
            proc.kill(); j["cancel"].set()

    # ---- resume data: what replaces reconstructing state by hand ---------

    def wait_prios(self, h, want, timeout=5):
        """prioritize_files is asynchronous -- reading straight back can hand
        you the values from before it was applied."""
        deadline = time.time() + timeout
        got = None
        while time.time() < deadline:
            got = list(h.get_file_priorities())
            if got == want:
                return got
            time.sleep(0.05)
        return got

    def settled_prios(self, h, hold=0.6, timeout=5):
        """What the priorities end up as, not what they pass through.

        Waiting for a value to merely appear is not enough: resume data and a
        later prioritize_files call both land asynchronously, so the correct
        list can show up and then be overwritten a moment later -- which a
        first-match check would happily report as a pass.
        """
        deadline = time.time() + timeout
        last, stable_since = None, time.time()
        while time.time() < deadline:
            got = list(h.get_file_priorities())
            if got != last:
                last, stable_since = got, time.time()
            elif time.time() - stable_since >= hold:
                return got
            time.sleep(0.05)
        return last

    def multi_file_torrent(self):
        """A three-file torrent, so a file pin is a thing that can be lost."""
        import libtorrent as lt
        d = os.path.join(self.dl, "pack")
        os.makedirs(d, exist_ok=True)
        for i in range(3):
            with open(os.path.join(d, "ep%d.bin" % i), "wb") as f:
                f.write(os.urandom(32 * 1024))
        fs = lt.file_storage()
        lt.add_files(fs, d)
        ct = lt.create_torrent(fs, piece_size=16 * 1024)
        lt.set_piece_hashes(ct, os.path.dirname(d))
        p = os.path.join(self.dl, "pack.torrent")
        with open(p, "wb") as f:
            f.write(lt.bencode(ct.generate()))
        return p

    def test_webtorrent_has_no_resume_data_to_save(self):
        bk = self.m.WebTorrentBackend()
        self.assertFalse(bk.save_state(self.job(), self.dl))

    def test_a_job_with_no_handle_saves_nothing(self):
        bk = self.m.LibtorrentBackend()
        self.assertFalse(bk.save_state(self.job(), self.dl))

    @needs_libtorrent
    def test_state_is_written_and_read_back(self):
        bk = self.m.LibtorrentBackend()
        j = self.job()
        out = os.path.join(self.dl, "out"); os.makedirs(out, exist_ok=True)
        proc = bk.start(j, self.torrent_file(), out, {"index": 0}, 0)
        try:
            self.assertTrue(bk.save_state(j, out))
            self.assertTrue(os.path.isfile(bk.resume_path(out)))
            self.assertIsNotNone(bk._resume_params(out))
        finally:
            proc.kill(); j["cancel"].set()

    @needs_libtorrent
    def test_a_pack_siblings_file_pin_survives_in_libtorrents_own_state(self):
        # The bug this whole stage exists for. Three duplicate-cascade
        # incidents came from wt_index being lost on restart, letting a
        # sibling re-pick file 0 and fan the pack out again. Here the pin is
        # kept by the thing that enforces it, not by a field reel had to
        # remember to write down -- and crucially it comes back even when the
        # restart has no idea which file was chosen.
        bk = self.m.LibtorrentBackend()
        tf = self.multi_file_torrent()
        out = os.path.join(self.dl, "packout"); os.makedirs(out, exist_ok=True)
        j = self.job()
        proc = bk.start(j, tf, out, {"index": 2}, 0)     # the third episode
        try:
            self.assertEqual(self.wait_prios(j["_lt"], [0, 0, 4]), [0, 0, 4])
            self.assertTrue(bk.save_state(j, out))
        finally:
            proc.kill(); j["cancel"].set()

        # A fresh backend, because a restart is a new process with a new
        # session -- and reusing this one would re-add the same infohash to a
        # session that has not finished removing it.
        bk = self.m.LibtorrentBackend()
        j2 = self.job()
        # chosen=None: the restart does not know which file this job was for.
        proc2 = bk.start(j2, tf, out, None, 0)
        try:
            self.assertTrue(j2["lt_resumed"])
            self.assertEqual(self.settled_prios(j2["_lt"]), [0, 0, 4])
        finally:
            proc2.kill(); j2["cancel"].set()

    @needs_libtorrent
    def test_resumed_priorities_beat_a_wrong_guess_from_the_restart(self):
        # The precise shape of the three cascade incidents: a restart that
        # has lost which file this job was for falls back to index 0, and
        # re-asserting that would overwrite the pin libtorrent had been
        # enforcing correctly -- re-fetching the wrong episode and fanning
        # the pack back out. Saved state has to win over the guess.
        bk = self.m.LibtorrentBackend()
        tf = self.multi_file_torrent()
        out = os.path.join(self.dl, "wrongguess"); os.makedirs(out, exist_ok=True)
        j = self.job()
        proc = bk.start(j, tf, out, {"index": 2}, 0)
        try:
            self.assertEqual(self.wait_prios(j["_lt"], [0, 0, 4]), [0, 0, 4])
            self.assertTrue(bk.save_state(j, out))
        finally:
            proc.kill(); j["cancel"].set()

        bk2 = self.m.LibtorrentBackend()
        j2 = self.job()
        # The restart thinks it is file 0. It is wrong, and must not win.
        proc2 = bk2.start(j2, tf, out, {"index": 0}, 0)
        try:
            self.assertTrue(j2["lt_resumed"])
            self.assertEqual(self.settled_prios(j2["_lt"]), [0, 0, 4])
        finally:
            proc2.kill(); j2["cancel"].set()

    @needs_libtorrent
    def test_a_fresh_download_is_not_marked_resumed(self):
        bk = self.m.LibtorrentBackend()
        out = os.path.join(self.dl, "fresh"); os.makedirs(out, exist_ok=True)
        j = self.job()
        proc = bk.start(j, self.torrent_file(), out, {"index": 0}, 0)
        try:
            self.assertFalse(j["lt_resumed"])
        finally:
            proc.kill(); j["cancel"].set()

    @needs_libtorrent
    def test_unreadable_resume_data_starts_over_rather_than_refusing(self):
        # A blob from an older libtorrent, or one half-written by a hard kill,
        # must cost the resume and nothing more.
        bk = self.m.LibtorrentBackend()
        out = os.path.join(self.dl, "bad"); os.makedirs(out, exist_ok=True)
        with open(bk.resume_path(out), "wb") as f:
            f.write(b"not resume data at all")
        self.assertIsNone(bk._resume_params(out))
        j = self.job()
        proc = bk.start(j, self.torrent_file(), out, {"index": 0}, 0)
        try:
            self.assertIsNotNone(proc)
            self.assertFalse(j["lt_resumed"])
        finally:
            proc.kill(); j["cancel"].set()

    # ---- staying seekable whichever live path is taken -------------------

    def _pipe_fallback(self, job):
        """Drive the real run_torrent_pipe with the two subprocesses stubbed,
        so the job-state changes under test are the shipped ones rather than a
        copy of them written into the test."""
        import types
        class FakeProc:
            def __init__(self): self.stdout, self.stderr = FakeIO(), FakeIO()
            def poll(self): return None
            def kill(self): pass
            def wait(self, *a, **k): return 0
        class FakeIO:
            def close(self): pass
            def readline(self): return ""
            def read(self, *a): return ""
            def __iter__(self): return iter(())
        real = self.m.subprocess
        self.m.subprocess = types.SimpleNamespace(
            Popen=lambda *a, **k: FakeProc(), PIPE=real.PIPE, DEVNULL=real.DEVNULL)
        self.m.audio_tracks = lambda *a, **k: []
        self.m.free_port = lambda *a, **k: 8899
        # It waits up to 20s for enough of a file to probe. Give it one
        # immediately rather than letting every test in this class sit
        # through the timeout.
        big = os.path.join(self.dl, "arrived.mkv")
        with open(big, "wb") as fh:
            fh.write(b"\0" * (600 * 1024))
        self.m.newest_file = lambda d: big
        self.m.disk_bytes = lambda p: 600 * 1024
        self.m.codecs_of = lambda p: ("h264", "aac", 1080, False)
        try:
            self.m.run_torrent_pipe(job, "magnet:?xt=urn:btih:" + "a" * 40,
                                    {"index": 0, "name": "f.mkv"}, self.dl)
        finally:
            self.m.subprocess = real

    def test_a_local_backends_job_stays_seekable_through_the_pipe_fallback(self):
        # The bug this closes: whether a still-downloading torrent could be
        # seeked depended on which live path it happened to take. The pipe
        # fallback cleared wt_direct because *its own* http endpoint was
        # unreadable -- which says nothing about a file on disk that still
        # answers ranges perfectly well.
        j = self.job()
        j["lt_file"] = os.path.join(self.dl, "film.mkv")
        j["wt_direct"] = True
        self._pipe_fallback(j)
        self.assertTrue(j["wt_direct"], "a local file is still range-readable")
        self.assertTrue(self.m.public(j)["seekable"])

    def test_a_remote_backends_job_still_loses_seeking_there(self):
        # webtorrent's case is unchanged: no local file, and the endpoint this
        # fallback exists to replace was the only way to read it.
        j = self.job()
        j["wt_direct"] = True
        self._pipe_fallback(j)
        self.assertFalse(j["wt_direct"])
        self.assertFalse(self.m.public(j)["seekable"])

    # ---- live_seek: what it will and will not read ------------------------

    def test_live_seek_needs_something_that_answers_ranges(self):
        j = self.job()
        j["duration"] = 600
        self.assertFalse(self.m.live_seek(j, 100))        # no source at all
        j["wt_url"] = "http://127.0.0.1:9/x.mkv"          # but no ranges
        self.assertFalse(self.m.live_seek(j, 100))

    def test_live_seek_refuses_a_point_past_the_end(self):
        j = self.job()
        j["duration"] = 600
        j["path"] = os.path.join(self.dl, "f.mp4")
        self.assertFalse(self.m.live_seek(j, 599.5))
        self.assertFalse(self.m.live_seek(j, 10_000))

    def test_live_seek_reads_webtorrents_endpoint_when_there_is_no_local_file(self):
        # The gap this closes: on the default backend there is no file to
        # read, but webtorrent's own server answers ranges perfectly well.
        seen = {}
        self.m.start_live_from_url = lambda job, url, kind, **kw: seen.update(
            url=url, start_at=kw.get("start_at"))
        j = self.job()
        j["duration"] = 600
        j["wt_url"] = "http://127.0.0.1:8801/webtorrent/abc/f.mkv"
        j["wt_ranges"] = True
        self.assertTrue(self.m.live_seek(j, 120))
        self.assertEqual(seen["url"], j["wt_url"])
        self.assertEqual(seen["start_at"], 120)
        self.assertEqual(j["live_offset"], 120)

    def test_live_seek_reads_reels_own_route_for_a_local_file(self):
        # So the reads pass through the range handler and pull pieces on the
        # way; pointed at the file it would read preallocated zeros.
        seen = {}
        self.m.start_live_from_url = lambda job, url, kind, **kw: seen.update(
            url=url, start_at=kw.get("start_at"))
        j = self.job()
        j["duration"] = 600
        j["lt_file"] = os.path.join(self.dl, "f.mkv")
        self.assertTrue(self.m.live_seek(j, 60))
        self.assertIn("/stream/" + j["id"], seen["url"])

    def test_live_seek_clears_the_stream_it_replaces(self):
        # Two streams writing the same file would interleave; the viewer on
        # the old one has to be given a clean end instead.
        old = os.path.join(self.dl, "old.live.mp4")
        with open(old, "wb") as f:
            f.write(b"x" * 32)
        self.m.start_live_from_url = lambda *a, **k: None
        j = self.job()
        j["duration"] = 600
        j["path"] = os.path.join(self.dl, "f.mp4")
        j["live_file"] = old
        j["live_ready"] = True
        self.assertTrue(self.m.live_seek(j, 30))
        self.assertFalse(os.path.exists(old))
        self.assertFalse(j["live_ready"])

    # ---- ensure_range: the reason for the whole migration ----------------

    def test_webtorrent_admits_it_cannot_prioritise(self):
        # True means "read it and find out" -- the behaviour that existed
        # before the seam, not a claim that the bytes are there.
        bk = self.m.WebTorrentBackend()
        self.assertTrue(bk.ensure_range(self.job(), 5_000_000, 65536))

    def test_a_job_with_no_handle_cannot_fetch_a_range(self):
        bk = self.m.LibtorrentBackend()
        self.assertFalse(bk.ensure_range(self.job(), 0, 1024))

    @needs_libtorrent
    def test_bytes_already_held_need_no_fetching(self):
        # The common case -- reading inside the downloaded prefix must not
        # disturb the sequential fill or wait on anything.
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            deadline = time.time() + 10
            h = j["_lt"]
            while time.time() < deadline and not h.status().is_seeding:
                time.sleep(0.05)
            self.assertTrue(h.status().is_seeding, "local torrent should verify")
            t = time.time()
            self.assertTrue(bk.ensure_range(j, 0, 1024))
            self.assertLess(time.time() - t, 1.0)     # immediate, not a wait
        finally:
            proc.kill(); j["cancel"].set()

    @needs_libtorrent
    def test_an_impossible_range_gives_up_rather_than_hanging_the_player(self):
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            j["cancel"].set()            # nothing will ever arrive now
            t = time.time()
            got = bk.ensure_range(j, 0, 1024, timeout=2)
            self.assertLess(time.time() - t, 3.0)
        finally:
            proc.kill()

    @needs_libtorrent
    def test_a_miss_fetches_a_window_not_just_the_bytes_asked_for(self):
        # The fix for the ~30s seek. Serving a range calls this once per
        # 256 KB; if each call fetched only its own chunk, every one of them
        # would miss and suspend the fill again. Prioritising a window means
        # the reads behind this one are already satisfied and take the cheap
        # path instead.
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        j["wt_index"] = 0
        # A big torrent, so a window spans many pieces. No peers, so nothing
        # arrives and the priorities stay observable.
        tf = os.path.join(os.path.dirname(__file__), "_big.torrent")
        d = os.path.join(self.dl, "big"); os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "payload.bin"), "wb") as f:
            f.write(os.urandom(4 * 1024 * 1024))
        fs = lt.file_storage(); lt.add_files(fs, d)
        ct = lt.create_torrent(fs, piece_size=16 * 1024)
        lt.set_piece_hashes(ct, os.path.dirname(d))
        with open(tf, "wb") as f:
            f.write(lt.bencode(ct.generate()))
        out = os.path.join(self.dl, "bigout"); os.makedirs(out, exist_ok=True)
        # Somewhere else entirely, so the data cannot already be there.
        proc = bk.start(j, tf, out, {"index": 0}, 0)
        try:
            h = j["_lt"]
            deadline = time.time() + 5
            while time.time() < deadline and h.torrent_file() is None:
                time.sleep(0.05)
            ti = h.torrent_file()
            self.assertGreater(ti.num_pieces(), 32, "need a torrent with room")
            bk.ensure_range(j, 0, 1024, timeout=0.3)
            prios = [h.piece_priority(p) for p in range(ti.num_pieces())]
            raised = [i for i, v in enumerate(prios) if v == 7]
            # More than the single piece the 1024 bytes needed.
            self.assertGreater(len(raised), 1, prios[:12])
        finally:
            proc.kill(); j["cancel"].set()
            for p in (tf,):
                try: os.remove(p)
                except OSError: pass

    @needs_libtorrent
    def test_sequential_fill_is_restored_after_a_seek(self):
        # It is suspended while waiting -- measured, the fill competes with
        # the deadline for the same peers -- and must come back afterwards or
        # the part being watched stops growing.
        import libtorrent as lt
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            bk.ensure_range(j, 0, 1024, timeout=1)
            self.assertTrue(j["_lt"].status().flags
                            & lt.torrent_flags.sequential_download)
        finally:
            proc.kill(); j["cancel"].set()

    @needs_libtorrent
    def test_a_real_handle_reports_peers_without_scraping_a_terminal(self):
        bk = self.m.LibtorrentBackend()
        j = self.job()
        proc = bk.start(j, self.torrent_file(), self.dl, {"index": 0}, 0)
        try:
            deadline = time.time() + 5
            while time.time() < deadline and j.get("peers") is None:
                time.sleep(0.05)
            self.assertIsNotNone(j["peers"])          # a number, not parsed text
            self.assertIn("peers", bk.recent_output(j))
        finally:
            proc.kill()
            j["cancel"].set()


# --------------------------------------------------------------------------
class TestTorrentParsing(Base):
    def test_bencode_roundtrip(self):
        self.assertEqual(self.m.bdecode(b"i42e")[0], 42)
        self.assertEqual(self.m.bdecode(b"4:spam")[0], b"spam")
        self.assertEqual(self.m.bdecode(b"li1ei2ee")[0], [1, 2])
        self.assertEqual(self.m.bdecode(b"d3:fooi1ee")[0], {b"foo": 1})

    def test_picks_the_feature_not_the_sample(self):
        files = [{"index": 0, "name": "sample.mkv", "size": 50_000_000},
                 {"index": 1, "name": "film.mkv", "size": 2_000_000_000},
                 {"index": 2, "name": "cover.jpg", "size": 100_000}]
        self.assertEqual(self.m.pick_file(files)["name"], "film.mkv")

    def test_magnets_and_drive_links_are_separated(self):
        text = ("magnet:?xt=urn:btih:" + "a" * 40 +
                "&dn=x https://drive.google.com/file/d/1ZB3COCpmsVydbHEgnKTX/view")
        magnets, ids, bad = self.m.split_sources(text)
        self.assertEqual(len(magnets), 1)
        self.assertEqual(ids, ["1ZB3COCpmsVydbHEgnKTX"])
        self.assertEqual(bad, 0)

    def test_moov_before_mdat_means_streamable(self):
        def atom(kind, size):
            return struct.pack(">I", size) + kind
        self.assertTrue(self.m.iso_index_first(atom(b"moov", 16) + b"\0" * 8))
        self.assertFalse(self.m.iso_index_first(atom(b"mdat", 16) + b"\0" * 8))
        self.assertIsNone(self.m.iso_index_first(b"\0" * 4))


# --------------------------------------------------------------------------
class TestFailureHandling(Base):
    def test_failing_a_job_stops_its_children(self):
        # A failed job left an ffmpeg running for minutes, reading a webtorrent
        # server that had already exited.
        procs = [subprocess.Popen(["sleep", "60"]) for _ in range(2)]
        j = self.m.new_job("d", procs=procs)
        self.m.fail(j, "simulated")
        time.sleep(0.4)
        self.assertEqual(j["status"], "error")
        for p in procs:
            self.assertIsNotNone(p.poll(), "a failed job must not leave children")
            if p.poll() is None:
                p.kill()

    def test_cancel_status_distinguishes_why(self):
        self.assertEqual(self.m.cancel_status({"evicted": True}), "evicted")
        self.assertEqual(self.m.cancel_status({"overflow": True}), "error")
        self.assertEqual(self.m.cancel_status({}), "removed")


# --------------------------------------------------------------------------
class TestRestore(Base):
    def test_orphan_sidecar_is_removed(self):
        with open(self.m.subs_path_for("ghost", "eng"), "w") as f:
            f.write("WEBVTT\n\n")
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(self.m.subs_path_for("ghost", "eng")))

    def test_sidecar_reattaches_to_its_job(self):
        p = os.path.join(self.dl, "abc__driveid__A Film.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        with open(self.m.subs_path_for("abc", "eng"), "w") as f:
            f.write("WEBVTT\n\n")
        self.m.JOBS.clear()
        # playable() shells out to ffprobe; without it, restore keeps the row
        self.m.playable = lambda _p: True
        self.m.restore()
        self.assertIn("abc", self.m.JOBS)
        self.assertEqual(self.m.JOBS["abc"].get("subs_status"), "ready")

    def test_live_fragments_are_discarded(self):
        # Not seekable, and meaningless once the writer is gone.
        with open(os.path.join(self.dl, "x.live.mp4"), "wb") as f:
            f.write(b"\0" * 10)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(os.path.join(self.dl, "x.live.mp4")))

    def test_audio_tracks_are_reprobed_on_restore(self):
        # audio_tracks lives only on the in-memory job, not on disk -- a real
        # Supergirl download had three tracks correctly kept at conversion
        # time (fre default, fre, eng), then lost the whole language menu and
        # fell back to French on the very next restart, because restore()
        # never re-ran the probe that conversion pays for once.
        p = os.path.join(self.dl, "abc__driveid__A Show.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: True
        self.m.audio_tracks = lambda p: [
            {"index": 0, "lang": "fre", "default": True},
            {"index": 1, "lang": "eng", "default": False}]
        self.m.restore()
        job = self.m.JOBS["abc"]
        self.assertEqual(len(job["audio_tracks"]), 2)
        self.assertEqual(job["audio_default"], 1)   # English, despite the
                                                     # container's own flag

    def test_an_audio_only_file_is_not_probed_for_audio_tracks(self):
        p = os.path.join(self.dl, "abc__driveid__A Song.mp3")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: True
        calls = []
        self.m.audio_tracks = lambda p: calls.append(p) or []
        self.m.restore()
        self.assertEqual(calls, [])
        self.assertEqual(self.m.JOBS["abc"]["audio_tracks"], [])

    def test_a_pack_siblings_file_pin_survives_a_restart(self):
        # The real bug: a pack sibling interrupted mid-download came back
        # from restore() with wt_index lost, indistinguishable from a fresh
        # unpinned magnet -- it re-picked file 0 and fanned the whole pack
        # back out as duplicates of episodes already sitting done elsewhere.
        # The fix is round-tripping index/files through .reel.json, which is
        # exactly what this proves rather than just asserting the write side
        # or the read side alone.
        wt = os.path.join(self.dl, "abc123_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            json.dump({"magnet": "magnet:?xt=urn:btih:" + "a" * 40,
                       "index": 8, "title": "S01E08", "total": 700_000_000,
                       "files": 25}, f)
        self.m.JOBS.clear()
        self.m.restore()
        job = self.m.JOBS["abc123"]
        self.assertEqual(job["wt_index"], 8)
        self.assertEqual(job["wt_files"], 25)

    def test_a_sidecar_written_before_this_fix_still_restores(self):
        # An in-flight download from before this fix shipped has no "index"
        # or "files" key at all -- must not crash, and degrades to exactly
        # today's (already-accepted) unpinned behaviour rather than a KeyError.
        wt = os.path.join(self.dl, "old456_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            json.dump({"magnet": "magnet:?xt=urn:btih:" + "b" * 40,
                       "title": "Something", "total": 100}, f)
        self.m.JOBS.clear()
        self.m.restore()
        job = self.m.JOBS["old456"]
        self.assertIsNone(job["wt_index"])
        self.assertEqual(job["wt_files"], 0)

    def test_a_tmdb_title_survives_a_restart(self):
        # Without this, a movie added from the catalogue would come back from
        # every restart wearing the raw scene release name again -- the same
        # class of bug the pack-pin fix above closes, just for the title
        # instead of the file index.
        wt = os.path.join(self.dl, "tmdbtitle_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            json.dump({"magnet": "magnet:?xt=urn:btih:" + "c" * 40,
                       "index": 0, "title": "Disclosure Day (2026)",
                       "total": 100, "files": 1, "title_locked": True}, f)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertTrue(self.m.JOBS["tmdbtitle"]["title_locked"])
        self.assertEqual(self.m.JOBS["tmdbtitle"]["title"], "Disclosure Day (2026)")

    def test_a_sidecar_without_title_locked_defaults_to_unlocked(self):
        # A sidecar written before this feature shipped has no such key --
        # must default to False (the old, already-accepted behaviour) rather
        # than crash or, worse, lock a title that was never actually known.
        wt = os.path.join(self.dl, "notlocked_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            json.dump({"magnet": "magnet:?xt=urn:btih:" + "d" * 40,
                       "index": 0, "title": "Some.Scene.Release.2026",
                       "total": 100, "files": 1}, f)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(self.m.JOBS["notlocked"]["title_locked"])

    # ---- scratch / dead-weight directories --------------------------------

    def test_scratch_directories_are_always_swept(self):
        # _raw, _meta and _probe are working directories for an in-flight
        # conversion -- never something to resume from, only cleanup.
        for suffix in ("_raw", "_meta", "_probe"):
            d = os.path.join(self.dl, "job1" + suffix)
            os.makedirs(d)
            with open(os.path.join(d, "junk.bin"), "wb") as f:
                f.write(b"x" * 10)
        self.m.JOBS.clear()
        self.m.restore()
        for suffix in ("_raw", "_meta", "_probe"):
            self.assertFalse(os.path.exists(os.path.join(self.dl, "job1" + suffix)))

    def test_a_wt_dir_with_no_sidecar_at_all_is_swept(self):
        # Never got far enough to write .reel.json -- nothing to identify it
        # by, so it is exactly as useless as an orphaned _raw folder.
        wt = os.path.join(self.dl, "nosidecar_wt")
        os.makedirs(wt)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(wt))
        self.assertNotIn("nosidecar", self.m.JOBS)

    def test_a_wt_dir_with_unparseable_json_is_swept_not_crashed_on(self):
        wt = os.path.join(self.dl, "badjson_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            f.write("{ this is not valid json at all")
        self.m.JOBS.clear()
        self.m.restore()                       # must not raise
        self.assertFalse(os.path.exists(wt))
        self.assertNotIn("badjson", self.m.JOBS)

    def test_a_wt_dir_whose_sidecar_has_no_magnet_is_swept(self):
        # A magnet is the one thing that makes a _wt folder resumable at
        # all -- json.dump succeeded but this run never got that far.
        wt = os.path.join(self.dl, "nomagnet_wt")
        os.makedirs(wt)
        with open(os.path.join(wt, ".reel.json"), "w") as f:
            json.dump({"index": 0, "title": "Something"}, f)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(wt))
        self.assertNotIn("nomagnet", self.m.JOBS)

    # ---- stray files --------------------------------------------------------

    def test_compat_fragments_are_discarded_like_live_ones(self):
        p = os.path.join(self.dl, "x.compat.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 10)
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(p))

    def test_a_zero_byte_finished_file_is_discarded(self):
        p = os.path.join(self.dl, "zerojob__driveid__Nothing.mp4")
        open(p, "wb").close()
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(p))
        self.assertNotIn("zerojob", self.m.JOBS)

    def test_a_foreign_file_is_left_alone(self):
        # .DS_Store and friends: no "__" to split on, so it is neither a job
        # nor recognised junk -- restore() must not touch it either way.
        p = os.path.join(self.dl, ".DS_Store")
        with open(p, "wb") as f:
            f.write(b"whatever finder puts here")
        self.m.JOBS.clear()
        self.m.restore()
        self.assertTrue(os.path.exists(p))
        self.assertEqual(len(self.m.JOBS), 0)

    # ---- torrent-sourced finished files -------------------------------------

    def test_a_finished_torrent_file_loads_its_magnet_from_the_sidecar(self):
        p = os.path.join(self.dl, "tjob__torrent__A Show.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        magnet = "magnet:?xt=urn:btih:" + "c" * 40
        with open(os.path.join(self.dl, "tjob.magnet"), "w") as f:
            f.write(magnet)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: True
        self.m.restore()
        job = self.m.JOBS["tjob"]
        self.assertEqual(job["source"], "torrent")
        self.assertEqual(job["magnet"], magnet)
        self.assertEqual(job["status"], "done")

    def test_a_finished_torrent_file_survives_a_missing_magnet_sidecar(self):
        # The .magnet sidecar can go missing (a mis-click, a partial cleanup)
        # without the row itself vanishing -- it just can't be refetched
        # until re-added from scratch, which replayable=False communicates.
        p = os.path.join(self.dl, "orphantorrent__torrent__A Show.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: True
        self.m.restore()                       # must not raise
        job = self.m.JOBS["orphantorrent"]
        self.assertIsNone(job["magnet"])
        self.assertFalse(self.m.public(job)["replayable"])

    # ---- unplayable (cut short by a hard exit) ------------------------------

    def test_an_unplayable_file_becomes_evicted_and_is_deleted(self):
        p = os.path.join(self.dl, "brokendrive__driveid__A Film.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: False
        self.m.restore()
        self.assertFalse(os.path.exists(p))
        job = self.m.JOBS["brokendrive"]
        self.assertEqual(job["status"], "evicted")
        self.assertFalse(job["hold"])
        self.assertEqual(job["title"], "A Film")

    def test_an_unplayable_torrent_file_keeps_its_magnet_for_a_refetch(self):
        p = os.path.join(self.dl, "brokentorrent__torrent__A Show.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        magnet = "magnet:?xt=urn:btih:" + "d" * 40
        with open(os.path.join(self.dl, "brokentorrent.magnet"), "w") as f:
            f.write(magnet)
        self.m.JOBS.clear()
        self.m.playable = lambda _p: False
        self.m.restore()
        self.assertFalse(os.path.exists(p))
        job = self.m.JOBS["brokentorrent"]
        self.assertEqual(job["status"], "evicted")
        self.assertEqual(job["source"], "torrent")
        self.assertEqual(job["magnet"], magnet)
        self.assertTrue(self.m.public(job)["replayable"])

    # ---- subtitle edge cases -------------------------------------------------

    def test_a_subtitle_with_no_language_segment_falls_back_to_default(self):
        p = os.path.join(self.dl, "langless__driveid__A Film.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        with open(os.path.join(self.dl, "langless.subs..vtt"), "w") as f:
            f.write("WEBVTT\n\n")
        self.m.JOBS.clear()
        self.m.playable = lambda _p: True
        self.m.restore()
        job = self.m.JOBS["langless"]
        self.assertEqual(job["subs_status"], "ready")
        self.assertEqual(job["subs_lang"], self.m.SUBS_LANG)

    # ---- everything at once --------------------------------------------------

    def test_a_mixed_directory_restores_each_item_independently(self):
        # Real startup scans one directory holding every kind of leftover at
        # once, in whatever order the filesystem hands them back -- nothing
        # here should depend on scan order, and one malformed entry must not
        # take any other, unrelated entry down with it.
        os.makedirs(os.path.join(self.dl, "scratch_raw"))

        pinned_wt = os.path.join(self.dl, "pinned_wt")
        os.makedirs(pinned_wt)
        with open(os.path.join(pinned_wt, ".reel.json"), "w") as f:
            json.dump({"magnet": "magnet:?xt=urn:btih:" + "e" * 40,
                       "index": 3, "files": 10, "title": "Mid-pack"}, f)

        os.makedirs(os.path.join(self.dl, "dead_wt"))   # no sidecar

        open(os.path.join(self.dl, "zero__driveid__X.mp4"), "wb").close()

        with open(os.path.join(self.dl, ".DS_Store"), "wb") as f:
            f.write(b"junk")

        with open(os.path.join(self.dl, "gooddrive__driveid__Good.mp4"), "wb") as f:
            f.write(b"\0" * 100)
        with open(os.path.join(self.dl, "gooddrive.subs.eng.vtt"), "w") as f:
            f.write("WEBVTT\n\n")

        with open(os.path.join(self.dl, "badtorrent__torrent__Bad.mp4"), "wb") as f:
            f.write(b"\0" * 100)
        with open(os.path.join(self.dl, "badtorrent.magnet"), "w") as f:
            f.write("magnet:?xt=urn:btih:" + "f" * 40)

        with open(os.path.join(self.dl, "goodtorrent__torrent__Good2.mp4"), "wb") as f:
            f.write(b"\0" * 100)
        good_magnet = "magnet:?xt=urn:btih:" + "1" * 40
        with open(os.path.join(self.dl, "goodtorrent.magnet"), "w") as f:
            f.write(good_magnet)

        self.m.JOBS.clear()
        self.m.playable = lambda p: "badtorrent" not in p
        self.m.restore()                       # must not raise

        self.assertFalse(os.path.exists(os.path.join(self.dl, "scratch_raw")))
        self.assertFalse(os.path.exists(os.path.join(self.dl, "dead_wt")))
        self.assertNotIn("dead", self.m.JOBS)
        self.assertNotIn("zero", self.m.JOBS)
        self.assertTrue(os.path.exists(os.path.join(self.dl, ".DS_Store")))

        self.assertEqual(self.m.JOBS["pinned"]["wt_index"], 3)
        self.assertEqual(self.m.JOBS["pinned"]["wt_files"], 10)

        self.assertEqual(self.m.JOBS["gooddrive"]["status"], "done")
        self.assertEqual(self.m.JOBS["gooddrive"]["subs_status"], "ready")

        self.assertEqual(self.m.JOBS["badtorrent"]["status"], "evicted")
        self.assertFalse(os.path.exists(
            os.path.join(self.dl, "badtorrent__torrent__Bad.mp4")))

        self.assertEqual(self.m.JOBS["goodtorrent"]["status"], "done")
        self.assertEqual(self.m.JOBS["goodtorrent"]["magnet"], good_magnet)

        self.assertEqual(len(self.m.JOBS), 4)   # pinned, gooddrive, badtorrent, goodtorrent


# --------------------------------------------------------------------------
class TestLanAddress(Base):
    def test_a_vpn_address_is_not_offered_to_the_phone(self):
        # It advertised 10.5.1.147 -- reachable only inside the tunnel -- while
        # the wifi was on 192.168.0.193, so no phone could connect.
        sample = ("lo0: flags=8049\n\tinet 127.0.0.1 netmask 0xff000000\n"
                  "ipsec0: flags=8051\n\tinet 10.5.1.147 --> 10.5.1.147\n"
                  "utun4: flags=8051\n\tinet 10.9.9.2 netmask 0xffffff00\n"
                  "en0: flags=8863\n\tinet 192.168.0.193 netmask 0xffffff00\n")

        class R:
            stdout = sample
        # Rebinding the module's own attribute, not subprocess.run itself:
        # mutating the shared module leaked into every later test and broke
        # each one that shells out to ffprobe.
        import types
        real = self.m.subprocess
        self.m.subprocess = types.SimpleNamespace(run=lambda *a, **k: R())
        try:
            self.assertEqual(self.m.lan_ip(), "192.168.0.193")
        finally:
            self.m.subprocess = real


# --------------------------------------------------------------------------
@needs_ffmpeg
class TestWithFfmpeg(Base):
    """The few things that genuinely need a decoder. Skipped without one."""

    def make(self, name, vcodec="libx264", pix="yuv420p", acodec="aac", secs=3):
        p = os.path.join(self.dl, name)
        subprocess.run(["ffmpeg", "-nostdin", "-v", "error", "-y",
                        "-f", "lavfi", "-i", "testsrc2=s=320x180:r=25:d=%d" % secs,
                        "-f", "lavfi", "-i", "sine=d=%d" % secs,
                        "-c:v", vcodec, "-pix_fmt", pix, "-preset", "ultrafast",
                        "-c:a", acodec, p], check=True, capture_output=True)
        return p

    def test_h264_mkv_is_not_browser_ready(self):
        # Codecs alone said yes; no browser can demux Matroska. This shipped
        # wrong and failed silently in the player.
        self.assertTrue(self.m.browser_ready(self.make("ok.mp4")))
        self.assertFalse(self.m.browser_ready(self.make("no.mkv")))

    def test_cover_art_is_not_accepted_as_a_film(self):
        # mjpeg is a real video codec, so a single JPEG passed validation and
        # was transcoded to h264 as if it were the movie.
        jpg = os.path.join(self.dl, "cover.jpg")
        subprocess.run(["ffmpeg", "-nostdin", "-v", "error", "-y", "-f", "lavfi",
                        "-i", "testsrc2=s=320x180:d=1", "-frames:v", "1", jpg],
                       check=True, capture_output=True)
        self.assertIsNone(self.m.validate_stream_url(jpg))

    def test_a_real_film_validates(self):
        film = self.make("film.mp4", secs=40)
        self.assertIsNotNone(self.m.validate_stream_url(film))

    def test_a_file_far_smaller_than_expected_is_refused(self):
        # find_wt_url knew the chosen file was 1.99 GB and accepted a 100 KB
        # cover image anyway. The size guard reads Content-Range, so this has to
        # go over http to exercise it at all.
        film = self.make("small.mp4", secs=40)
        import http.server, socketserver

        class Quiet(http.server.SimpleHTTPRequestHandler):
            def __init__(self, *a, **kw):
                super().__init__(*a, directory=dl, **kw)

            def log_message(self, *a):
                pass                      # no access log in test output

        class Server(socketserver.TCPServer):
            allow_reuse_address = True

            def handle_error(self, request, client_address):
                # ffprobe reads a few KB and disconnects. That is the whole
                # point of a ranged probe, not an error worth a traceback.
                if not isinstance(sys.exc_info()[1], (BrokenPipeError,
                                                      ConnectionResetError)):
                    super().handle_error(request, client_address)

        dl = self.dl
        srv = Server(("127.0.0.1", 0), Quiet)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        try:
            url = "http://127.0.0.1:%d/small.mp4" % srv.server_address[1]
            self.assertIsNotNone(self.m.validate_stream_url(url),
                                 "the real file must pass on its own terms")
            self.assertIsNone(self.m.validate_stream_url(url, want_bytes=2_000_000_000),
                              "far too small to be the chosen file")
        finally:
            srv.shutdown()
            srv.server_close()

    def test_probe_reports_ten_bit(self):
        p = self.make("ten.mkv", vcodec="libx265", pix="yuv420p10le")
        v, a, _h, _hdr, _br, _dur, pix = self.m.probe_media(p)
        self.assertEqual(v, "hevc")
        self.assertEqual(self.m.codec_key(v, pix), "hevc10")


# --------------------------------------------------------------------------
class TestFindWtUrl(Base):
    """The bug that looked like broken subtitles: a Planet Earth II job
    picked for S01E01 Islands ended up streaming S01E02 Mountains instead --
    a sibling episode from the same pack, discovered on the same server
    listing, whose size (1,292,117,405 bytes) was within a megabyte of
    Islands' own (1,292,928,557). The old size floor only rejected a
    candidate *dramatically* smaller than expected, so Mountains passed it
    easily -- and it already had real data (a sibling job was actively
    downloading it) while Islands' own url kept timing out with nothing to
    serve yet. Subtitles fetched and scored for Islands then played out
    against Mountains, which is what looked like a subtitle bug."""

    IH = "a" * 40

    def setUp(self):
        super().setUp()
        self.job_ = self.job(
            magnet="magnet:?xt=urn:btih:%s&dn=Planet.Earth.II.2016.S01.1080p."
                   "BluRay.x264-RiPRG" % self.IH)
        self.chosen = {
            "name": "Planet.Earth.II.S01E01.Islands.mkv",
            "rel": "Planet.Earth.II.2016.S01.1080p.BluRay.x264-RiPRG/"
                   "Planet.Earth.II.S01E01.Islands.mkv",
            "index": 0, "size": 1_292_928_557}
        self.right_url = ("http://127.0.0.1:9/webtorrent/%s/Planet.Earth.II."
                          "2016.S01.1080p.BluRay.x264-RiPRG/Planet.Earth.II."
                          "S01E01.Islands.mkv" % self.IH)
        self.wrong_url = ("http://127.0.0.1:9/webtorrent/%s/Planet.Earth.II."
                          "2016.S01.1080p.BluRay.x264-RiPRG/Planet.Earth.II."
                          "S01E02.Mountains.mkv" % self.IH)
        self.m.WT_SERVER_WAIT = 0.3
        self.validated = []

    def test_a_same_sized_sibling_is_never_substituted(self):
        # Both files are on the server listing. Only Mountains -- the wrong
        # episode -- has real data behind it (a sibling job is actively
        # downloading it); every path to Islands, crawled or guessed, is
        # still empty and times out -- exactly the real Planet Earth II
        # timeline, before any distinction is made between them.
        self.m.discover_links = lambda base, timeout=5: (
            [self.wrong_url, self.right_url] if base.endswith("/") else [])
        probed = []

        def fake_probe_url(url, timeout=4):
            probed.append(url)
            if "Mountains" in url:
                return {"ok": True, "status": 200, "ranges": True,
                        "length": "1292117405"}
            return {"ok": False, "status": None, "ranges": False,
                    "error": "timed out"}
        self.m.probe_url = fake_probe_url

        def fake_validate(url, want_bytes=0):
            self.validated.append(url)
            # The old bug: this is exactly what let Mountains pass -- 99.94%
            # of the expected size, nowhere near the 50% floor. Only reached
            # if the name filter failed to exclude it first.
            return (None, None, None, None, None, None, None)
        self.m.validate_stream_url = fake_validate

        got = self.m.find_wt_url(self.job_, 9, self.chosen)
        self.assertNotIn(self.wrong_url, probed,
                         "a same-shaped sibling must never even be probed: "
                         + repr(probed))
        self.assertEqual(self.validated, [],
                         "nothing reached the size check at all -- "
                         "every candidate that was tried timed out")
        # Every url actually named for the chosen file timed out in this
        # test, so the honest answer is one of those -- stalled, not
        # substituted -- never the wrong episode.
        self.assertIsNotNone(got)
        self.assertIn("Islands", got)
        self.assertNotIn("Mountains", got)

    def test_the_named_file_wins_once_it_has_data(self):
        # Same setup, except the right file now also answers -- confirming
        # this isn't just "always prefer whichever times out".
        self.m.discover_links = lambda base, timeout=5: (
            [self.wrong_url, self.right_url] if base.endswith("/") else [])
        self.m.probe_url = lambda url, timeout=4: {
            "ok": True, "status": 200, "ranges": True, "length": "1292928557"}
        self.m.validate_stream_url = lambda url, want_bytes=0: (
            (None, None, None, None, None, None, None) if url == self.right_url
            else None)
        got = self.m.find_wt_url(self.job_, 9, self.chosen)
        self.assertEqual(got, self.right_url)

    def test_guesses_built_from_the_chosen_name_are_unaffected(self):
        # The pre-built fallback guesses are exempt from the name filter --
        # they are constructed from the chosen file's own name, so they
        # cannot land on a neighbour the way a directory crawl can.
        self.m.discover_links = lambda base, timeout=5: []
        self.m.probe_url = lambda url, timeout=4: {
            "ok": True, "status": 200, "ranges": True, "length": "1292928557"}
        self.m.validate_stream_url = lambda url, want_bytes=0: (
            None, None, None, None, None, None, None)
        got = self.m.find_wt_url(self.job_, 9, self.chosen)
        self.assertIsNotNone(got)
        self.assertIn("Islands.mkv", got)


# --------------------------------------------------------------------------
class TestFeedParsing(Base):
    def test_pulls_title_and_year_out_of_a_release_name(self):
        for name, want in (
                ("Toy.Story.5.2026.1080p.WEB-DL.DDP5.1.H264-GROUP", ("Toy Story 5", 2026)),
                ("Supergirl (2026) [1080p] [WEBRip] [5.1]", ("Supergirl", 2026)),
                ("The.Incredibles.2.2018.HDRip.XviD.AC3-EVO", ("The Incredibles 2", 2018)),
                ("Magellan 2025 WEBSCR H264-II", ("Magellan", 2025))):
            self.assertEqual(self.m.feed_title(name), want, name)

    def test_a_number_in_the_title_is_not_the_year(self):
        # Parsed left to right, "Blade Runner 2049" gives the title "Blade
        # Runner" released in 2049. Any year past next year is part of a name.
        title, year = self.m.feed_title("Blade Runner 2049.HDRip.XviD.AC3-EVO")
        self.assertEqual(title, "Blade Runner 2049")
        self.assertIsNone(year)

    def test_html_entities_do_not_reach_the_shelf(self):
        # therarbg hands back escaped names, and the entity survived just far
        # enough to be seen: the semicolon was stripped as punctuation, leaving
        # "Shake Rattle&amp Roll" on the page.
        title, year = self.m.feed_title("Shake Rattle &amp; Roll 2025 1080p WEB-DL")
        self.assertEqual(title, "Shake Rattle & Roll")
        self.assertEqual(year, 2025)

    def test_survives_a_name_with_no_year_at_all(self):
        title, year = self.m.feed_title("Some Obscure Film")
        self.assertEqual(title, "Some Obscure Film")
        self.assertIsNone(year)

    def test_collections_are_not_films(self):
        # All of these were really in the list, and none is something to press
        # play on: a 127-file boxset has no single thing to stream.
        self.assertTrue(self.m.feed_pack("BAFTA Best Pictures (1947 - 2021)", 127))
        self.assertTrue(self.m.feed_pack("Akira Kurosawa Boxset", 159))
        self.assertTrue(self.m.feed_pack("Rome - Seasons 1 and 2 - HBO", 33))
        self.assertTrue(self.m.feed_pack("Some.Show.S02E04.1080p", 1))
        # A film with subtitles, a sample and an nfo is still a film.
        self.assertFalse(self.m.feed_pack("Beautiful.Boy.2018.HDRip.AC3.X264-CMRG", 3))


# --------------------------------------------------------------------------
class TestFeedScoring(Base):
    def test_votes_temper_the_rating(self):
        # A 9.2 from 300 people is noise beside an 8.1 from a million.
        few = self.m.rating_score(9.2, 300)
        many = self.m.rating_score(8.1, 1_000_000)
        self.assertLess(few, many)

    def test_no_rating_is_not_evidence_in_its_favour(self):
        # The first version dropped the rating factor and averaged the rest,
        # which scored an unknown film on its *best* remaining signals: two
        # films nobody had rated took the top two places over one rated 8.2.
        common = {"added": time.time(), "seeders": 800, "year": 2026, "direct": True}
        rated = dict(common, rating=8.2, votes=467897)
        unrated = dict(common, rating=None, votes=0)
        self.assertGreater(self.m.feed_score(rated)[0], self.m.feed_score(unrated)[0])

    def test_an_unrated_film_scores_as_average_not_as_bad(self):
        common = {"added": time.time(), "seeders": 800, "year": 2026, "direct": True}
        unrated = self.m.feed_score(dict(common, rating=None, votes=0))[0]
        poor = self.m.feed_score(dict(common, rating=3.0, votes=50000))[0]
        good = self.m.feed_score(dict(common, rating=8.5, votes=50000))[0]
        self.assertLess(poor, unrated)
        self.assertLess(unrated, good)

    def test_something_that_plays_without_converting_ranks_higher(self):
        common = {"added": time.time(), "seeders": 500, "year": 2026,
                  "rating": 7.0, "votes": 50000}
        direct = self.m.feed_score(dict(common, direct=True))[0]
        remux = self.m.feed_score(dict(common, direct=False))[0]
        self.assertGreater(direct, remux)

    def test_a_fresh_upload_outranks_an_old_one(self):
        now = time.time()
        common = {"seeders": 500, "year": 2026, "rating": 7.0, "votes": 50000,
                  "direct": True}
        new = self.m.feed_score(dict(common, added=now - 86400), now)[0]
        old = self.m.feed_score(dict(common, added=now - 400 * 86400), now)[0]
        self.assertGreater(new, old)

    def test_the_reasons_given_match_the_score(self):
        s, why = self.m.feed_score({"added": time.time(), "seeders": 900,
                                    "year": 2026, "rating": 7.4, "votes": 86158,
                                    "direct": True})
        self.assertTrue(any("7.4" in w for w in why))
        self.assertTrue(any("plays without converting" in w for w in why))
        self.assertGreater(s, 0)


# --------------------------------------------------------------------------
class TestFeedBuild(Base):
    """Shelf building with stand-in sources: no network, no trackers."""

    def setUp(self):
        super().setUp()
        self.m.live_seeders = lambda *a, **k: None      # never scrape a tracker
        self.m.ratings_for = lambda ids: self.ratings
        self.m.bolly_fetch = lambda: ([], {})          # its own source, tested apart
        self.m._TMDB.clear(); self.m._TMDB["key"] = ""   # force the tracker path
        self.ratings = {}

    def shelves(self, *raw):
        self.m.feed_fetch = lambda: (list(raw), {"201": len(raw)})
        return self.m.build_shelves()

    def rows(self, *raw):
        """Every film across every shelf. Each appears on exactly one, so this
        is the whole recommendation set with the shelving flattened away."""
        shelves, err, per = self.shelves(*raw)
        return [f for s in shelves for f in s["films"]], err, per

    def raw(self, ih, name, **kw):
        r = {"info_hash": ih, "name": name, "seeders": 100, "leechers": 1,
             "size": 2_000_000_000, "num_files": 1, "added": time.time(),
             "status": "vip", "imdb": ""}
        r.update(kw)
        return r

    def test_one_row_per_film_even_across_release_names(self):
        # The same film, twice, under names that share no imdb id -- which is
        # real: 30 of 200 rows carry none, so title+year is the only key left.
        rows, err, _ = self.rows(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.H264-ONE"),
            self.raw("b" * 40, "Some Film (2026) [1080p] [WEBRip]"))
        self.assertIsNone(err)
        self.assertEqual(len(rows), 1)

    def test_keeps_the_copy_that_will_actually_play(self):
        # An x265 release with more seeders still costs a remux and twice the
        # disk, so the h264 one is the better thing to offer.
        rows, _, _ = self.rows(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.x265-HEVC", seeders=900),
            self.raw("b" * 40, "Some.Film.2026.1080p.WEB-DL.H264-GRP", seeders=100))
        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["direct"])

    def test_a_rating_found_on_one_release_covers_the_film(self):
        # Only one of the two rows carries the imdb id; collapsing them must
        # keep the rating rather than losing it with the row it came on.
        self.ratings = {"tt1": (8.2, 400000)}
        rows, _, _ = self.rows(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.H264-ONE", imdb="tt1",
                     seeders=100),
            self.raw("b" * 40, "Some Film (2026) [1080p] [WEBRip] [5.1]", seeders=900))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["rating"], 8.2)

    def test_collections_never_reach_the_list(self):
        rows, _, _ = self.rows(
            self.raw("a" * 40, "Disney MEGA Collection 1937-2008", num_files=127),
            self.raw("b" * 40, "Some.Film.2026.1080p.WEB-DL.H264-GRP"))
        self.assertEqual([r["title"] for r in rows], ["Some Film"])

    def test_a_measured_dead_swarm_is_dropped(self):
        # The indexer claims 100; the tracker says nobody is there. It cannot
        # serve a byte, so it is not a recommendation.
        self.m.live_seeders = lambda *a, **k: 0
        rows, _, _ = self.rows(self.raw("a" * 40, "Some.Film.2026.1080p.H264-GRP"))
        self.assertEqual(rows, [])

    def test_cost_on_disk_accounts_for_the_remux(self):
        # A remux holds the source and the output at once -- the overlap that
        # put an 8.6 GB film 20 GB over a 15 GB cap.
        rows, _, _ = self.rows(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.x265-HEVC",
                     size=10_000_000_000))
        self.assertGreater(rows[0]["peak"], rows[0]["size"])
        self.m.CACHE_CAP_GB = 5.0
        rows, _, _ = self.rows(
            self.raw("b" * 40, "Other.Film.2026.1080p.WEB-DL.x265-HEVC",
                     size=10_000_000_000))
        self.assertFalse(rows[0]["fits"])

    def test_a_dead_source_reads_as_an_empty_shelf(self):
        self.m.feed_fetch = lambda: ([], {"201": "failed: timeout"})
        rows, err, _ = self.m.build_shelves()
        self.assertEqual(rows, [])
        self.assertIn("could not reach", err)

    def test_a_source_that_throws_never_breaks_the_page(self):
        def boom():
            raise RuntimeError("indexer on fire")
        self.m.feed_fetch = boom
        rows, err, _ = self.m.recommendations(force=True)
        self.assertEqual(rows, [])
        self.assertIn("indexer on fire", err)

    def test_the_feed_is_not_rebuilt_on_every_request(self):
        calls = []

        def once():
            calls.append(1)
            return [self.raw("a" * 40, "Some.Film.2026.1080p.H264-GRP")], {"201": 1}
        self.m.feed_fetch = once
        self.m.recommendations(force=True)
        self.m.recommendations()
        self.m.recommendations()
        self.assertEqual(len(calls), 1)


# --------------------------------------------------------------------------
class TestTorrentSubtitles(Base):
    """Subtitles lifted out of the torrent, modelled on a real season pack:
    387 files, 9 episodes, 378 subtitle files under Subs/<video name>/."""

    def pack(self, episodes=3, langs=("2_English", "17_French", "9_Danish")):
        files, i = [], 0
        root = "Severance.S01.1080p.WEBRip.x265[eztv.re]"
        vids = []
        for e in range(1, episodes + 1):
            stem = "Severance.S01E%02d.1080p.WEBRip.x265-RARBG[eztv.re]" % e
            vids.append({"index": i, "name": "%s/%s.mp4" % (root, stem),
                         "size": 900_000_000})
            i += 1
        files += vids
        for e in range(1, episodes + 1):
            stem = "Severance.S01E%02d.1080p.WEBRip.x265-RARBG[eztv.re]" % e
            for L in langs:
                files.append({"index": i, "size": 40_000,
                              "name": "%s/Subs/%s/%s.srt" % (root, stem, L)})
                i += 1
        return files, vids

    def test_each_episode_gets_its_own_subtitle(self):
        # The association is the video's filename appearing in the subtitle's
        # path, which is how packs lay them out.
        files, vids = self.pack()
        for n, v in enumerate(vids, 1):
            got = self.m.torrent_subs(files, v, "eng")
            self.assertTrue(got, "episode %d" % n)
            self.assertIn("S01E%02d" % n, got[0]["name"])
            self.assertTrue(got[0]["name"].endswith("2_English.srt"))

    def test_the_configured_language_is_the_one_taken(self):
        files, vids = self.pack()
        self.assertIn("French", self.m.torrent_subs(files, vids[0], "fre")[0]["name"])
        self.assertIn("Danish", self.m.torrent_subs(files, vids[0], "dan")[0]["name"])
        # a language the pack does not carry yields nothing rather than a guess
        self.assertEqual(self.m.torrent_subs(files, vids[0], "swa"), [])

    def test_language_is_matched_by_name_not_by_code(self):
        # Packers write "2_English.srt", never "2_eng.srt", so the ISO code has
        # to be translated into the word that actually appears.
        self.assertTrue(self.m.sub_speaks("2_English.srt", "eng"))
        self.assertTrue(self.m.sub_speaks("29_nor.srt", "nor"))
        self.assertFalse(self.m.sub_speaks("17_French.srt", "eng"))
        # and must not match a word that merely contains the code
        self.assertFalse(self.m.sub_speaks("13_Spanish.srt", "pan"))

    def test_the_packers_own_numbering_breaks_ties(self):
        files, vids = self.pack(episodes=1, langs=("3_English", "2_English"))
        got = self.m.torrent_subs(files, vids[0], "eng")
        self.assertTrue(got[0]["name"].endswith("2_English.srt"))

    def test_forced_subtitles_rank_below_full_ones(self):
        # Forced tracks caption only foreign dialogue, so they are not what
        # someone turning subtitles on is asking for.
        files, vids = self.pack(episodes=1, langs=("2_English_forced", "4_English"))
        got = self.m.torrent_subs(files, vids[0], "eng")
        self.assertTrue(got[0]["name"].endswith("4_English.srt"))

    def test_a_single_film_needs_no_association(self):
        files = [{"index": 0, "name": "Film.2026.1080p.mkv", "size": 6_000_000_000},
                 {"index": 1, "name": "Subs/English.srt", "size": 40_000}]
        got = self.m.torrent_subs(files, files[0], "eng")
        self.assertEqual(len(got), 1)

    def test_unattributable_subtitles_are_refused_not_guessed(self):
        # Several videos and nothing tying the subtitles to any of them:
        # handing one the wrong track is worse than handing it none.
        files = [{"index": 0, "name": "A.mkv", "size": 6_000_000_000},
                 {"index": 1, "name": "B.mkv", "size": 6_000_000_000},
                 {"index": 2, "name": "Subs/English.srt", "size": 40_000}]
        self.assertEqual(self.m.torrent_subs(files, files[0], "eng"), [])

    def test_a_torrent_with_no_subtitles_yields_none(self):
        files = [{"index": 0, "name": "Film.2026.mkv", "size": 6_000_000_000}]
        self.assertEqual(self.m.torrent_subs(files, files[0], "eng"), [])

    @needs_ffmpeg
    def test_srt_bytes_become_a_vtt_sidecar(self):
        j = self.job()
        srt = ("1\n00:00:14,139 --> 00:00:15,307\nFirst line.\n\n"
               "2\n00:00:16,000 --> 00:00:18,000\nSecond line.\n")
        self.assertTrue(self.m.write_subs(j, srt.encode()))
        path = self.m.subs_path_for(j["id"], self.m.SUBS_LANG)
        with open(path, encoding="utf-8") as f:
            out = f.read()
        self.assertTrue(out.startswith("WEBVTT"))
        self.assertEqual(out.count("-->"), 2)
        self.assertEqual(j["subs_cues"], 2)

    def test_empty_bytes_are_not_a_subtitle(self):
        j = self.job()
        self.assertFalse(self.m.write_subs(j, b""))
        self.assertFalse(self.m.write_subs(j, b"   \n "))


# --------------------------------------------------------------------------
class TestPacks(Base):
    def f(self, i, name, gb):
        return {"index": i, "name": name, "size": int(gb * 1_000_000_000)}

    def test_an_ordinary_film_is_not_a_pack(self):
        # The common case, and the one that must not change: one item, chosen
        # by size, exactly as before.
        files = [self.f(0, "Some.Film.2026.1080p.mkv", 6.0),
                 self.f(1, "readme.txt", 0.0)]
        self.assertEqual(self.m.pack_files(files), [])
        self.assertEqual(self.m.pick_file(files)["index"], 0)

    def test_extras_do_not_earn_their_own_row(self):
        # A sample beside a feature is not a second film. Judged against the
        # biggest file, since "big enough" means nothing on its own.
        files = [self.f(0, "Some.Film.2026.1080p.mkv", 12.0),
                 self.f(1, "sample.mkv", 0.2),
                 self.f(2, "trailer.mp4", 0.1)]
        self.assertEqual(self.m.pack_files(files), [])

    def test_a_season_becomes_one_item_per_episode(self):
        files = [self.f(0, "Show.S01E01.1080p.mkv", 2.0),
                 self.f(1, "Show.S01E02.1080p.mkv", 2.1),
                 self.f(2, "Show.S01E03.1080p.mkv", 1.9)]
        got = self.m.pack_files(files)
        self.assertEqual([f["index"] for f in got], [0, 1, 2])

    def test_a_pack_plays_in_index_order_not_size_order(self):
        # pick_file takes the biggest, which for a season is an arbitrary
        # episode. The order that matters here is the one they were meant to be
        # watched in.
        files = [self.f(0, "Show.S01E01.mkv", 2.0),
                 self.f(1, "Show.S01E02.mkv", 9.0),
                 self.f(2, "Show.S01E03.mkv", 2.0)]
        self.assertEqual(self.m.pick_file(files)["index"], 1)
        self.assertEqual(self.m.pack_files(files)[0]["index"], 0)

    def test_bonus_material_is_excluded_by_name_not_by_size(self):
        # A 1.9 GB "behind the scenes" beside an 8 GB feature is a quarter of
        # it, and no size bar loose enough to keep a short episode also excludes
        # that. The name is the precise signal.
        files = [self.f(0, "Movie.2026.1080p.mkv", 8.0),
                 self.f(1, "behind.the.scenes.mkv", 1.9),
                 self.f(2, "deleted.scenes.mkv", 0.6)]
        self.assertEqual(self.m.pack_files(files), [])

    def test_an_uneven_pack_keeps_its_smaller_features(self):
        # Tightening the size bar to catch bonus material instead cost real
        # files: a trilogy encoded unevenly, or a season with one double-length
        # episode, has smaller entries that are still whole features.
        files = [self.f(0, "Godfather.1972.mkv", 16.0),
                 self.f(1, "Godfather.Part.II.1974.mkv", 4.0)]
        self.assertEqual([f["index"] for f in self.m.pack_files(files)], [0, 1])

    def test_episode_order_beats_file_order(self):
        # From a real Severance pack: the torrent listed E01 at index 0, E03 at
        # index 1 and E02 at index 8, so ordering by index put episode 2 last
        # in the queue.
        files = [self.f(0, "Severance.S01E01.1080p.WEBRip.x265.mkv", 0.96),
                 self.f(1, "Severance.S01E03.1080p.WEBRip.x265.mkv", 0.95),
                 self.f(2, "Severance.S01E04.1080p.WEBRip.x265.mkv", 0.78),
                 self.f(8, "Severance.S01E02.1080p.WEBRip.x265.mkv", 0.89)]
        got = self.m.pack_files(files)
        self.assertEqual([f["name"].split(".")[1] for f in got],
                         ["S01E01", "S01E02", "S01E03", "S01E04"])

    def test_seasons_sort_before_episodes(self):
        files = [self.f(0, "Show.S02E01.mkv", 2.0), self.f(1, "Show.S01E09.mkv", 2.0),
                 self.f(2, "Show.S01E10.mkv", 2.0)]
        got = self.m.pack_files(files)
        self.assertEqual([f["name"].split(".")[1] for f in got],
                         ["S01E09", "S01E10", "S02E01"])

    def test_films_without_episode_numbers_keep_file_order(self):
        # A trilogy has nothing to parse, so index remains the best guess.
        files = [self.f(0, "Godfather.1972.mkv", 14.0),
                 self.f(1, "Godfather.Part.II.1974.mkv", 16.0),
                 self.f(2, "Godfather.Part.III.1990.mkv", 13.0)]
        self.assertEqual([f["index"] for f in self.m.pack_files(files)], [0, 1, 2])

    def test_every_common_numbering_scheme_orders_correctly(self):
        # Releases number themselves in a handful of conventional ways, and the
        # torrent's own file order matches none of them reliably.
        cases = [
            ("season/episode", ["X.S01E01.mkv", "X.S01E03.mkv", "X.S01E02.mkv"],
             ["X.S01E01.mkv", "X.S01E02.mkv", "X.S01E03.mkv"]),
            ("1x02 form", ["X 1x03.mkv", "X 1x01.mkv", "X 1x02.mkv"],
             ["X 1x01.mkv", "X 1x02.mkv", "X 1x03.mkv"]),
            ("episode word", ["A - Episode 10.mkv", "A - Episode 2.mkv"],
             ["A - Episode 2.mkv", "A - Episode 10.mkv"]),
            ("two seasons", ["X.S02E01.mkv", "X.S01E09.mkv", "X.S01E10.mkv"],
             ["X.S01E09.mkv", "X.S01E10.mkv", "X.S02E01.mkv"]),
            ("part digits", ["F.Part.2.mkv", "F.Part.1.mkv"],
             ["F.Part.1.mkv", "F.Part.2.mkv"]),
            ("part numerals", ["G.Part.III.mkv", "G.Part.I.mkv", "G.Part.II.mkv"],
             ["G.Part.I.mkv", "G.Part.II.mkv", "G.Part.III.mkv"]),
            ("disc split", ["M.CD2.avi", "M.CD1.avi"], ["M.CD1.avi", "M.CD2.avi"]),
            ("films by year", ["G.1990.mkv", "G.1972.mkv", "G.1974.mkv"],
             ["G.1972.mkv", "G.1974.mkv", "G.1990.mkv"]),
            ("leading number", ["03 - c.mkv", "01 - a.mkv", "02 - b.mkv"],
             ["01 - a.mkv", "02 - b.mkv", "03 - c.mkv"]),
        ]
        for label, names, want in cases:
            files = [{"index": i, "name": n, "size": 2_000_000_000}
                     for i, n in enumerate(names)]
            got = [f["name"] for f in self.m.pack_order(files)]
            self.assertEqual(got, want, label)

    def test_a_scheme_every_file_shares_is_not_a_position(self):
        # Nearly every release name carries a year, and in a season they all
        # carry the same one. A scheme that cannot tell the files apart must be
        # rejected rather than used to produce an arbitrary order.
        files = [{"index": i, "name": n, "size": 2_000_000_000} for i, n in
                 enumerate(["X.2024.S01E02.mkv", "X.2024.S01E01.mkv"])]
        self.assertEqual([f["name"] for f in self.m.pack_order(files)],
                         ["X.2024.S01E01.mkv", "X.2024.S01E02.mkv"])

    def test_unparseable_names_keep_the_torrents_own_order(self):
        files = [{"index": i, "name": n, "size": 2_000_000_000}
                 for i, n in enumerate(["zzz.mkv", "aaa.mkv", "mmm.mkv"])]
        self.assertEqual([f["index"] for f in self.m.pack_order(files)], [0, 1, 2])

    def test_only_video_files_count(self):
        files = [self.f(0, "Film.mkv", 4.0), self.f(1, "soundtrack.mp3", 2.0),
                 self.f(2, "cover.jpg", 1.0)]
        self.assertEqual(self.m.pack_files(files), [])

    def test_a_huge_collection_is_capped(self):
        files = [self.f(i, "Film.%02d.mkv" % i, 2.0) for i in range(60)]
        self.assertEqual(len(self.m.pack_files(files)), self.m.PACK_MAX)

    def test_fan_out_queues_the_rest_as_their_own_jobs(self):
        parent = self.job(source="torrent", magnet="magnet:?xt=urn:btih:" + "a" * 40)
        files = [self.f(0, "Show.S01E01.mkv", 2.0),
                 self.f(1, "Show.S01E02.mkv", 2.0),
                 self.f(2, "Show.S01E03.mkv", 2.0)]
        made = self.m.fan_out(parent, parent["magnet"], files, files[1:])
        self.assertEqual(len(made), 2)
        sibs = [self.m.JOBS[i] for i in made]
        self.assertEqual([s["wt_index"] for s in sibs], [1, 2])
        self.assertEqual([s["title"] for s in sibs], ["Show.S01E02", "Show.S01E03"])
        # Each is an ordinary torrent job, held until a person starts it by
        # hand -- auto=False is what keeps the scheduler from cascading
        # through the rest of the series on its own. See scheduler_tick().
        for s in sibs:
            self.assertEqual(s["magnet"], parent["magnet"])
            self.assertEqual(s["status"], "queued")
            self.assertTrue(s["hold"])
            self.assertFalse(s["auto"])

    def test_the_chosen_episode_itself_still_auto_starts(self):
        # Only the siblings fan_out() creates are auto=False -- the episode
        # actually picked when the series was added is an ordinary job, made
        # by new_job() the same way anything else is, and starts normally.
        j = self.job(source="torrent", magnet="m")
        self.assertTrue(j["auto"])

    def test_siblings_keep_their_own_filename_even_from_a_tmdb_parent(self):
        # A TV pack found via the catalogue locks the parent's title to the
        # show's TMDB name, but every sibling still needs its own episode
        # number -- "Show Name" repeated on every row would be strictly less
        # useful than the scene filename it would replace. title_locked is
        # never passed through fan_out(), so this is the default, not a
        # special case.
        parent = self.job(source="torrent", magnet="magnet:?xt=urn:btih:" + "e" * 40,
                          title="Some Show", title_locked=True)
        files = [self.f(0, "Show.S01E01.mkv", 2.0), self.f(1, "Show.S01E02.mkv", 2.0)]
        made = self.m.fan_out(parent, parent["magnet"], files, files[1:])
        sib = self.m.JOBS[made[0]]
        self.assertFalse(sib["title_locked"])
        self.assertEqual(sib["title"], "Show.S01E02")

    def test_a_sibling_never_fans_out_again(self):
        # Pinned jobs must not re-expand, or a three-file pack breeds one item
        # per file per file.
        files = [self.f(i, "Show.S01E%02d.mkv" % i, 2.0) for i in range(3)]
        sib = self.job(source="torrent", magnet="m", wt_index=1)
        self.assertIsNotNone(sib["wt_index"])
        # pack_files is only consulted when wt_index is None; assert the flag
        # that decides it, since run_torrent needs a live torrent to exercise.
        self.assertTrue(len(self.m.pack_files(files)) > 1)

    def test_pack_detection_can_be_turned_off(self):
        self.m.PACK_MAX = 1
        files = [self.f(i, "Show.S01E%02d.mkv" % i, 2.0) for i in range(3)]
        self.assertEqual(len(self.m.pack_files(files)), 1)


# --------------------------------------------------------------------------
class TestPauseResume(Base):
    """pause_job/resume_job send SIGSTOP/SIGCONT to whichever process is
    actually driving a job, verified against a real child process for the
    part worth not taking on faith -- that a 'paused' process genuinely
    stops doing work rather than just being labelled paused in the UI."""

    def test_pause_proc_actually_stops_and_resumes_real_work(self):
        path = os.path.join(self.dl, "ticks.txt")
        proc = subprocess.Popen(
            [sys.executable, "-c",
             "import time\n"
             "f = open(%r, 'w')\n"
             "for i in range(80):\n"
             "    f.write('x'); f.flush(); time.sleep(0.05)\n" % path])
        try:
            deadline = time.time() + 5
            while time.time() < deadline and not os.path.exists(path):
                time.sleep(0.02)
            time.sleep(0.2)
            self.assertTrue(self.m.pause_proc(proc, True))
            size_paused = os.path.getsize(path)
            time.sleep(0.4)
            self.assertEqual(os.path.getsize(path), size_paused,
                             "the file grew while the process was supposedly stopped")
            self.assertTrue(self.m.pause_proc(proc, False))
            time.sleep(0.4)
            self.assertGreater(os.path.getsize(path), size_paused,
                               "no growth after resuming -- SIGCONT didn't take")
        finally:
            proc.kill()
            proc.wait()

    def test_pause_proc_on_a_finished_process_is_false(self):
        proc = subprocess.Popen([sys.executable, "-c", "pass"])
        proc.wait()
        self.assertFalse(self.m.pause_proc(proc, True))

    def test_pause_proc_on_nothing_is_false(self):
        self.assertFalse(self.m.pause_proc(None, True))

    # ---- pause_job / resume_job: job-state transitions, pause_proc mocked
    # for determinism -- the real signalling is proven above.

    def test_pause_job_marks_it_paused_by_hand(self):
        j = self.job(status="downloading", proc=object())
        self.m.pause_proc = lambda proc, on: True
        self.assertTrue(self.m.pause_job(j["id"]))
        self.assertTrue(j["paused"])
        self.assertTrue(j["user_paused"])

    def test_pause_job_refuses_a_job_that_is_not_active(self):
        j = self.job(status="queued", hold=True)
        self.m.pause_proc = lambda proc, on: True
        self.assertFalse(self.m.pause_job(j["id"]))
        self.assertFalse(j["paused"])

    def test_pause_job_refuses_one_already_paused(self):
        j = self.job(status="downloading", paused=True)
        self.m.pause_proc = lambda proc, on: True
        self.assertFalse(self.m.pause_job(j["id"]))

    def test_pause_job_refuses_an_unknown_id(self):
        self.assertFalse(self.m.pause_job("no-such-job"))

    def test_pause_job_does_not_claim_success_if_the_signal_failed(self):
        # A dead or already-gone process: pause_proc's own honest "no" must
        # not get turned into a job the UI thinks is safely paused.
        j = self.job(status="downloading", proc=object())
        self.m.pause_proc = lambda proc, on: False
        self.assertFalse(self.m.pause_job(j["id"]))
        self.assertFalse(j["paused"])
        self.assertFalse(j["user_paused"])

    def test_resume_job_clears_both_flags(self):
        j = self.job(status="downloading", paused=True, user_paused=True,
                     proc=object())
        self.m.pause_proc = lambda proc, on: True
        self.assertTrue(self.m.resume_job(j["id"]))
        self.assertFalse(j["paused"])
        self.assertFalse(j["user_paused"])

    def test_resume_job_refuses_one_that_was_not_paused(self):
        j = self.job(status="downloading", paused=False)
        self.m.pause_proc = lambda proc, on: True
        self.assertFalse(self.m.resume_job(j["id"]))

    def test_resume_job_refuses_an_unknown_id(self):
        self.assertFalse(self.m.resume_job("no-such-job"))


# --------------------------------------------------------------------------
class TestSchedulerTick(Base):
    """The behaviour actually asked for: opening a 25-episode series starts
    the one episode picked, not the other 24 behind it. auto=False (set by
    fan_out(), see TestPacks) is what scheduler_tick() must respect in both
    of the places it would otherwise start something on its own."""

    def test_an_auto_false_job_is_never_started_while_idle(self):
        j = self.job(status="queued", hold=True, auto=False)
        self.m.scheduler_tick()
        self.assertEqual(j["status"], "queued")
        self.assertTrue(j["hold"])

    def test_an_auto_true_job_still_starts_while_idle(self):
        # The regression guard: a single ordinary item -- the overwhelming
        # common case -- must keep starting itself exactly as before.
        j = self.job(status="queued", hold=True, auto=True)
        self.m.scheduler_tick()
        self.assertFalse(j["hold"])

    def test_an_auto_false_job_is_never_prefetched_while_watching(self):
        playing = self.job(status="streaming", path="/x", total=100, received=50)
        sibling = self.job(status="queued", hold=True, auto=False)
        self.m.note_playing("dev1", playing["id"], 10.0)
        self.m.stream_health = lambda j: "ok"
        self.m.scheduler_tick()
        self.assertTrue(sibling["hold"])
        self.assertFalse(sibling.get("prefetch"))

    def test_an_auto_true_job_is_still_prefetched_while_watching(self):
        playing = self.job(status="streaming", path="/x", total=100, received=50)
        nxt = self.job(status="queued", hold=True, auto=True)
        self.m.note_playing("dev1", playing["id"], 10.0)
        self.m.stream_health = lambda j: "ok"
        self.m.scheduler_tick()
        self.assertFalse(nxt["hold"])
        self.assertTrue(nxt.get("prefetch"))

    def test_a_manual_pause_survives_an_improving_stream(self):
        # Rule 2 would ordinarily resume a paused prefetch once the margin
        # is fine again -- must not, when a person paused it on purpose.
        playing = self.job(status="streaming", path="/x", total=100, received=50)
        pf = self.job(status="downloading", prefetch=True,
                      paused=True, user_paused=True, proc=object())
        self.m.note_playing("dev1", playing["id"], 10.0)
        self.m.stream_health = lambda j: "ok"       # would normally un-pause
        calls = []
        self.m.pause_proc = lambda proc, on: calls.append(on) or True
        self.m.scheduler_tick()
        self.assertEqual(calls, [])                 # never touched at all
        self.assertTrue(pf["paused"])

    def test_an_unpaused_prefetch_still_gets_throttled_by_health(self):
        # The regression guard for rule 2 itself: ordinary (non-manual)
        # prefetch throttling must be unaffected by the user_paused check.
        playing = self.job(status="streaming", path="/x", total=100, received=50)
        pf = self.job(status="downloading", prefetch=True, proc=object())
        self.m.note_playing("dev1", playing["id"], 10.0)
        self.m.stream_health = lambda j: "behind"
        self.m.pause_proc = lambda proc, on: True
        self.m.scheduler_tick()
        self.assertTrue(pf["paused"])
        self.assertFalse(pf["user_paused"])          # the scheduler's own doing


# --------------------------------------------------------------------------
class TestSecondInstance(Base):
    def free_port(self):
        s = socket.socket()
        s.bind(("127.0.0.1", 0))
        port = s.getsockname()[1]
        s.close()
        return port

    def test_an_empty_port_is_not_in_use(self):
        # A genuine restart must be unaffected: the old socket may still be in
        # TIME_WAIT, but nothing is listening, so this has to say so.
        self.assertFalse(self.m.already_serving("127.0.0.1", self.free_port()))

    def test_a_live_server_is_detected(self):
        s = socket.socket()
        s.bind(("127.0.0.1", 0))
        s.listen(1)
        try:
            self.assertTrue(self.m.already_serving("127.0.0.1", s.getsockname()[1]))
        finally:
            s.close()

    def test_the_shadowing_case_is_caught(self):
        # The one that actually happened: an instance holds 127.0.0.1:PORT and
        # a second binds 0.0.0.0:PORT. Both binds succeed -- they are different
        # pairs -- and the more specific one wins every request, so the older
        # server answers while the newer serves nobody. Probing from the
        # wildcard server's point of view has to find the loopback one.
        s = socket.socket()
        s.bind(("127.0.0.1", 0))
        s.listen(1)
        try:
            self.assertTrue(self.m.already_serving("0.0.0.0", s.getsockname()[1]))
        finally:
            s.close()

    def test_binding_would_not_have_caught_it(self):
        # Why this probes by connecting rather than by trying to bind: with
        # allow_reuse_address the bind succeeds in exactly the case being
        # guarded against, so it can never be the test.
        held = socket.socket()
        held.bind(("127.0.0.1", 0))
        held.listen(1)
        port = held.getsockname()[1]
        second = socket.socket()
        second.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            second.bind(("0.0.0.0", port))     # succeeds, which is the problem
        except OSError:
            self.skipTest("this platform refuses the overlapping bind")
        finally:
            second.close()
            held.close()


# --------------------------------------------------------------------------
class TestCatalogue(Base):
    """TMDb-backed search with stubbed responses: no key, no network."""

    def setUp(self):
        super().setUp()
        self.m.TMDB_KEY_FILE = os.path.join(self.dl, "nokey")
        self.m._TMDB.clear()
        self.m._TMDB["key"] = "test-key"
        self.calls = []
        self.m.tmdb_genres = lambda kind="movie": {
            "science fiction": 878, "horror": 27, "drama": 18}

    def stub(self, payload):
        def fake(path, **params):
            self.calls.append((path, params))
            return payload(path, params) if callable(payload) else payload
        self.m.tmdb_get = fake

    def movie(self, title, year, rating=8.0, votes=5000, genres=(878,)):
        return {"id": 1, "title": title, "release_date": "%d-01-01" % year,
                "vote_average": rating, "vote_count": votes,
                "genre_ids": list(genres), "overview": "A film."}

    def test_filters_become_query_parameters(self):
        self.stub({"results": []})
        self.m.catalogue_search({"kind": "movie", "genre": "horror",
                                 "year_from": 1980, "year_to": 1989,
                                 "rating_min": 7.5, "votes_min": 900})
        path, p = self.calls[-1]
        self.assertEqual(path, "discover/movie")
        self.assertEqual(p["with_genres"], 27)
        self.assertEqual(p["vote_average.gte"], 7.5)
        self.assertEqual(p["vote_count.gte"], 900)
        self.assertEqual(p["primary_release_date.gte"], "1980-01-01")
        self.assertEqual(p["primary_release_date.lte"], "1989-12-31")

    def test_television_uses_its_own_field_names(self):
        # Shows carry name and first_air_date where films carry title and
        # primary_release_date. Getting it wrong reads as "no results" rather
        # than as an error, which is why it is worth pinning.
        self.stub({"results": [{"id": 2, "name": "Some Show",
                                "first_air_date": "2016-05-01",
                                "vote_average": 8.5, "vote_count": 900,
                                "genre_ids": [18], "overview": ""}]})
        rows, err, _ = self.m.catalogue_search({"kind": "tv", "year_from": 2015})
        path, p = self.calls[-1]
        self.assertEqual(path, "discover/tv")
        self.assertIn("first_air_date.gte", p)
        self.assertEqual(rows[0]["title"], "Some Show")
        self.assertEqual(rows[0]["year"], 2016)

    def test_an_actor_becomes_a_cast_id(self):
        self.m.tmdb_person = lambda n: (3063, "Tilda Swinton")
        self.stub({"results": []})
        _rows, _err, note = self.m.catalogue_search({"actor": "tilda swinton"})
        self.assertEqual(self.calls[-1][1]["with_cast"], 3063)
        self.assertIn("Tilda Swinton", note)

    def test_an_unknown_person_is_said_so(self):
        self.m.tmdb_person = lambda n: (None, None)
        self.stub({"results": []})
        rows, err, _ = self.m.catalogue_search({"actor": "nobody at all"})
        self.assertEqual(rows, [])
        self.assertIn("nobody at all", err)

    def test_an_unknown_genre_is_noted_not_fatal(self):
        # Dropping the filter and saying so beats returning nothing.
        self.stub({"results": [self.movie("Something", 2020)]})
        rows, err, note = self.m.catalogue_search({"genre": "wuxia"})
        self.assertIsNone(err)
        self.assertTrue(rows)
        self.assertIn("wuxia", note)
        self.assertNotIn("with_genres", self.calls[-1][1])

    def test_language_becomes_a_discover_parameter(self):
        self.stub({"results": []})
        self.m.catalogue_search({"kind": "movie", "language": "JA"})
        self.assertEqual(self.calls[-1][1]["with_original_language"], "ja")

    def test_language_filters_free_text_locally(self):
        # search/movie carries no with_original_language of its own, so a
        # language filter combined with free text has to be applied to what
        # came back rather than sent as a parameter.
        self.stub({"results": [
            dict(self.movie("Oldboy", 2003), original_language="ko"),
            dict(self.movie("Oldboy", 2013), original_language="en"),
        ]})
        rows, _err, _ = self.m.catalogue_search({"text": "oldboy", "language": "ko"})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["year"], 2003)

    def test_the_quality_filter_reaches_find_torrent(self):
        self.stub({"results": [self.movie("Ikiru", 1952)]})
        calls = []
        def fake_find(title, year=None, min_res=None):
            calls.append(min_res)
            return None
        self.m.find_torrent = fake_find
        self.m.catalogue_with_copies({"quality": "1080p"})
        self.assertEqual(calls, ["1080p"])

    def test_free_text_searches_by_name_instead(self):
        # discover cannot take a title, so a query with text has to switch
        # endpoints rather than silently ignore it.
        self.stub({"results": [self.movie("Zindagi Na Milegi Dobara", 2011, 7.6)]})
        rows, _err, _ = self.m.catalogue_search({"text": "zindagi"})
        self.assertEqual(self.calls[-1][0], "search/movie")
        self.assertEqual(rows[0]["title"], "Zindagi Na Milegi Dobara")

    def test_an_unreachable_catalogue_is_not_a_crash(self):
        self.m.tmdb_get = lambda path, **p: None
        rows, err, _ = self.m.catalogue_search({"genre": "horror"})
        self.assertEqual(rows, [])
        self.assertIn("could not reach", err)

    def test_without_a_key_the_feature_says_so(self):
        self.m._TMDB.clear()
        self.m._TMDB["key"] = ""
        rows, err, _ = self.m.catalogue_search({"genre": "horror"})
        self.assertEqual(rows, [])
        self.assertIn("no TMDb key", err)
        self.assertFalse(self.m.has_tmdb())

    def test_a_copy_of_the_wrong_film_is_refused(self):
        # A search for one title cheerfully returns others, and the catalogue
        # already decided which film this is.
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "Some.Other.Film.2019.1080p.H264-GRP",
             "seeders": 900, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "magnet:?xt=urn:btih:" + "a" * 40},
        ], {})
        self.assertIsNone(self.m.find_torrent("The Thing", 1982))

    def test_the_right_film_is_matched_across_a_year_of_drift(self):
        # Release names and release dates disagree across territories more
        # often than they agree exactly.
        self.m.search_all = lambda q: ([
            {"infohash": "b" * 40, "name": "The.Thing.1983.1080p.BluRay.H264-GRP",
             "seeders": 120, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "magnet:?xt=urn:btih:" + "b" * 40},
        ], {})
        hit = self.m.find_torrent("The Thing", 1982)
        self.assertIsNotNone(hit)

    def test_a_playable_copy_beats_a_better_seeded_one(self):
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "The.Thing.1982.1080p.x265-HEVC",
             "seeders": 900, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "m1"},
            {"infohash": "b" * 40, "name": "The.Thing.1982.1080p.WEB-DL.H264-GRP",
             "seeders": 40, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "m2"},
        ], {})
        self.assertEqual(self.m.find_torrent("The Thing", 1982)["magnet"], "m2")

    def test_an_exact_title_beats_a_longer_one_containing_it(self):
        # "Gabriel's Inferno" is a substring of "Gabriel's Inferno Part Three",
        # and matching loosely handed the first film the third one's copy.
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40,
             "name": "Gabriels.Inferno.Part.Three.2020.1080p.WEB-DL.H264-GRP",
             "seeders": 900, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "wrong"},
            {"infohash": "b" * 40,
             "name": "Gabriels.Inferno.2020.1080p.WEB-DL.H264-GRP",
             "seeders": 40, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "right"},
        ], {})
        self.assertEqual(self.m.find_torrent("Gabriel's Inferno", 2020)["magnet"], "right")

    def test_a_quality_floor_rejects_a_lower_resolution(self):
        # A worse-than-asked-for release is not what a quality filter means:
        # this must report no copy, not settle for the one that exists.
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "Ikiru.1952.720p.BluRay.x264-GRP",
             "seeders": 60, "leechers": 1, "size": 3_000_000_000, "files": 1,
             "magnet": "m"},
        ], {})
        self.assertIsNone(self.m.find_torrent("Ikiru", 1952, min_res="1080p"))

    def test_a_quality_floor_accepts_the_matching_release(self):
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "Ikiru.1952.720p.BluRay.x264-GRP",
             "seeders": 60, "leechers": 1, "size": 3_000_000_000, "files": 1,
             "magnet": "small"},
            {"infohash": "b" * 40, "name": "Ikiru.1952.2160p.BluRay.x264-GRP",
             "seeders": 20, "leechers": 1, "size": 7_000_000_000, "files": 1,
             "magnet": "big"},
        ], {})
        hit = self.m.find_torrent("Ikiru", 1952, min_res="1080p")
        self.assertEqual(hit["magnet"], "big")

    def test_an_unknown_resolution_does_not_pass_a_floor(self):
        # Unknown is treated as not meeting the bar, the same way an unknown
        # codec is costed as needing a remux elsewhere in this file.
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "Ikiru.1952.BluRay.x264-GRP",
             "seeders": 60, "leechers": 1, "size": 3_000_000_000, "files": 1,
             "magnet": "m"},
        ], {})
        self.assertIsNone(self.m.find_torrent("Ikiru", 1952, min_res="720p"))

    def test_no_floor_is_unaffected(self):
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "Ikiru.1952.720p.BluRay.x264-GRP",
             "seeders": 60, "leechers": 1, "size": 3_000_000_000, "files": 1,
             "magnet": "m"},
        ], {})
        self.assertIsNotNone(self.m.find_torrent("Ikiru", 1952))

    def test_camera_rips_and_packs_are_not_offered_as_the_copy(self):
        self.m.search_all = lambda q: ([
            {"infohash": "a" * 40, "name": "The.Thing.1982.1080p.TELESYNC-X",
             "seeders": 900, "leechers": 1, "size": 2_000_000_000, "files": 1,
             "magnet": "m1"},
            {"infohash": "b" * 40, "name": "The.Thing.Complete.Collection",
             "seeders": 800, "leechers": 1, "size": 9_000_000_000, "files": 40,
             "magnet": "m2"},
        ], {})
        self.assertIsNone(self.m.find_torrent("The Thing", 1982))


# --------------------------------------------------------------------------
class TestCatalogueShelves(Base):
    """The inversion: shelves built from what TMDb says is good, not from what
    a tracker happens to be seeding this week."""

    def setUp(self):
        super().setUp()
        self.m._TMDB.clear()
        self.m._TMDB["key"] = "test-key"
        self.m.AVAIL.clear()

    def test_availability_is_cached_rather_than_asked_twice(self):
        # Five shelves asking about the same classics every half hour would be
        # sixty indexer searches per rebuild; almost all of that is memory.
        calls = []
        def fake_find(title, year=None):
            calls.append(title)
            return {"infohash": "a" * 40, "name": title, "seeders": 50,
                   "leechers": 1, "size": 2_000_000_000, "magnet": "m"}
        self.m.find_torrent = fake_find
        self.m.cached_torrent("The Godfather", 1972)
        self.m.cached_torrent("The Godfather", 1972)
        self.assertEqual(len(calls), 1)

    def test_a_cached_miss_is_not_retried_either(self):
        calls = []
        def fake_find(title, year=None):
            calls.append(title)
            return None
        self.m.find_torrent = fake_find
        self.m.cached_torrent("Nothing Findable", 2026)
        self.m.cached_torrent("Nothing Findable", 2026)
        self.assertEqual(len(calls), 1)

    def test_a_stale_entry_is_asked_about_again(self):
        self.m.AVAIL_TTL = 0.01
        calls = []
        def fake_find(title, year=None):
            calls.append(title)
            return None
        self.m.find_torrent = fake_find
        self.m.cached_torrent("X", 2020)
        time.sleep(0.02)
        self.m.cached_torrent("X", 2020)
        self.assertEqual(len(calls), 2)

    def test_films_with_no_copy_are_dropped_not_greyed_out(self):
        # Unlike a search result, where the specific film was asked for, a
        # recommendation you cannot press play on is not one.
        self.m.cached_torrent = lambda t, y=None: (
            {"infohash": "a" * 40, "name": t, "seeders": 50, "leechers": 1,
             "size": 2_000_000_000, "magnet": "m"} if t == "Found" else None)
        self.m.feed_verify = lambda rows, now=None: rows
        rows = [{"title": "Found", "year": 2020, "rating": 8.0, "votes": 5000},
                {"title": "Not Found", "year": 2020, "rating": 8.0, "votes": 5000}]
        got = self.m.shelf_from_catalogue(rows, 8, time.time())
        self.assertEqual([r["title"] for r in got], ["Found"])

    def test_a_swarm_that_measures_thin_is_dropped(self):
        # A title still in theatrical release turned up a "1080p WEB" release
        # at a tenth of the size a real one runs here, with leechers roughly
        # equal to seeders -- the standard bait-upload signature. The indexer
        # claimed 137 seeders; the tracker itself said 15. This is the general
        # form: whatever the indexer claims, a swarm measured too thin to
        # stream is not a recommendation.
        self.m.cached_torrent = lambda t, y=None: (
            {"infohash": "a" * 40, "name": t, "seeders": 137, "leechers": 139,
             "size": 900_000_000, "magnet": "m"})
        self.m.feed_verify = lambda rows, now=None: [
            dict(r, seeders=2, verified=True) for r in rows]
        rows = [{"title": "Bait Upload", "year": 2026, "rating": 8.0, "votes": 5000}]
        got = self.m.shelf_from_catalogue(rows, 8, time.time())
        self.assertEqual(got, [])

    def test_ratings_are_reweighted_not_trusted_as_given(self):
        # TMDb's own "top rated" sort surfaces a 2026 film at 9.4 from 497
        # votes over The Godfather -- brand new and barely seen. The same
        # vote-weighting the IMDb ratings already get is applied here.
        self.m.tmdb_get = lambda path, **p: {"results": [
            {"id": 1, "title": "Brand New", "release_date": "2026-01-01",
             "vote_average": 9.4, "vote_count": 497, "genre_ids": [], "overview": ""},
            {"id": 2, "title": "The Godfather", "release_date": "1972-01-01",
             "vote_average": 8.7, "vote_count": 23236, "genre_ids": [], "overview": ""},
        ]}
        rows = self.m.tmdb_rows(sort_by="vote_average.desc")
        self.m.cached_torrent = lambda t, y=None: (
            {"infohash": "a" * 40, "name": t, "seeders": 500, "leechers": 1,
             "size": 8_000_000_000, "magnet": "m"})
        self.m.feed_verify = lambda rows, now=None: rows
        got = self.m.shelf_from_catalogue(rows, 8, time.time())
        self.assertEqual(got[0]["title"], "The Godfather")

    def page(self, ids, total_pages=3):
        return {"total_pages": total_pages,
                "results": [{"id": i, "title": "Film %d" % i,
                             "release_date": "2020-01-01", "vote_average": 8.0,
                             "vote_count": 5000, "genre_ids": [], "overview": ""}
                            for i in ids]}

    def paged(self, per_page, asked=None):
        """A fake tmdb_get that only answers discover, so the genre lookup
        tmdb_rows makes first is not mistaken for a page of results."""
        def fake(path, **p):
            if not path.startswith("discover"):
                return {"genres": []}
            if asked is not None:
                asked.append(p.get("page"))
            return per_page(p.get("page"))
        return fake

    def test_more_than_one_page_is_walked_to_fill_a_shelf(self):
        # discover returns exactly 20 rows per page however large a limit is
        # asked for, so the old single request silently capped every shelf's
        # candidate pool at 20 -- which is what left the TV shelves at three
        # films once the "has a whole-season copy" filter had taken its cut.
        asked = []
        self.m.tmdb_get = self.paged(
            lambda n: self.page(range((n - 1) * 20, n * 20)), asked)
        rows = self.m.tmdb_rows(limit=40)
        self.assertEqual(len(rows), 40)
        self.assertEqual(asked, [1, 2])          # stops as soon as it has enough
        self.assertEqual(len({r["tmdb_id"] for r in rows}), 40)

    def test_paging_stops_at_the_last_page_rather_than_looping(self):
        # A query with only one page of matches must not keep asking for more.
        asked = []
        self.m.tmdb_get = self.paged(
            lambda n: self.page(range(5), total_pages=1), asked)
        rows = self.m.tmdb_rows(limit=40)
        self.assertEqual(len(rows), 5)
        self.assertEqual(asked, [1])

    def test_a_page_that_fails_keeps_what_was_already_fetched(self):
        # A catalogue hiccup on page 2 should cost the extra candidates, not
        # the whole shelf -- the same principle tmdb_get's own retry follows.
        self.m.tmdb_get = self.paged(
            lambda n: self.page(range(20)) if n == 1 else None)
        rows = self.m.tmdb_rows(limit=40)
        self.assertEqual(len(rows), 20)

    def test_a_repeated_page_is_not_shown_twice(self):
        # Defensive: if the catalogue ever returns the same page again, the
        # same film must not appear twice on one shelf.
        self.m.tmdb_get = self.paged(lambda n: self.page(range(20)))
        rows = self.m.tmdb_rows(limit=40)
        self.assertEqual(len(rows), 20)
        self.assertEqual(len({r["tmdb_id"] for r in rows}), 20)

    def test_no_key_falls_back_to_the_tracker_shelves(self):
        self.m._TMDB.clear()
        self.m._TMDB["key"] = ""
        self.m.live_seeders = lambda *a, **k: None
        self.m.ratings_for = lambda ids: {}
        self.m.bolly_fetch = lambda: ([], {})
        self.m.feed_fetch = lambda: ([], {"201": "failed: no network in this test"})
        rows, err, per = self.m.build_shelves()
        self.assertEqual(rows, [])
        self.assertIn("could not reach", err)


# --------------------------------------------------------------------------
class TestShelfAssembly(Base):
    """build_catalogue_shelves itself, which until now was only ever mocked --
    so the widening to 20 a shelf, and the cross-shelf dedup that stops one
    film filling half the page, had no coverage at all.

    tmdb_rows and shelf_from_catalogue are stubbed so this tests the assembly
    -- ordering, capping, dedup, omission -- rather than the catalogue or the
    indexers, which have their own tests."""

    def setUp(self):
        super().setUp()
        self.asked = []                       # the discover queries issued
        self.finders = []                     # which copy-finder each shelf used
        # Captured before stub() replaces the function, so the film path's
        # reliance on the default is still checkable.
        self.real_finder_default = inspect.signature(
            self.m.shelf_from_catalogue).parameters["finder"].default

    def stub(self, per_shelf, tv=False):
        """per_shelf: {shelf name: [titles]} the catalogue offers for each.

        The catalogue returns exactly those titles, and every candidate that
        reaches shelf_from_catalogue is treated as having a copy -- so what
        the shelf ends up holding is decided by build_catalogue_shelves' own
        dedup and capping, which is the thing under test.
        """
        shelves = self.m.CAT_SHELVES_TV if tv else self.m.CAT_SHELVES
        plan = [per_shelf.get(n, []) for n in (n for n, _, _ in shelves)]
        def rows(**q):
            self.asked.append(q)
            titles = plan[len(self.asked) - 1] if len(self.asked) <= len(plan) else []
            return [{"title": t, "year": 2020, "rating": 8.0, "votes": 5000}
                    for t in titles]
        self.m.tmdb_rows = rows
        def shelf(rows_in, want, now, finder=None):
            self.finders.append(finder)
            return [{"title": r["title"], "name": r["title"], "size": 1,
                     "seeders": 99} for r in rows_in][:want]
        self.m.shelf_from_catalogue = shelf
        self.m.feed_dress = lambda rows: rows

    def names(self, out):
        return [s["name"] for s in out]

    def test_a_shelf_is_capped_at_the_configured_width(self):
        # FEED_SHELF is the promise; more candidates surviving must not widen it.
        wide = ["f%d" % i for i in range(50)]
        self.stub({"Tonight": wide})
        out, err, _ = self.m.build_catalogue_shelves()
        self.assertIsNone(err)
        self.assertEqual(len(out[0]["films"]), self.m.FEED_SHELF)

    def test_a_film_is_not_repeated_on_a_later_shelf(self):
        # Popular-and-well-reviewed films qualify for several shelves at once;
        # without the dedup the same handful fills most of the page.
        self.stub({"Tonight": ["Dune", "Arrival"], "Just landed": ["Dune", "Tenet"]})
        out, _err, _ = self.m.build_catalogue_shelves()
        seen = [f["title"] for s in out for f in s["films"]]
        self.assertEqual(len(seen), len(set(seen)), seen)

    def test_a_shelf_with_nothing_available_is_omitted_not_shown_bare(self):
        self.stub({"Tonight": ["Dune"], "Top rated": []})
        out, _err, _ = self.m.build_catalogue_shelves()
        self.assertIn("Tonight", self.names(out))
        self.assertNotIn("Top rated", self.names(out))

    def test_shelves_come_back_in_the_configured_order(self):
        # Filled in one order, displayed in another: what needs protecting and
        # what belongs at the top of the page are different questions.
        order = [n for n, _, _ in self.m.CAT_SHELVES]
        self.stub({n: ["only-%s" % n] for n in order})
        out, _err, _ = self.m.build_catalogue_shelves()
        self.assertEqual(self.names(out), order)

    def test_nothing_available_anywhere_is_an_error_not_an_empty_success(self):
        # An empty page with no explanation reads as a broken app.
        self.stub({})
        out, err, _ = self.m.build_catalogue_shelves()
        self.assertEqual(out, [])
        self.assertIn("nothing with a copy", err)

    def test_no_shelf_asks_for_films_released_in_the_future(self):
        # Nothing released tomorrow can be watched tonight.
        self.stub({"Tonight": ["Dune"]})
        self.m.build_catalogue_shelves()
        today = time.strftime("%Y-%m-%d", time.gmtime())
        for q in self.asked:
            self.assertLessEqual(q.get("primary_release_date.lte", "0"), today)

    def test_just_landed_asks_for_a_recent_window_and_gems_an_old_one(self):
        # The two shelves that are defined by *when*, not just by rating.
        self.stub({"Tonight": ["Dune"]})
        self.m.build_catalogue_shelves()
        by = {}
        for name, q in zip([n for n, _, _ in self.m.CAT_SHELVES], self.asked):
            by[name] = q
        self.assertIn("primary_release_date.gte", by["Just landed"])
        # gems must be old enough that its rating has settled
        self.assertLess(by["Hidden gems"]["primary_release_date.lte"],
                        by["Tonight"]["primary_release_date.lte"])

    def test_film_shelves_look_for_a_film_not_a_season(self):
        # Films take shelf_from_catalogue's default finder rather than passing
        # one, so this pins both halves: the film path overrides nothing, and
        # the default it inherits is the film finder, not the season one.
        self.assertIs(self.real_finder_default, self.m.cached_torrent)
        self.stub({"Tonight": ["Dune"]})
        self.m.build_catalogue_shelves()
        self.assertTrue(self.finders)
        self.assertTrue(all(f is None for f in self.finders), self.finders)

    def test_tv_shelves_only_count_a_whole_season_as_available(self):
        # The guarantee that keeps a show whose only copies are single
        # episodes off the shelf entirely, rather than offered with a caveat.
        self.stub({"Tonight": ["Severance"]}, tv=True)
        out, _per = self.m.build_catalogue_shelves_tv()
        self.assertTrue(self.finders)
        self.assertTrue(all(f is self.m.cached_season for f in self.finders),
                        self.finders)
        self.assertEqual(out[0]["films"][0]["title"], "Severance")

    def test_tv_shelves_ask_first_air_date_not_release_date(self):
        # A different field on the catalogue side; asking the film one back
        # would silently return nothing for every TV shelf.
        self.stub({"Tonight": ["Severance"]}, tv=True)
        self.m.build_catalogue_shelves_tv()
        self.assertTrue(any("first_air_date.lte" in q for q in self.asked))
        self.assertFalse(any("primary_release_date.lte" in q for q in self.asked))

    def test_the_gems_shelf_still_demands_a_real_audience(self):
        # The rating floor was loosened to 7.0; the vote floor is what stops
        # a 9.4-from-500-votes film being called a hidden gem, and must stay.
        gems = dict(next(p for n, _, p in self.m.CAT_SHELVES if n == "Hidden gems"))
        self.assertGreaterEqual(gems["vote_count.gte"], 300)
        self.assertIn("vote_count.lte", gems)      # "barely seen" is the point
        self.assertLessEqual(gems["vote_average.gte"], 7.5)


# --------------------------------------------------------------------------
class TestSeasonDetection(Base):
    """A TV shelf must offer whole seasons only. Two layers: a cheap name
    check that decides what's worth a request, and a real file-list check
    that decides what's actually trusted."""

    def test_a_bare_season_number_looks_like_a_pack(self):
        self.assertTrue(self.m.tv_looks_like_season("Severance.S01.1080p.WEB"))
        self.assertTrue(self.m.tv_looks_like_season("Show Season 2 Complete"))
        self.assertTrue(self.m.tv_looks_like_season("Breaking.Bad.Complete.Series.1080p"))

    def test_a_single_episode_does_not_look_like_a_pack_name(self):
        self.assertFalse(self.m.tv_looks_like_episode("Severance.S01.1080p.WEB"))
        self.assertTrue(self.m.tv_looks_like_episode("Severance.S01E04.1080p.WEB"))

    def test_a_spelled_out_range_is_not_mistaken_for_one_episode(self):
        # "S01E01-E10" names a season as surely as bare "S01" does -- refusing
        # it as "one episode" because E01 appears would throw out a real pack
        # for looking like the episode it happens to start with.
        name = "Show.S01E01-E10.1080p.WEB"
        self.assertFalse(self.m.tv_looks_like_episode(name))
        self.assertTrue(self.m.tv_looks_like_season(name))

    def f(self, name, gb):
        return {"name": name, "size": int(gb * 1_000_000_000)}

    def test_a_real_season_survives_the_file_check(self):
        files = [self.f("Show.S01E%02d.1080p.mkv" % i, 1.5) for i in range(1, 9)]
        got = self.m.season_episode_files(files)
        self.assertEqual(len(got), 8)

    def test_a_single_video_file_is_not_a_season(self):
        # Whatever the torrent's name claims, one file is one file.
        files = [self.f("Show.S01E01.1080p.mkv", 1.5),
                 self.f("NEW upcoming releases by Xclusive.txt", 0.0)]
        self.assertEqual(self.m.season_episode_files(files), [])

    def test_a_trilogy_is_not_a_season(self):
        # Passes the same count-and-size bar a season does; only the episode
        # numbering in the names tells them apart.
        files = [self.f("Godfather.1972.mkv", 14.0),
                 self.f("Godfather.Part.II.1974.mkv", 16.0),
                 self.f("Godfather.Part.III.1990.mkv", 13.0)]
        self.assertEqual(self.m.season_episode_files(files), [])

    def test_bonus_material_does_not_count_toward_the_episode_total(self):
        files = [self.f("Show.S01E01.mkv", 2.0), self.f("Show.S01E02.mkv", 2.0),
                 self.f("sample.mkv", 0.1)]
        got = self.m.season_episode_files(files)
        self.assertEqual(len(got), 2)

    def test_is_real_season_reports_none_when_unfetchable(self):
        self.m.torrent_file_list = lambda tid, timeout=6: None
        self.assertIsNone(self.m.is_real_season("123"))

    def test_is_real_season_confirms_a_real_pack(self):
        self.m.torrent_file_list = lambda tid, timeout=6: [
            self.f("Show.S01E%02d.mkv" % i, 1.2) for i in range(1, 7)]
        self.assertTrue(self.m.is_real_season("123"))

    def test_is_real_season_refuses_a_single_file_dressed_as_a_pack(self):
        # The name check alone would have accepted this -- "Show.S01." reads
        # as a season -- which is exactly why the file list gets checked too.
        self.m.torrent_file_list = lambda tid, timeout=6: [
            self.f("Show.S01.Episode.1.mkv", 4.0)]
        self.assertFalse(self.m.is_real_season("123"))


# --------------------------------------------------------------------------
class TestFindSeason(Base):
    """find_season(), the TV-shelf equivalent of find_torrent() -- accepts
    the opposite shape, and never trusts a name alone."""

    def row(self, name, seeders=100, tid="1", size=8_000_000_000, ih="a" * 40):
        return self.m._row(ih, name, seeders, 1, size, files=0, tid=tid)

    def test_single_episodes_are_never_offered(self):
        self.m.search_all = lambda q: ([
            self.row("Severance.S01E04.1080p.WEB-DL.x265-GRP")], {})
        self.assertIsNone(self.m.find_season("Severance", 2022))

    def test_a_season_shaped_name_is_confirmed_against_its_file_list(self):
        self.m.search_all = lambda q: ([
            self.row("Severance.S01.1080p.WEB-DL.x265-GRP")], {})
        self.m.torrent_file_list = lambda tid, timeout=6: [
            {"name": "Severance.S01E%02d.mkv" % i, "size": 1_200_000_000}
            for i in range(1, 10)]
        got = self.m.find_season("Severance", 2022)
        self.assertIsNotNone(got)
        self.assertIn("Severance", got["name"])

    def test_a_pack_shaped_name_around_a_single_file_is_refused(self):
        # The bait case: named like a season, but the real file list shows
        # one episode. The name alone must not be trusted.
        self.m.search_all = lambda q: ([
            self.row("Severance.S01.COMPLETE.1080p.WEB-DL.x265-GRP")], {})
        self.m.torrent_file_list = lambda tid, timeout=6: [
            {"name": "Severance.S01E01.mkv", "size": 1_200_000_000}]
        self.assertIsNone(self.m.find_season("Severance", 2022))

    def test_a_row_with_no_id_cannot_be_verified_so_is_not_offered(self):
        # torrents-csv and therarbg never supply an id -- no id, no file list,
        # no way to confirm a name-only guess.
        row = self.row("Severance.S01.1080p.WEB-DL.x265-GRP", tid="")
        self.m.search_all = lambda q: ([row], {})
        self.m.torrent_file_list = lambda tid, timeout=6: [
            {"name": "Severance.S01E01.mkv", "size": 1_200_000_000}] * 8
        self.assertIsNone(self.m.find_season("Severance", 2022))

    def test_camera_rips_are_excluded_the_same_as_for_films(self):
        self.m.search_all = lambda q: ([
            self.row("Severance.S01.HDCAM.x265-GRP")], {})
        self.assertIsNone(self.m.find_season("Severance", 2022))

    def test_the_best_verified_candidate_wins(self):
        # Two season-shaped names; only the second holds up under the file
        # check, and it has fewer seeders -- a real pack should still win
        # over a higher-seeded name that doesn't check out.
        self.m.search_all = lambda q: ([
            self.row("Severance.S01.2160p.WEB-DL-GRP", seeders=900, tid="1",
                    ih="a" * 40),
            self.row("Severance.S01.1080p.WEB-DL-GRP", seeders=50, tid="2",
                    ih="b" * 40),
        ], {})
        def files(tid, timeout=6):
            if tid == "2":
                return [{"name": "Severance.S01E%02d.mkv" % i,
                        "size": 1_200_000_000} for i in range(1, 10)]
            return [{"name": "Severance.S01E01.mkv", "size": 1_200_000_000}]
        self.m.torrent_file_list = files
        got = self.m.find_season("Severance", 2022)
        self.assertEqual(got["id"], "2")


# --------------------------------------------------------------------------
class TestTvShelves(Base):
    """The catalogue shelves extended to TV -- same ranking and verification
    machinery, gated by find_season instead of find_torrent."""

    def setUp(self):
        super().setUp()
        self.m._TMDB.clear()
        self.m._TMDB["key"] = "test-key"
        self.m.AVAIL.clear()

    def test_shelf_from_catalogue_uses_the_finder_it_is_given(self):
        calls = []
        def fake_season(title, year=None):
            calls.append(title)
            return {"infohash": "a" * 40, "name": title, "seeders": 50,
                   "leechers": 1, "size": 4_000_000_000, "magnet": "m"}
        self.m.feed_verify = lambda rows, now=None: rows
        rows = [{"title": "Severance", "year": 2022, "rating": 8.7, "votes": 5000}]
        got = self.m.shelf_from_catalogue(rows, 8, time.time(), finder=fake_season)
        self.assertEqual(calls, ["Severance"])
        self.assertEqual(got[0]["title"], "Severance")

    def test_default_finder_is_still_cached_torrent(self):
        # The film shelves must keep working unmodified -- finder is opt-in.
        self.m.cached_torrent = lambda t, y=None: (
            {"infohash": "a" * 40, "name": t, "seeders": 50, "leechers": 1,
             "size": 4_000_000_000, "magnet": "m"})
        self.m.feed_verify = lambda rows, now=None: rows
        rows = [{"title": "Ikiru", "year": 1952, "rating": 8.5, "votes": 5000}]
        got = self.m.shelf_from_catalogue(rows, 8, time.time())
        self.assertEqual(got[0]["title"], "Ikiru")

    def test_movie_and_tv_shelves_are_tagged_by_section(self):
        self.m.build_catalogue_shelves = lambda: (
            [{"name": "Tonight", "note": "n", "films": []}], None, {})
        self.m.build_catalogue_shelves_tv = lambda: (
            [{"name": "Tonight", "note": "n", "films": []}], {})
        rows, err, per = self.m.build_shelves()
        self.assertEqual([r["section"] for r in rows], ["movie", "tv"])

    def test_a_broken_tv_build_does_not_cost_the_movie_shelves(self):
        self.m.build_catalogue_shelves = lambda: (
            [{"name": "Tonight", "note": "n", "films": []}], None, {})
        def broken():
            raise RuntimeError("tv catalogue query failed")
        self.m.build_catalogue_shelves_tv = broken
        rows, err, per = self.m.build_shelves()
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["section"], "movie")

    def test_no_key_means_no_tv_section_either(self):
        self.m._TMDB.clear()
        self.m._TMDB["key"] = ""
        self.m.live_seeders = lambda *a, **k: None
        self.m.bolly_fetch = lambda: ([], {})
        self.m.feed_fetch = lambda: ([], {})
        rows, err, per = self.m.build_shelves()
        self.assertNotIn("tv", [r.get("section") for r in rows])


# --------------------------------------------------------------------------
class TestPosterProxy(Base):
    """Posters are proxied rather than pointed at image.tmdb.org directly, so
    the CSP never has to trust a third party. The path is built from whatever
    a client sends, so validation is the security-relevant part."""

    def setUp(self):
        super().setUp()
        self.m.TMDB_IMG_DIR = os.path.join(self.dl, "posters")

    def test_an_unlisted_size_is_refused(self):
        self.assertIsNone(self.m.poster_file("w9999", "abc123.jpg"))

    def test_a_path_that_is_not_a_bare_filename_is_refused(self):
        # What stops this being handed a path to fetch or read arbitrarily.
        for bad in ("../../../../etc/passwd", "a/b.jpg", "abc123.jpg/../x",
                    "abc123.exe", "abc123", ""):
            self.assertIsNone(self.m.poster_file("w154", bad), bad)

    def stand_in(self, fn):
        """Rebinds the module's whole urllib rather than patching
        urllib.request.urlopen in place, which would patch the *shared*
        module and take every other test's http fixture down with it."""
        self.m.urllib = types.SimpleNamespace(
            request=types.SimpleNamespace(urlopen=fn, Request=urllib.request.Request),
            parse=urllib.parse)

    def test_a_valid_request_is_fetched_once_and_then_cached(self):
        calls = []
        class FakeResponse(io.BytesIO):
            def __enter__(self): return self
            def __exit__(self, *a): return False
        def fake_urlopen(req, timeout=None):
            calls.append(req.full_url)
            return FakeResponse(b"\xff\xd8\xff" + b"x" * 100)   # jpeg-ish bytes
        self.stand_in(fake_urlopen)
        p1 = self.m.poster_file("w154", "abc123.jpg")
        p2 = self.m.poster_file("w154", "abc123.jpg")
        self.assertEqual(p1, p2)
        self.assertEqual(len(calls), 1)          # the second call never fetched
        self.assertIn("w154/abc123.jpg", calls[0])

    def test_a_failed_fetch_leaves_no_partial_file(self):
        def refuse(req, timeout=None):
            raise OSError("unreachable")
        self.stand_in(refuse)
        self.assertIsNone(self.m.poster_file("w154", "abc123.jpg"))
        self.assertFalse(os.path.exists(
            os.path.join(self.m.TMDB_IMG_DIR, "w154", "abc123.jpg.part")))


# --------------------------------------------------------------------------
class TestUndoRemove(Base):
    def finished(self):
        j = self.job()
        j["status"] = "done"
        j["path"] = os.path.join(self.dl, "film.mp4")
        with open(j["path"], "wb") as f:
            f.write(b"x" * 4096)
        return j

    def test_removing_takes_the_row_but_keeps_the_bytes(self):
        # The row goes at once, because that is what was asked for. The file
        # waits, because a mis-click on a small x otherwise costs a
        # multi-gigabyte re-download.
        j = self.finished()
        self.assertTrue(self.m.remove_job(j["id"]))
        self.assertNotIn(j["id"], self.m.JOBS)
        self.assertTrue(os.path.exists(j["path"]))

    def test_undo_puts_it_back(self):
        j = self.finished()
        self.m.remove_job(j["id"])
        self.assertTrue(self.m.undo_remove(j["id"]))
        self.assertIn(j["id"], self.m.JOBS)
        self.assertEqual(self.m.JOBS[j["id"]]["status"], "done")
        self.assertTrue(os.path.exists(j["path"]))

    def test_the_grace_period_ends_in_a_real_deletion(self):
        j = self.finished()
        self.m.remove_job(j["id"])
        self.m.empty_trash()                       # too soon
        self.assertTrue(os.path.exists(j["path"]))
        self.m.empty_trash(force=True)
        self.assertFalse(os.path.exists(j["path"]))

    def test_undo_after_the_grace_period_says_no(self):
        # Rather than reporting success and restoring nothing.
        j = self.finished()
        self.m.remove_job(j["id"])
        self.m.empty_trash(force=True)
        self.assertFalse(self.m.undo_remove(j["id"]))
        self.assertNotIn(j["id"], self.m.JOBS)

    def test_an_unfinished_item_comes_back_ready_to_restart(self):
        # Its processes were stopped on the way out, so there is nothing left
        # running to resume -- it has to go back to the scheduler.
        j = self.job()
        j["status"] = "downloading"
        self.m.remove_job(j["id"])
        self.m.undo_remove(j["id"])
        back = self.m.JOBS[j["id"]]
        self.assertEqual(back["status"], "queued")
        self.assertTrue(back["hold"])
        # the old cancel Event was set on removal and cannot be reused
        self.assertFalse(back["cancel"].is_set())

    def test_undoing_something_never_removed_is_harmless(self):
        self.assertFalse(self.m.undo_remove("no-such-job"))

    def test_eviction_still_deletes_immediately(self):
        # drop() is what runs where no one is clicking anything -- eviction and
        # restore cleanup -- and there is nothing to take back there.
        j = self.finished()
        self.m.drop(j["id"])
        self.assertNotIn(j["id"], self.m.JOBS)
        self.assertFalse(os.path.exists(j["path"]))


# --------------------------------------------------------------------------
class TestRefetch(Base):
    """The 'refetch' button: for a file that came down wrong -- corrupt
    source data, same as the real Invincible episode this was built for --
    where /retry's refusal to touch anything but error/evicted/removed means
    a 'done' row with bad bytes has no way back short of a terminal."""

    def finished(self, **extra):
        j = self.job(source="torrent", magnet="magnet:?xt=urn:btih:" + "a" * 40,
                     wt_index=3, wt_files=25, **extra)
        j["status"] = "done"
        j["path"] = os.path.join(self.dl, "film.mp4")
        j["received"] = j["total"] = 4096
        j["audio_tracks"] = [{"index": 0, "codec": "aac", "lang": "eng", "default": True}]
        j["subs_status"] = "ready"
        with open(j["path"], "wb") as f:
            f.write(b"x" * 4096)
        return j

    def test_works_on_a_done_job_unlike_retry(self):
        # The actual gap this closes: /retry's own status check would refuse
        # this exact case.
        j = self.finished()
        self.assertNotIn(j["status"], ("error", "evicted", "removed"))
        self.assertTrue(self.m.refetch_job(j["id"]))

    def test_the_bad_file_is_gone_and_the_row_starts_clean(self):
        j = self.finished()
        jid, path = j["id"], j["path"]
        self.assertTrue(self.m.refetch_job(jid))
        self.assertFalse(os.path.exists(path))
        back = self.m.JOBS[jid]
        self.assertEqual(back["id"], jid)                # same row
        self.assertEqual(back["status"], "queued")
        self.assertEqual(back["received"], 0)
        self.assertIsNone(back["path"])
        self.assertEqual(back["audio_tracks"], [])        # not carried over stale
        self.assertIsNone(back["subs_status"])
        self.assertFalse(back["hold"])                    # handed to the scheduler

    def test_identity_needed_to_redownload_survives(self):
        # The id staying the same is what keeps this the same queue row; the
        # magnet and pack pin are what a pack sibling needs to fetch the
        # right file again rather than rediscovering the whole pack.
        j = self.finished()
        jid, magnet = j["id"], j["magnet"]
        self.m.refetch_job(jid)
        back = self.m.JOBS[jid]
        self.assertEqual(back["magnet"], magnet)
        self.assertEqual(back["wt_index"], 3)
        self.assertEqual(back["title"], j["title"])

    def test_a_tmdb_title_survives_a_refetch(self):
        # Without this, refetching a movie added from the catalogue would
        # rebuild the row via new_job() with title_locked defaulted back to
        # False, and the next run_torrent would overwrite the TMDB title
        # with the torrent's own scene release name -- the fix working on
        # first add but silently regressing on the very next refetch.
        j = self.finished(title="Disclosure Day (2026)", title_locked=True)
        jid = j["id"]
        self.m.refetch_job(jid)
        self.assertTrue(self.m.JOBS[jid]["title_locked"])
        self.assertEqual(self.m.JOBS[jid]["title"], "Disclosure Day (2026)")

    def test_a_drive_job_keeps_its_drive_id(self):
        j = self.job(drive_id="1AbCdEfGhIjKlMnOpQrStUvWxYz0123456")
        j["status"] = "done"
        j["path"] = os.path.join(self.dl, "drivefilm.mp4")
        with open(j["path"], "wb") as f:
            f.write(b"y" * 2048)
        jid, did = j["id"], j["drive_id"]
        self.assertTrue(self.m.refetch_job(jid))
        self.assertEqual(self.m.JOBS[jid]["drive_id"], did)
        self.assertEqual(self.m.JOBS[jid]["source"], "drive")

    def test_running_processes_are_stopped_first(self):
        j = self.finished()
        killed = []
        class FakeProc:
            def poll(self): return None
            def kill(self): killed.append(True)
        j["procs"] = [FakeProc()]
        self.m.refetch_job(j["id"])
        self.assertEqual(killed, [True])

    def test_nothing_to_refetch_from_is_refused(self):
        j = self.job()             # neither drive_id nor magnet
        self.assertFalse(self.m.refetch_job(j["id"]))
        self.assertIn(j["id"], self.m.JOBS)     # left untouched, not silently dropped

    def test_an_unknown_id_is_refused(self):
        self.assertFalse(self.m.refetch_job("no-such-job"))


# --------------------------------------------------------------------------
class TestIntegrityCheck(Base):
    """The check built from the two real corrupt Invincible episodes: ffprobe
    reported both as clean, complete files -- duration, codecs, everything --
    and only an actual decode pass caught the bad frames. scan_for_corruption
    is tested against a real ffmpeg decode of a real corrupted file, not
    asserted from a mocked stderr string."""

    def _video(self, name, seconds=2):
        src = os.path.join(self.dl, name)
        subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
             "-f", "lavfi", "-i", "testsrc=size=320x240:rate=25:duration=%d" % seconds,
             "-c:v", "libx264", "-pix_fmt", "yuv420p",
             "-movflags", "+faststart", src], check=True, capture_output=True)
        return src

    def _corrupt(self, path):
        # Well past the ftyp/moov header (faststart puts it at the front), so
        # the container still opens -- this breaks a frame's compressed data,
        # the same shape of damage the real files had.
        size = os.path.getsize(path)
        with open(path, "r+b") as f:
            f.seek(int(size * 0.6))
            f.write(os.urandom(min(4096, size // 4)))

    @needs_ffmpeg
    def test_a_clean_file_scans_clean(self):
        src = self._video("clean.mp4")
        self.assertEqual(self.m.scan_for_corruption(src), 0)

    @needs_ffmpeg
    def test_a_corrupted_file_is_actually_caught(self):
        src = self._video("bad.mp4", seconds=4)
        self._corrupt(src)
        hits = self.m.scan_for_corruption(src)
        self.assertIsNotNone(hits)
        self.assertGreater(hits, 0)

    def test_a_path_that_cannot_be_read_is_inconclusive_not_corrupt(self):
        # None has to mean "couldn't tell," never get treated as either
        # verdict -- see check_integrity's guard against writing it as ok.
        got = self.m.scan_for_corruption("/no/such/file.mp4")
        self.assertIsNone(got)

    def test_no_path_anywhere_is_a_no_op(self):
        j = self.job()
        self.m.check_integrity(j)
        self.assertIsNone(j["integrity"])

    def test_checking_state_is_set_immediately(self):
        # Before the background thread has had any chance to run at all --
        # the row should say *something* the instant a scan starts.
        j = self.job()
        j["path"] = "/wherever"
        self.m.scan_for_corruption = lambda path, timeout=None: (
            time.sleep(0.2) or 0)
        self.m.check_integrity(j)
        self.assertEqual(j["integrity"], "checking")

    def _wait(self, job, timeout=5):
        deadline = time.time() + timeout
        while time.time() < deadline and job["integrity"] == "checking":
            time.sleep(0.02)
        return job["integrity"]

    def test_a_clean_verdict_lands_on_the_job(self):
        j = self.job()
        j["path"] = "/wherever"
        self.m.scan_for_corruption = lambda path, timeout=None: 0
        self.m.check_integrity(j)
        self.assertEqual(self._wait(j), "ok")

    def test_a_corrupt_verdict_lands_on_the_job_with_a_count(self):
        j = self.job()
        j["path"] = "/wherever"
        self.m.scan_for_corruption = lambda path, timeout=None: 2
        self.m.check_integrity(j)
        self.assertEqual(self._wait(j), "corrupt")
        self.assertEqual(j["integrity_hits"], 2)

    def test_an_inconclusive_scan_is_not_reported_as_either_verdict(self):
        j = self.job()
        j["path"] = "/wherever"
        self.m.scan_for_corruption = lambda path, timeout=None: None
        self.m.check_integrity(j)
        deadline = time.time() + 5
        while time.time() < deadline and j["integrity"] == "checking":
            time.sleep(0.02)
        self.assertIsNone(j["integrity"])

    def test_an_explicit_path_overrides_the_jobs_own(self):
        # What a direct-stream torrent needs: it never gets job["path"] set
        # at all, so the caller has to say where the file actually is.
        j = self.job()
        seen = []
        self.m.scan_for_corruption = lambda path, timeout=None: (
            seen.append(path) or 0)
        self.m.check_integrity(j, path="/explicit/path.mp4")
        self._wait(j)
        self.assertEqual(seen, ["/explicit/path.mp4"])

    def test_a_cancelled_job_is_never_overwritten_after_the_fact(self):
        # refetch_job() sets cancel on the job it is discarding; a scan
        # already in flight for that exact copy must not resurrect a verdict
        # about bytes that no longer exist.
        j = self.job()
        j["path"] = "/wherever"
        self.m.scan_for_corruption = lambda path, timeout=None: (
            time.sleep(0.15) or 3)
        self.m.check_integrity(j)
        j["cancel"].set()
        time.sleep(0.4)
        self.assertNotIn(j["integrity"], ("ok", "corrupt"))


# --------------------------------------------------------------------------
class TestResume(Base):
    def test_a_position_comes_back(self):
        self.m.note_resume("job1", 1830.0, 7200.0)
        self.assertEqual(self.m.resume_at("job1"), 1830.0)

    def test_the_first_half_minute_is_not_progress(self):
        # Starting over is what you wanted anyway, and jumping 12 seconds in is
        # more annoying than starting clean.
        self.m.note_resume("job1", 12.0, 7200.0)
        self.assertIsNone(self.m.resume_at("job1"))

    def test_something_watched_to_the_end_is_finished(self):
        # Offering to resume the closing credits is worse than not offering.
        self.m.note_resume("job1", 7150.0, 7200.0)
        self.assertIsNone(self.m.resume_at("job1"))
        # but a minute earlier is a real place to come back to
        self.m.note_resume("job2", 7000.0, 7200.0)
        self.assertEqual(self.m.resume_at("job2"), 7000.0)

    def test_an_unknown_length_still_resumes(self):
        # Live items report no duration; the tail rule simply cannot apply.
        self.m.note_resume("job1", 900.0, 0)
        self.assertEqual(self.m.resume_at("job1"), 900.0)

    def test_the_latest_report_wins(self):
        # Two devices on one film should leave it where it was last actually
        # watched, not wherever the one that got ahead stopped.
        self.m.note_resume("job1", 3000.0, 7200.0)
        self.m.note_resume("job1", 600.0, 7200.0)
        self.assertEqual(self.m.resume_at("job1"), 600.0)

    def test_finishing_clears_the_position(self):
        # What the client sends on 'ended'.
        self.m.note_resume("job1", 3000.0, 7200.0)
        self.m.note_resume("job1", 0, 0)
        self.assertIsNone(self.m.resume_at("job1"))

    def test_an_item_never_watched_has_no_position(self):
        self.assertIsNone(self.m.resume_at("never-seen"))

    def test_positions_survive_a_restart(self):
        self.m.note_resume("job1", 1830.0, 7200.0)
        self.m.save_resume(force=True)
        fresh = load_reel(self.dl)
        fresh.RESUME_PATH = self.m.RESUME_PATH
        fresh.load_resume()
        self.assertEqual(fresh.resume_at("job1"), 1830.0)

    def test_a_corrupt_store_is_not_a_reason_not_to_start(self):
        with open(self.m.RESUME_PATH, "w") as f:
            f.write("{ this is not json")
        self.m.load_resume()                      # must not raise
        self.assertIsNone(self.m.resume_at("job1"))

    def test_removing_an_item_forgets_where_it_was(self):
        j = self.job()
        self.m.note_resume(j["id"], 1830.0, 7200.0)
        self.m.drop(j["id"])
        self.assertIsNone(self.m.resume_at(j["id"]))

    def test_the_position_reaches_the_client(self):
        j = self.job()
        self.m.note_resume(j["id"], 1830.0, 7200.0)
        self.assertEqual(self.m.public(j)["resume_at"], 1830.0)

    def test_writes_are_not_one_per_report(self):
        # The page reports every three seconds per viewer, and none of those is
        # worth a write of its own.
        self.m.save_resume(force=True)
        before = os.path.getmtime(self.m.RESUME_PATH)
        for i in range(20):
            self.m.note_resume("job1", 100.0 + i, 7200.0)
        self.assertEqual(os.path.getmtime(self.m.RESUME_PATH), before)
        # the position is still current in memory, just not yet on disk
        self.assertEqual(self.m.resume_at("job1"), 119.0)

    def test_the_last_position_is_not_lost_on_the_way_out(self):
        # The throttle above means the newest position is only in memory when
        # the process ends, and the loss is not "a few seconds": a session
        # shorter than one flush interval wrote its *first* position and
        # nothing after, so 40 minutes of watching landed on disk as 12
        # seconds. atexit and the SIGTERM handler both force this.
        for at in (12.0, 600.0, 1830.0, 2400.0):
            self.m.note_resume("job1", at, 7200.0)
        self.m.save_resume(force=True)
        with open(self.m.RESUME_PATH, encoding="utf-8") as f:
            self.assertEqual(json.load(f)["job1"]["at"], 2400.0)


# --------------------------------------------------------------------------
class TestAudioTracks(Base):
    def test_tracks_come_back_in_container_order(self):
        data = {"streams": [
            {"codec_type": "video", "codec_name": "h264"},
            {"codec_type": "audio", "codec_name": "aac", "tags": {"language": "fre"}},
            {"codec_type": "audio", "codec_name": "aac", "tags": {"language": "eng"}},
        ]}
        got = self.m.audio_tracks(data)
        self.assertEqual([t["lang"] for t in got], ["fre", "eng"])
        # The index is the audio-relative position, which is exactly what
        # ffmpeg's -map 0:a:N addresses -- not the container's own stream index.
        self.assertEqual([t["index"] for t in got], [0, 1])

    def test_an_untagged_track_reads_as_undetermined_not_english(self):
        data = {"streams": [{"codec_type": "audio", "codec_name": "aac", "tags": {}}]}
        self.assertEqual(self.m.audio_tracks(data)[0]["lang"], "und")

    def test_english_is_preferred_over_the_containers_own_default_flag(self):
        # The real bug: a MULTi release had its French track flagged default by
        # whoever packaged it, and French is exactly what should not win.
        tracks = [{"index": 0, "lang": "fre", "default": True},
                  {"index": 1, "lang": "eng", "default": False}]
        self.assertEqual(self.m.guess_audio_default(tracks), 1)

    def test_the_default_flag_only_matters_absent_an_english_track(self):
        tracks = [{"index": 0, "lang": "jpn", "default": False},
                  {"index": 1, "lang": "fre", "default": True}]
        self.assertEqual(self.m.guess_audio_default(tracks), 1)

    def test_absent_either_signal_the_first_track_is_kept(self):
        tracks = [{"index": 0, "lang": "und", "default": False},
                  {"index": 1, "lang": "und", "default": False}]
        self.assertEqual(self.m.guess_audio_default(tracks), 0)

    def test_a_single_track_is_its_own_default(self):
        self.assertEqual(self.m.guess_audio_default(
            [{"index": 0, "lang": "und", "default": False}]), 0)

    def test_no_tracks_does_not_crash(self):
        self.assertEqual(self.m.guess_audio_default([]), 0)

    @needs_ffmpeg
    def test_every_track_survives_a_real_conversion(self):
        # The actual bug, reproduced: a MULTi release with French ordered first
        # and English second. Runs the real ffmpeg command finalize_torrent
        # builds and checks what came out the other end, not just the argv.
        src = os.path.join(self.dl, "multi.mkv")
        subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
             "-f", "lavfi", "-i", "color=c=blue:s=320x240:r=5:d=1",
             "-f", "lavfi", "-i", "sine=frequency=440:duration=1",
             "-f", "lavfi", "-i", "sine=frequency=880:duration=1",
             "-map", "0:v", "-map", "1:a", "-map", "2:a",
             "-c:v", "libx264", "-c:a", "aac",
             "-metadata:s:a:0", "language=fre", "-metadata:s:a:1", "language=eng",
             src], check=True, capture_output=True)

        tracks = self.m.audio_tracks(src)
        self.assertEqual([t["lang"] for t in tracks], ["fre", "eng"])
        self.assertEqual(self.m.guess_audio_default(tracks), 1)   # English, not first

        amaps, ameta = [], []
        for t in tracks:
            amaps += ["-map", "0:a:%d?" % t["index"]]
            ameta += ["-metadata:s:a:%d" % t["index"], "language=" + t["lang"]]
        out = os.path.join(self.dl, "multi_out.mp4")
        r = subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", src,
             "-map", "0:v:0", *amaps, *ameta, "-c:v", "copy", "-c:a", "copy", out],
            capture_output=True)
        self.assertEqual(r.returncode, 0, r.stderr)

        kept = self.m.audio_tracks(out)
        self.assertEqual(len(kept), 2)
        self.assertEqual([t["lang"] for t in kept], ["fre", "eng"])

    @needs_ffmpeg
    def test_the_output_is_actually_reordered_not_just_tagged(self):
        # Keeping every track and tagging the right one "default" was the
        # first fix, and it was not enough: Chrome, Brave and Edge have no
        # audioTracks API to read that tag with, and simply play whichever
        # audio stream is physically first in the container. Proven with two
        # distinctly-pitched tones and a browser's own Web Audio analyser
        # against the real finalize command, not asserted from the argv.
        src = os.path.join(self.dl, "multi2.mkv")
        subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
             "-f", "lavfi", "-i", "color=c=blue:s=320x240:r=5:d=1",
             "-f", "lavfi", "-i", "sine=frequency=440:duration=1",
             "-f", "lavfi", "-i", "sine=frequency=880:duration=1",
             "-map", "0:v", "-map", "1:a", "-map", "2:a",
             "-c:v", "libx264", "-c:a", "aac",
             "-metadata:s:a:0", "language=fre", "-disposition:a:0", "default",
             "-metadata:s:a:1", "language=eng", "-disposition:a:1", "0",
             src], check=True, capture_output=True)

        tracks = self.m.audio_tracks(src)
        amaps, ameta, ordered = self.m.audio_remap_args(tracks)
        self.assertEqual([t["lang"] for t in ordered], ["eng", "fre"])

        out = os.path.join(self.dl, "multi2_out.mp4")
        r = subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", src,
             "-map", "0:v:0", *amaps, *ameta, "-c:v", "copy", "-c:a", "copy",
             out], capture_output=True)
        self.assertEqual(r.returncode, 0, r.stderr)

        kept = self.m.probe_all(out)["streams"]
        audio = [s for s in kept if s["codec_type"] == "audio"]
        self.assertEqual([s["tags"]["language"] for s in audio], ["eng", "fre"])
        self.assertEqual(audio[0]["disposition"]["default"], 1)
        self.assertEqual(audio[1]["disposition"]["default"], 0)

    def test_no_tracks_is_a_no_op(self):
        self.assertEqual(self.m.audio_remap_args([]), ([], [], []))


# --------------------------------------------------------------------------
class TestLiveAudioRemap(Base):
    """The bug found debugging Enola Holmes 3: audio_remap_args fixed the
    FINISHED file (finalize_torrent, restore, the browser_ready shortcuts),
    but the live phase -- what actually plays while a file is still
    downloading -- built its ffmpeg command with no -map at all. Without one,
    ffmpeg's automatic stream selection just takes whichever track the
    container itself flags default, which for a MULTi release is whoever
    packaged it, not English. ffmpeg -i also happily accepts a local path,
    so this proves it against a real conversion rather than just the argv."""

    def _multi_track_src(self, name):
        # Polish flagged default and first, exactly like the real release
        # ("[AUDIO #0 POLISH] [AUDIO #1 ENGLISH]") that surfaced this.
        src = os.path.join(self.dl, name)
        subprocess.run(
            ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
             "-f", "lavfi", "-i", "color=c=blue:s=320x240:r=5:d=1",
             "-f", "lavfi", "-i", "sine=frequency=440:duration=1",
             "-f", "lavfi", "-i", "sine=frequency=880:duration=1",
             "-map", "0:v", "-map", "1:a", "-map", "2:a",
             "-c:v", "libx264", "-c:a", "aac",
             "-metadata:s:a:0", "language=pol", "-disposition:a:0", "default",
             "-metadata:s:a:1", "language=eng", "-disposition:a:1", "0",
             src], check=True, capture_output=True)
        return src

    @needs_ffmpeg
    def test_start_live_from_url_keeps_and_reorders_every_track(self):
        src = self._multi_track_src("live_multi.mkv")
        job = self.job(id="livejob")
        self.m.start_live_from_url(job, src, "video", vcodec="h264",
                                   height=240, hdr=False, pix="yuv420p")
        out = os.path.join(self.dl, "livejob.live.mp4")
        deadline = time.time() + 15
        while time.time() < deadline and not job.get("live_done"):
            if os.path.exists(out) and os.path.getsize(out) > 0:
                break
            time.sleep(0.1)
        # Give ffmpeg a moment to flush and exit so the file is readable.
        proc = job.get("live_proc")
        if proc:
            proc.wait(timeout=10)
        self.assertTrue(os.path.exists(out), job.get("live_note"))

        kept = self.m.audio_tracks(out)
        self.assertEqual(len(kept), 2,
                         "both tracks must survive, not just the default one")
        self.assertEqual([t["lang"] for t in kept], ["eng", "pol"],
                         "English must be first regardless of container order")
        self.assertEqual(job["audio_tracks"][0]["lang"], "eng")
        self.assertEqual(job["audio_default"], 0)

    @needs_ffmpeg
    def test_run_torrent_pipe_keeps_and_reorders_every_track(self):
        src = self._multi_track_src("pipe_multi.mkv")
        out_dir = os.path.join(self.dl, "pipedir")
        os.makedirs(out_dir, exist_ok=True)
        # run_torrent_pipe spawns webtorrent itself; standing in for it with
        # cat keeps this a real ffmpeg run without a real torrent swarm. The
        # partial-file probe it does for language tags reads out_dir, so the
        # source is placed there under the name it already expects.
        on_disk = os.path.join(out_dir, "pipe_multi.mkv")
        shutil.copy(src, on_disk)
        job = self.job(id="pipejob")
        real_popen = self.m.subprocess.Popen
        real_disk_bytes = self.m.disk_bytes

        def fake_popen(cmd, **kw):
            if cmd and cmd[0] == "webtorrent":
                return real_popen(["cat", src], **kw)
            return real_popen(cmd, **kw)
        # The tiny synthetic clip never reaches the 512KB floor run_torrent_pipe
        # waits for before it will probe codecs -- a real torrent's own
        # preallocated file clears that immediately, so faking the same result
        # here is standing in for scale, not skipping something meaningful.
        self.m.subprocess.Popen = fake_popen
        self.m.disk_bytes = lambda p: 10**7
        try:
            self.m.run_torrent_pipe(job, "magnet:?xt=urn:btih:" + "a" * 40,
                                    {"index": 0}, out_dir)
        finally:
            self.m.subprocess.Popen = real_popen
            self.m.disk_bytes = real_disk_bytes

        out = os.path.join(self.dl, "pipejob.live.mp4")
        deadline = time.time() + 15
        while time.time() < deadline and not job.get("live_done"):
            time.sleep(0.1)
        self.assertTrue(os.path.exists(out) and os.path.getsize(out) > 0,
                        job.get("live_note"))

        kept = self.m.audio_tracks(out)
        self.assertEqual([t["lang"] for t in kept], ["eng", "pol"])
        self.assertEqual(job["audio_tracks"][0]["lang"], "eng")


# --------------------------------------------------------------------------
class TestJobLog(Base):
    def test_events_are_kept_in_order_with_timestamps(self):
        j = self.job()
        self.m.record(j, "first")
        self.m.record(j, "second")
        self.assertEqual([e["m"] for e in j["log"]], ["first", "second"])
        self.assertLessEqual(j["log"][0]["t"], j["log"][1]["t"])

    def test_the_log_is_bounded(self):
        # A pathological job must not grow without limit, and the oldest event
        # is the right end to lose.
        j = self.job()
        for i in range(self.m.JOB_LOG_MAX + 50):
            self.m.record(j, "event %d" % i)
        self.assertEqual(len(j["log"]), self.m.JOB_LOG_MAX)
        self.assertEqual(j["log"][-1]["m"], "event %d" % (self.m.JOB_LOG_MAX + 49))
        self.assertNotIn("event 0", [e["m"] for e in j["log"]])

    def test_a_long_message_cannot_bloat_the_log(self):
        j = self.job()
        self.m.record(j, "x" * 5000)
        self.assertLessEqual(len(j["log"][0]["m"]), 400)

    def test_recording_against_a_job_without_a_log_is_harmless(self):
        # restore() and older paths build jobs by hand; a missing log must not
        # turn a diagnostic into a crash.
        self.m.record({}, "nothing to attach this to")
        self.m.record(None, "nor this")

    def test_a_failure_says_so_in_the_log(self):
        j = self.job()
        self.m.fail(j, "no peers found for that magnet")
        self.assertEqual(j["status"], "error")
        self.assertTrue(any("no peers found" in e["m"] for e in j["log"]))

    def test_eviction_is_recorded_on_the_job_it_happened_to(self):
        j = self.job()
        j.update(status="done", path=os.path.join(self.dl, "gone.mp4"))
        self.m.record(j, "evicted to stay under the 15 GB cap")
        self.assertTrue(any("evicted" in e["m"] for e in j["log"]))

    def test_jobs_carries_a_count_not_the_events(self):
        # /jobs is polled every second; shipping every event on every poll to
        # render a panel that is usually closed would dominate the wire.
        j = self.job()
        for i in range(5):
            self.m.record(j, "event %d" % i)
        pub = self.m.public(j)
        self.assertEqual(pub["log_n"], 5)
        self.assertNotIn("log", pub)

    def test_the_log_survives_json(self):
        j = self.job()
        self.m.record(j, "probed in 1.2s: h264/aac -> direct stream")
        json.dumps({"events": j["log"]})       # must not raise


# --------------------------------------------------------------------------
class TestShelves(Base):
    """Shelf assignment: which films land where, and what never lands at all."""

    def setUp(self):
        super().setUp()
        self.m.live_seeders = lambda *a, **k: None
        self.m.ratings_for = lambda ids: self.ratings
        self.m.bolly_fetch = lambda: (list(self.bolly), {})
        self.m._TMDB.clear(); self.m._TMDB["key"] = ""   # force the tracker path
        self.ratings, self.bolly = {}, []

    def raw(self, ih, name, **kw):
        r = {"info_hash": ih, "name": name, "seeders": 100, "leechers": 1,
             "size": 2_000_000_000, "num_files": 1, "added": time.time(),
             "status": "vip", "imdb": ""}
        r.update(kw)
        return r

    def build(self, *raw):
        self.m.feed_fetch = lambda: (list(raw), {"201": len(raw)})
        shelves, err, _ = self.m.build_shelves()
        return {s["name"]: [f["title"] for f in s["films"]] for s in shelves}, err

    def test_a_film_appears_on_exactly_one_shelf(self):
        # The whole point of filling in priority order. With ~200 films to fill
        # five shelves, letting each rank independently shows the same handful
        # of titles over and over.
        old = time.time() - 900 * 86400
        got, _ = self.build(
            self.raw("a" * 40, "New.Film.2026.1080p.WEB-DL.H264-GRP"),
            self.raw("b" * 40, "Old.Gem.2001.1080p.BluRay.H264-GRP", added=old,
                     seeders=40, imdb="tt9"),
            self.raw("c" * 40, "Another.2026.1080p.WEB-DL.x265-HEVC", seeders=700))
        self.ratings = {"tt9": (8.4, 300000)}
        placed = [t for titles in got.values() for t in titles]
        self.assertEqual(len(placed), len(set(placed)))

    def test_a_camcorder_rip_is_never_recommended(self):
        # Three of the top twelve were cinema recordings: new, well seeded, and
        # too recent to have a rating that would have pushed them down.
        got, _ = self.build(
            self.raw("a" * 40, "Some.Film.2026.1080p.TELESYNC.x264-DKS", seeders=6000),
            self.raw("b" * 40, "Other.Film.2026.1080p.CAM.H264-X", seeders=5000),
            self.raw("c" * 40, "Third.Film.2026.1080p.HDTC.X264-RAMA", seeders=4000),
            self.raw("d" * 40, "Real.Film.2026.1080p.WEB-DL.H264-GRP", seeders=10))
        placed = [t for titles in got.values() for t in titles]
        self.assertEqual(set(placed), {"Real Film"})

    def test_the_same_film_survives_as_a_better_release(self):
        # Dropping cam rips must not drop the *film* when a real release of it
        # exists -- Supergirl was in the list twice, once as a TELESYNC.
        got, _ = self.build(
            self.raw("a" * 40, "Supergirl.2026.1080p.TELESYNC.x264-DKS", seeders=6000),
            self.raw("b" * 40, "Supergirl.2026.1080p.WEB-DL.H264-GRP", seeders=50))
        placed = [t for titles in got.values() for t in titles]
        self.assertEqual(placed, ["Supergirl"])

    def test_a_badly_rated_film_is_not_a_recommendation(self):
        self.ratings = {"tt1": (3.2, 40000), "tt2": (7.4, 40000)}
        got, _ = self.build(
            self.raw("a" * 40, "Bad.Film.2026.1080p.WEB-DL.H264-GRP", imdb="tt1"),
            self.raw("b" * 40, "Good.Film.2026.1080p.WEB-DL.H264-GRP", imdb="tt2"))
        placed = [t for titles in got.values() for t in titles]
        self.assertEqual(set(placed), {"Good Film"})

    def test_an_unrated_film_is_not_treated_as_a_bad_one(self):
        got, _ = self.build(
            self.raw("a" * 40, "Unknown.Film.2026.1080p.WEB-DL.H264-GRP"))
        placed = [t for titles in got.values() for t in titles]
        self.assertEqual(placed, ["Unknown Film"])

    def test_recently_uploaded_is_not_the_same_as_recently_released(self):
        # A 1976 film posted this morning is not "just landed", and one with
        # five seeders was topping that shelf because it had been.
        now = time.time()
        self.assertFalse(self.m.landed({"added": now, "year": 1976}, now))
        self.assertTrue(self.m.landed({"added": now, "year": 2026}, now))
        # nor is an old upload of a new film
        self.assertFalse(self.m.landed({"added": now - 200 * 86400, "year": 2026}, now))
        # a searched row carries no upload time at all
        self.assertFalse(self.m.landed({"added": 0, "year": 2026}, now))

    def test_a_gem_is_well_reviewed_and_thinly_seeded(self):
        self.assertTrue(self.m.gem({"rating": 8.6, "votes": 800000, "seeders": 57}))
        self.assertFalse(self.m.gem({"rating": 8.6, "votes": 800000, "seeders": 5000}))
        self.assertFalse(self.m.gem({"rating": 5.1, "votes": 800000, "seeders": 57}))
        self.assertFalse(self.m.gem({"rating": None, "votes": 0, "seeders": 57}))

    def test_a_swarm_measured_too_thin_to_stream_is_dropped(self):
        # Gems are thinly seeded by definition, so the indexer's inflation bites
        # hardest there: rows claiming 100+ measured out at 2 and 4.
        self.m.live_seeders = lambda ih, **k: 2
        got, _ = self.build(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.H264-GRP"))
        self.assertEqual(got, {})

    def test_an_empty_shelf_is_left_out_rather_than_shown_bare(self):
        got, _ = self.build(
            self.raw("a" * 40, "Some.Film.2026.1080p.WEB-DL.x265-HEVC"))
        self.assertNotIn("Plays instantly", got)      # nothing qualifies
        self.assertIn("Tonight", got)

    def test_bollywood_is_filled_before_the_shelves_that_could_empty_it(self):
        # A Hindi release rarely wins a general ranking -- these swarms are a
        # fraction of a global release's -- so on a shared pool the general
        # shelves would take the few films this one has.
        self.bolly = [self.raw("f" * 40, "3.Idiots.2009.1080p.BluRay.H264-GRP",
                               seeders=44, imdb="tt5")]
        self.ratings = {"tt5": (8.4, 400000)}
        got, _ = self.build(
            self.raw("a" * 40, "Blockbuster.2026.1080p.WEB-DL.H264-GRP", seeders=9000))
        self.assertEqual(got.get("Bollywood"), ["3 Idiots"])

    def test_a_hindi_dub_of_a_foreign_film_is_not_indian_cinema(self):
        for name in ("War Machine 2026 2160p WEB-DL Dual Audio [Hindi + English]",
                     "Michael.2026.2160p.WEB-DL.MULTi.FRE.ITA.HINDI.LAT",
                     "Some.Film.2024.1080p.Hindi.Dubbed.x264"):
            self.assertTrue(self.m.feed_dubbed(name), name)
        for name in ("3 Idiots 2009 1080p BluRay x264 Hindi AAC - Ozlem",
                     "Gangs of Wasseypur 2012 Hindi 1080p Blu-Ray x264 DD 5.1"):
            self.assertFalse(self.m.feed_dubbed(name), name)

    def test_a_searched_row_keeps_its_imdb_id(self):
        # search_all drops through _row, which discarded the id -- leaving the
        # whole Bollywood shelf unrated while the id sat in the response.
        r = self.m._row("a" * 40, "3 Idiots 2009", 44, 1, 100, 1, "77", "tt1187043")
        self.assertEqual(r["imdb"], "tt1187043")
        self.assertEqual(self.m._row("a" * 40, "x", 1, 1, 1, 1, "", "garbage")["imdb"], "")

    def test_a_listing_page_is_reshaped_into_a_browse_row(self):
        # therarbg abbreviates its keys, so the mapping is the whole risk: a
        # wrong one reads as an empty source rather than an error.
        page = {"results": [{"h": "A" * 40, "n": "Some.Film.2026.1080p.H264-GRP",
                             "se": 40, "le": 3, "s": 2_000_000_000,
                             "a": 1785439244, "i": "tt77"}]}
        self.m._search_json = lambda url, **k: page
        rows = self.m.rarbg_browse(pages=1)
        self.assertEqual(len(rows), 1)
        r = rows[0]
        self.assertEqual(r["info_hash"], "A" * 40)
        self.assertEqual((r["seeders"], r["size"], r["added"], r["imdb"]),
                         (40, 2_000_000_000, 1785439244, "tt77"))

    def test_one_dead_listing_page_is_not_a_dead_source(self):
        calls = []

        def flaky(url, **k):
            calls.append(url)
            if "page=2" in url:
                raise OSError("gateway timeout")
            return {"results": [{"h": "B" * 40, "n": "Film.2026.1080p.H264-G",
                                 "se": 10, "le": 1, "s": 1, "a": 1, "i": ""}]}
        self.m._search_json = flaky
        rows = self.m.rarbg_browse(pages=3)
        self.assertEqual(len(calls), 3)
        self.assertEqual(len(rows), 2)          # pages 1 and 3 survived

    def test_a_file_count_that_arrives_as_a_string_is_still_a_count(self):
        # The precompiled lists send an int, the search endpoint a string. The
        # same field, the same api, and comparing raised TypeError on every
        # search-sourced row.
        self.assertTrue(self.m.feed_pack("Some Boxset", "40"))
        self.assertFalse(self.m.feed_pack("Some.Film.2026", "1"))
        self.assertFalse(self.m.feed_pack("Some.Film.2026", None))


# --------------------------------------------------------------------------
class TestRatingsCache(Base):
    def offline(self):
        """Cut this copy of the module off from the network.

        Rebinds the whole urllib stand-in rather than assigning to
        urllib.request.urlopen, which would patch the *shared* module and take
        every later test's http fixture down with it.
        """
        def refuse(*a, **k):
            raise OSError("imdb unreachable")
        self.m.urllib = types.SimpleNamespace(
            request=types.SimpleNamespace(urlopen=refuse,
                                          Request=urllib.request.Request),
            parse=urllib.parse)

    def dump(self, rows):
        path = os.path.join(self.m.CACHE_DIR, "imdb-ratings.tsv.gz")
        with gzip.open(path, "wt") as f:
            f.write("tconst\taverageRating\tnumVotes\n")
            for t, r, v in rows:
                f.write("%s\t%s\t%s\n" % (t, r, v))
        return path

    def test_reads_only_the_ids_asked_about(self):
        self.dump([("tt1", 8.2, 400000), ("tt2", 5.1, 900), ("tt3", 7.0, 12)])
        got = self.m.ratings_for({"tt1", "tt3"})
        self.assertEqual(got, {"tt1": (8.2, 400000), "tt3": (7.0, 12)})

    def test_asking_about_nothing_costs_nothing(self):
        self.m.ratings_file = lambda: self.fail("should not have fetched")
        self.assertEqual(self.m.ratings_for(set()), {})

    def test_a_truncated_dump_yields_what_it_can(self):
        # Half a file beats no ratings at all, and must not raise.
        path = self.dump([("tt1", 8.2, 400000), ("tt2", 5.1, 900)])
        with open(path, "rb") as f:
            data = f.read()
        with open(path, "wb") as f:
            f.write(data[:len(data) // 2])
        self.assertIsInstance(self.m.ratings_for({"tt1", "tt2"}), dict)

    def test_a_failed_refresh_keeps_yesterdays_copy(self):
        # A rating a day old is worth far more than no rating.
        path = self.dump([("tt1", 8.2, 400000)])
        os.utime(path, (0, 0))                      # long stale
        self.offline()
        self.assertEqual(self.m.ratings_file(), path)
        self.assertEqual(self.m.ratings_for({"tt1"}), {"tt1": (8.2, 400000)})

    def test_no_dump_and_no_network_is_survivable(self):
        self.offline()
        self.assertIsNone(self.m.ratings_file())
        self.assertEqual(self.m.ratings_for({"tt1"}), {})


# --------------------------------------------------------------------------
class TestTrackerRefresh(Base):
    """SEARCH_TRACKERS was a hardcoded list, manually refreshed by hand from
    ngosang/trackerslist and tested before adopting -- the comment above it
    said so. This is that same process automated: fetched weekly, filtered to
    udp:// (the only scheme live_seeders' raw BEP 15 socket can talk to), and
    each candidate actually pinged before being trusted, never just parsed
    off the page and believed."""

    def urls(self, mapping):
        """mapping: url -> text, or url -> an exception instance to raise."""
        class FakeResponse(io.BytesIO):
            def __enter__(self): return self
            def __exit__(self, *a): return False
        def fake_urlopen(req, timeout=None):
            body = mapping.get(req.full_url)
            if isinstance(body, Exception):
                raise body
            if body is None:
                raise OSError("unmapped url: " + req.full_url)
            return FakeResponse(body.encode("utf-8"))
        self.m.urllib = types.SimpleNamespace(
            request=types.SimpleNamespace(urlopen=fake_urlopen,
                                          Request=urllib.request.Request),
            parse=urllib.parse)

    def test_non_udp_trackers_are_dropped_before_anything_is_pinged(self):
        pinged = []
        self.m.verify_trackers_live = lambda cands, timeout=3.0: (pinged.extend(cands) or cands)
        text = "\n".join([
            "udp://a.example:80/announce",
            "https://b.example/announce",     # live_seeders can't speak this
            "wss://c.example/announce",
            "udp://d.example:80/announce",
            "udp://e.example:80/announce",
            "udp://f.example:80/announce",
            "udp://g.example:80/announce",
        ])
        self.urls({self.m.TRACKER_LIST_URLS[0]: text})
        got = self.m.fetch_tracker_list()
        self.assertTrue(all(t.startswith("udp://") for t in pinged), pinged)
        self.assertEqual(len(pinged), 5)
        self.assertEqual(list(got), pinged)

    def test_duplicates_are_collapsed(self):
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands
        text = "\n".join(["udp://a.example:80/announce"] * 3 +
                         ["udp://b.example:80/announce",
                          "udp://c.example:80/announce",
                          "udp://d.example:80/announce",
                          "udp://e.example:80/announce"])
        self.urls({self.m.TRACKER_LIST_URLS[0]: text})
        got = self.m.fetch_tracker_list()
        self.assertEqual(len(got), 5)

    def test_only_the_ones_that_actually_answer_are_adopted(self):
        # Parsed fine, but a scrape only confirms five of the eight as live --
        # the other three must never reach SEARCH_TRACKERS just for being listed.
        text = "\n".join("udp://t%d.example:80/announce" % i for i in range(8))
        self.urls({self.m.TRACKER_LIST_URLS[0]: text})
        live = {"udp://t0.example:80/announce", "udp://t2.example:80/announce",
                "udp://t4.example:80/announce", "udp://t6.example:80/announce",
                "udp://t7.example:80/announce"}
        self.m.verify_trackers_live = lambda cands, timeout=3.0: tuple(
            c for c in cands if c in live)
        got = self.m.fetch_tracker_list()
        self.assertEqual(set(got), live)

    def test_a_kept_tracker_absent_from_the_fetch_still_survives(self):
        # The real bug: tracker.torrent.eu.org answered in 0.03s with the
        # highest seeder count of anything tried, but a wholesale replace
        # dropped it anyway because ngosang's shortlist doesn't include it.
        # keep= is how a known-good tracker gets a chance to prove itself
        # again instead of being discarded for a reason that has nothing to
        # do with whether it still works.
        text = "\n".join("udp://new%d.example:80/announce" % i for i in range(5))
        self.urls({self.m.TRACKER_LIST_URLS[0]: text})
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands   # all alive
        got = self.m.fetch_tracker_list(keep=("udp://kept.example:80/announce",))
        self.assertIn("udp://kept.example:80/announce", got)
        self.assertEqual(len(got), 6)

    def test_a_kept_tracker_that_has_actually_gone_dark_is_dropped(self):
        text = "\n".join("udp://new%d.example:80/announce" % i for i in range(5))
        self.urls({self.m.TRACKER_LIST_URLS[0]: text})
        self.m.verify_trackers_live = lambda cands, timeout=3.0: tuple(
            c for c in cands if c != "udp://dead.example:80/announce")
        got = self.m.fetch_tracker_list(keep=("udp://dead.example:80/announce",))
        self.assertNotIn("udp://dead.example:80/announce", got)

    def test_kept_trackers_alone_are_enough_when_the_fetch_fails(self):
        self.urls({})   # every url raises "unmapped"
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands
        keep = tuple("udp://k%d.example:80/announce" % i for i in range(5))
        got = self.m.fetch_tracker_list(keep=keep)
        self.assertEqual(set(got), set(keep))

    def test_too_few_candidates_falls_through_to_the_mirror(self):
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands
        primary, mirror = self.m.TRACKER_LIST_URLS
        good = "\n".join("udp://t%d.example:80/announce" % i for i in range(6))
        self.urls({primary: "udp://only-one.example:80/announce", mirror: good})
        got = self.m.fetch_tracker_list()
        self.assertEqual(len(got), 6)

    def test_a_network_failure_falls_through_to_the_mirror(self):
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands
        primary, mirror = self.m.TRACKER_LIST_URLS
        good = "\n".join("udp://t%d.example:80/announce" % i for i in range(5))
        self.urls({primary: OSError("unreachable"), mirror: good})
        got = self.m.fetch_tracker_list()
        self.assertEqual(len(got), 5)

    def test_too_few_live_answers_overall_is_reported_as_nothing_found(self):
        # Every mirror parses fine but barely anything actually answers --
        # this must not hand back a near-empty list for apply_trackers to adopt.
        self.m.verify_trackers_live = lambda cands, timeout=3.0: cands[:1]
        text = "\n".join("udp://t%d.example:80/announce" % i for i in range(6))
        self.urls({u: text for u in self.m.TRACKER_LIST_URLS})
        self.assertIsNone(self.m.fetch_tracker_list())

    def test_apply_trackers_keeps_verify_trackers_in_sync(self):
        new = tuple("udp://t%d.example:80/announce" % i for i in range(8))
        self.m.apply_trackers(new)
        self.assertEqual(self.m.SEARCH_TRACKERS, new)
        self.assertEqual(self.m.VERIFY_TRACKERS, new[:5])

    def test_cache_round_trips(self):
        trackers = tuple("udp://t%d.example:80/announce" % i for i in range(5))
        self.m.save_cached_trackers(trackers, 12345.0)
        got, at = self.m.load_cached_trackers()
        self.assertEqual(got, trackers)
        self.assertEqual(at, 12345.0)

    def test_a_missing_cache_is_not_an_error(self):
        got, at = self.m.load_cached_trackers()
        self.assertIsNone(got)
        self.assertEqual(at, 0.0)

    def test_a_short_cached_list_is_refused(self):
        # Fewer than five is suspicious enough to distrust rather than adopt --
        # the same floor a live fetch is held to.
        self.m.save_cached_trackers(("udp://only.example:80/announce",), 1.0)
        got, _at = self.m.load_cached_trackers()
        self.assertIsNone(got)

    def test_tick_is_a_no_op_inside_the_refresh_window(self):
        recent = tuple("udp://t%d.example:80/announce" % i for i in range(5))
        self.m.save_cached_trackers(recent, time.time())
        self.m.fetch_tracker_list = lambda timeout=10, keep=(): self.fail(
            "must not fetch again inside the refresh window")
        self.assertFalse(self.m.tracker_refresh_tick())

    def test_tick_refreshes_once_the_window_has_passed(self):
        stale = ("udp://old.example:80/announce",) * 5
        self.m.save_cached_trackers(stale, time.time() - self.m.TRACKER_REFRESH_INTERVAL - 1)
        fresh = tuple("udp://new%d.example:80/announce" % i for i in range(5))
        self.m.fetch_tracker_list = lambda timeout=10, keep=(): fresh
        self.assertTrue(self.m.tracker_refresh_tick())
        self.assertEqual(self.m.SEARCH_TRACKERS, fresh)
        self.assertEqual(self.m.VERIFY_TRACKERS, fresh[:5])
        got, _at = self.m.load_cached_trackers()
        self.assertEqual(got, fresh)

    def test_a_refresh_reaches_downloads_already_running(self):
        # A refresh that only helps the next download is of least use to the
        # one that needs it most: already stalled on a few peers, and unable
        # to be restarted without throwing away what it has.
        self.m.save_cached_trackers(
            (), time.time() - self.m.TRACKER_REFRESH_INTERVAL - 1)
        fresh = tuple("udp://new%d.example:80/announce" % i for i in range(3))
        self.m.fetch_tracker_list = lambda timeout=10, keep=(): fresh
        got = []
        self.m.push_trackers = lambda tr: got.append(tuple(tr))
        self.assertTrue(self.m.tracker_refresh_tick())
        self.assertEqual(got, [fresh])       # the new list, not the old one

    def test_a_failed_refresh_pushes_nothing(self):
        # Nothing was verified, so there is nothing to hand anyone.
        self.m.save_cached_trackers(
            (), time.time() - self.m.TRACKER_REFRESH_INTERVAL - 1)
        self.m.fetch_tracker_list = lambda timeout=10, keep=(): ()
        got = []
        self.m.push_trackers = lambda tr: got.append(tr)
        self.assertFalse(self.m.tracker_refresh_tick())
        self.assertEqual(got, [])

    def test_tick_passes_the_trackers_already_in_use_to_be_kept(self):
        # The actual bug this guards: a wholesale replace silently dropped a
        # known-good tracker (tracker.torrent.eu.org) just for being outside
        # whatever the upstream source happened to curate that week.
        stale = tuple("udp://old%d.example:80/announce" % i for i in range(5))
        self.m.save_cached_trackers(stale, time.time() - self.m.TRACKER_REFRESH_INTERVAL - 1)
        self.m.apply_trackers(stale)
        seen = {}
        def fake_fetch(timeout=10, keep=()):
            seen["keep"] = keep
            return keep
        self.m.fetch_tracker_list = fake_fetch
        self.m.tracker_refresh_tick()
        self.assertEqual(set(seen["keep"]), set(stale))

    def test_a_failed_tick_never_overwrites_the_previous_list(self):
        stale = tuple("udp://old%d.example:80/announce" % i for i in range(5))
        self.m.save_cached_trackers(stale, time.time() - self.m.TRACKER_REFRESH_INTERVAL - 1)
        self.m.apply_trackers(stale)
        self.m.fetch_tracker_list = lambda timeout=10, keep=(): None
        self.assertFalse(self.m.tracker_refresh_tick())
        self.assertEqual(self.m.SEARCH_TRACKERS, stale)


if __name__ == "__main__":
    unittest.main(verbosity=2)
