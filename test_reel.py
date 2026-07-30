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
import json
import os
import shutil
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
        # Each is an ordinary torrent job the scheduler will start in turn.
        for s in sibs:
            self.assertEqual(s["magnet"], parent["magnet"])
            self.assertEqual(s["status"], "queued")
            self.assertTrue(s["hold"])

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


if __name__ == "__main__":
    unittest.main(verbosity=2)
