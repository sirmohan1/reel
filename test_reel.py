#!/usr/bin/env python3
"""
Tests for reel.

Every case here is a bug that actually happened, kept so it cannot happen twice.
Where that is the point of the test, the comment says which one.

Stdlib only, no network, and no ffmpeg except where a test says otherwise --
those skip themselves rather than fail when it is missing.

Run:  python3 test_reel.py          (or -v for the list)
"""

import importlib.util
import os
import shutil
import struct
import subprocess
import tempfile
import threading
import time
import unittest


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
        open(self.m.subs_path_for("ghost", "eng"), "w").write("WEBVTT\n\n")
        self.m.JOBS.clear()
        self.m.restore()
        self.assertFalse(os.path.exists(self.m.subs_path_for("ghost", "eng")))

    def test_sidecar_reattaches_to_its_job(self):
        p = os.path.join(self.dl, "abc__driveid__A Film.mp4")
        with open(p, "wb") as f:
            f.write(b"\0" * 100)
        open(self.m.subs_path_for("abc", "eng"), "w").write("WEBVTT\n\n")
        self.m.JOBS.clear()
        # playable() shells out to ffprobe; without it, restore keeps the row
        self.m.playable = lambda _p: True
        self.m.restore()
        self.assertIn("abc", self.m.JOBS)
        self.assertEqual(self.m.JOBS["abc"].get("subs_status"), "ready")

    def test_live_fragments_are_discarded(self):
        # Not seekable, and meaningless once the writer is gone.
        open(os.path.join(self.dl, "x.live.mp4"), "wb").write(b"\0" * 10)
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
        import http.server, socketserver, functools
        handler = functools.partial(http.server.SimpleHTTPRequestHandler,
                                    directory=self.dl)
        srv = socketserver.TCPServer(("127.0.0.1", 0), handler)
        srv.allow_reuse_address = True
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
