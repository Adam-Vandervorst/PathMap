import pathlib
import re
import unittest
from unittest.mock import patch

from differential import ConvexInputs, RandomInputs
from input_format import HEADER_SIZE, NOPS, WIRE_MAGIC, input_header, versioned_input
import shrink


class InputFormatTests(unittest.TestCase):
    def test_generation_count_matches_rust(self):
        harness = pathlib.Path(__file__).resolve().parents[1] / "differential/src/harness.rs"
        count = re.search(r"pub const NOPS: usize = (\d+);", harness.read_text())
        self.assertIsNotNone(count)
        self.assertEqual(NOPS, int(count[1]))

    def test_random_inputs_always_have_current_header(self):
        source = RandomInputs(7, 10, 300)
        for i in range(len(source)):
            blob = source.get(i)
            self.assertTrue(blob.startswith(input_header()))
            self.assertEqual(blob, source.get(i))

    def test_random_baseline_encoding_keeps_identical_payload(self):
        current, baseline = RandomInputs(7, 20, 300), RandomInputs(7, 20, 300, selectors=61)
        for i in range(len(current)):
            self.assertEqual(baseline.get(i)[:HEADER_SIZE], input_header(61))
            self.assertEqual(current.get(i)[HEADER_SIZE:], baseline.get(i)[HEADER_SIZE:])

    def test_convex_programs_are_deterministic_and_cover_every_kernel(self):
        source = ConvexInputs(7, 128)
        for i in range(len(source)):
            blob = source.get(i)
            self.assertEqual(blob, source.get(i))
            self.assertTrue(blob.startswith(input_header()))
            # Decode the generated subset to verify instruction boundaries:
            # matching opcode bytes inside a path or payload would be vacuous.
            pos = HEADER_SIZE

            def skip_path():
                nonlocal pos
                length = blob[pos]
                self.assertLess(length, 6)
                pos += length + 1

            for _ in range(2):
                count = blob[pos]
                self.assertLess(count, 8)
                pos += 1
                for _ in range(count):
                    skip_path()
                    pos += 1
            skip_path()
            skip_path()
            ops = []
            while pos < len(blob):
                op = blob[pos]
                pos += 1
                ops.append(op)
                if op in (0, 18):
                    pos += 1  # target
                    skip_path()
                elif op == 60:
                    skip_path()
                    pos += 1  # value
                else:
                    self.assertIn(op, (29, 61, 62, 63, 64))
            self.assertEqual(pos, len(blob))
            self.assertLessEqual(len(ops), 256)
            for op in range(61, 65):
                self.assertEqual(ops.count(op), 2)
        self.assertNotEqual(source.get(7), ConvexInputs(8, 128).get(7))

    def test_legacy_inputs_get_applicable_count(self):
        for payload in [b"", b"\x00\x00\x00\x00\x38", b"x" + WIRE_MAGIC]:
            self.assertEqual(versioned_input(payload), input_header(56) + payload)

    def test_versioned_inputs_keep_recorded_count(self):
        for count in [1, 56, 57, 58, 61, 65, 256]:
            blob = input_header(count) + bytes(range(256))
            self.assertEqual(versioned_input(blob), blob)

    def test_invalid_headers_are_rejected(self):
        for blob in [WIRE_MAGIC, WIRE_MAGIC + b"\x39",
                     WIRE_MAGIC + b"\x00\x00", WIRE_MAGIC + b"\x01\x01"]:
            with self.assertRaises(ValueError):
                versioned_input(blob)

    def test_shrinking_preserves_format_and_operation_count(self):
        for original in [b"\xff\x38", input_header() + b"\xff\x38",
                         input_header(58) + b"\xff\x38"]:
            expected_header = versioned_input(original)[:HEADER_SIZE]

            def signature(blob):
                self.assertEqual(blob[:HEADER_SIZE], expected_header)
                return "DIFF remove_subtrie" if blob[HEADER_SIZE:].endswith(b"\x38") else None

            with patch.object(shrink, "signature", signature), patch("builtins.print"):
                small, sig = shrink.shrink(original)
            self.assertEqual(small, expected_header + b"\x38")
            self.assertEqual(sig, "DIFF remove_subtrie")


class PrunedInputFormatTests(unittest.TestCase):
    """The pruned harness's header: same layout, its own marker and table."""

    def test_pruned_count_matches_rust(self):
        from input_format import PRUNED_LEGACY_NOPS, PRUNED_NOPS
        pruned = pathlib.Path(__file__).resolve().parents[1] / "differential/src/pruned.rs"
        text = pruned.read_text()
        self.assertEqual(PRUNED_NOPS, int(re.search(r"pub const NOPS: usize = (\d+);", text)[1]))
        self.assertEqual(PRUNED_LEGACY_NOPS,
                         int(re.search(r"pub const LEGACY_NOPS: usize = (\d+);", text)[1]))

    def test_pruned_driver_generates_and_saves_pruned_headers(self):
        import pruned_differential  # noqa: F401 -- installs the pruned format
        import differential as D
        from input_format import PRUNED_MAGIC, pruned_input_header
        try:
            source = D.RandomInputs(7, 5, 300)
            for i in range(len(source)):
                self.assertTrue(source.get(i).startswith(pruned_input_header()))
            self.assertEqual(D.versioned_input(b"\x01\x02"), pruned_input_header() + b"\x01\x02")
            blob = PRUNED_MAGIC + (7).to_bytes(2, "little") + b"\x09"
            self.assertEqual(D.versioned_input(blob), blob)
        finally:
            # Other tests in this process use the main harness's format.
            import importlib
            importlib.reload(D)


if __name__ == "__main__":
    unittest.main()
