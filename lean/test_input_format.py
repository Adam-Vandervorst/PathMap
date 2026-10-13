import pathlib
import re
import unittest
from unittest.mock import patch

from differential import RandomInputs
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

    def test_legacy_inputs_get_applicable_count(self):
        for payload in [b"", b"\x00\x00\x00\x00\x38", b"x" + WIRE_MAGIC]:
            self.assertEqual(versioned_input(payload), input_header(56) + payload)

    def test_versioned_inputs_keep_recorded_count(self):
        for count in [1, 56, 57, 58, 256]:
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


if __name__ == "__main__":
    unittest.main()
