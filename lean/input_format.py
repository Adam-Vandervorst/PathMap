"""Versioned fuzzer inputs shared by the Python generators and shrinker."""

WIRE_MAGIC = b"PMFUZZ\x01\x00"
LEGACY_NOPS = 56
# Keep in sync with NOPS in differential/src/harness.rs.
NOPS = 60
HEADER_SIZE = len(WIRE_MAGIC) + 2


def input_header(count=NOPS):
    if not 1 <= count <= 256:
        raise ValueError("invalid fuzzer selector count")
    return WIRE_MAGIC + count.to_bytes(2, "little")


def versioned_input(blob):
    """Use the latest header while preserving the input's operation decoding."""
    if blob.startswith(WIRE_MAGIC):
        if len(blob) < HEADER_SIZE:
            raise ValueError("truncated fuzzer input header")
        count = int.from_bytes(blob[len(WIRE_MAGIC):HEADER_SIZE], "little")
        return input_header(count) + blob[HEADER_SIZE:]
    return input_header(LEGACY_NOPS) + blob
