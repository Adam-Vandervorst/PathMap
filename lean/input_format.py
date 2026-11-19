"""Versioned fuzzer inputs shared by the Python generators and shrinker."""

WIRE_MAGIC = b"PMFUZZ\x01\x00"
LEGACY_NOPS = 56
# Keep in sync with NOPS in differential/src/harness.rs.
NOPS = 75
HEADER_SIZE = len(WIRE_MAGIC) + 2


def input_header(count=NOPS, magic=WIRE_MAGIC):
    if not 1 <= count <= 256:
        raise ValueError("invalid fuzzer selector count")
    return magic + count.to_bytes(2, "little")


def versioned_input(blob, magic=WIRE_MAGIC, legacy=LEGACY_NOPS):
    """Use the latest header while preserving the input's operation decoding."""
    size = len(magic) + 2
    if blob.startswith(magic):
        if len(blob) < size:
            raise ValueError("truncated fuzzer input header")
        count = int.from_bytes(blob[len(magic):size], "little")
        return input_header(count, magic) + blob[size:]
    return input_header(legacy, magic) + blob


# The pruned harness (differential/src/pruned.rs, PrunedModel/Fuzz.lean): the
# same layout with its own marker and operation table.
PRUNED_MAGIC = b"PMPRUN\x01\x00"
PRUNED_LEGACY_NOPS = 54
# Keep in sync with NOPS in differential/src/pruned.rs.
PRUNED_NOPS = 54


def pruned_input_header(count=PRUNED_NOPS):
    return input_header(count, PRUNED_MAGIC)


def pruned_versioned_input(blob):
    return versioned_input(blob, PRUNED_MAGIC, PRUNED_LEGACY_NOPS)
