# Crash-only fuzzing findings

Failures `crash_fuzz` found in `pathmap` on 2026-09-16, at commit `7c61024` on
`fuzz-fixes-v2`.  The op table is `differential/src/crash.rs`; see
`differential/src/bin/crash_fuzz.rs` for the runner.  The sites below are as
found; see "Fixed on `fuzz-fixes-v3`" for where they stand now.

Each finding is an input that makes the crate panic, fail a debug assertion,
abort, segfault or hang **through its public API**, with every documented
precondition met.  Calls the crate documents as panicking, stubs, and failures
already known from the differential work are steered around unless
`--include-known` is passed; they are listed at the end.

## Fixed on `fuzz-fixes-v3`

No site outside "Known failures" reproduces on `fuzz-fixes-v3` (fixes on
`fuzz-fixes-v2` and `v3`, each with a test that fails without it).  These
turned up only once the earlier ones were gone:

- A `ZipperHead` reader cloned an ancestor node, so the next exclusive writer
  copied that node and left live writers pointing into the old copy
  (use-after-free).  Readers now own a private root holding only their entry.
  This was behind findings 3, 4 and 8 and the "Lock is missing" panic in
  `zipper_tracking.rs`.
- `PrefixZipper::fork_read_zipper` always forked from the prefix start.
- `ProductZipper` sibling steps that fail at a factor root lost the factor.
- `TrieRef::is_shared` read the refcount of the empty sentinel.
- Joins of two empty child nodes under one key: a dense-node debug assertion
  and a list node left with two onward children.

After the fixes, with the debug-assertion build and known failures steered
around: 0 failures in 4M inputs (seed 36) and in 8M inputs with `--maxlen
2000` (seed 39).  With `--include-known`, only the known failures remain.

## How the surveys were run

| Survey | Build | Inputs | Seed | Time | Failures | Sites |
|---|---|---|---|---|---|---|
| A | debug assertions + overflow checks | 50,000 | 12 | 222 s | 7,165 | 27 |
| B | release | 50,000 | 11 | 134 s | 2,043 | 17 |
| C | release, `--features pathmap/all_dense_nodes` | 10,000 | 13 | 62 s | 845 | 11 |

```sh
# A
CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true \
  CARGO_TARGET_DIR=target/dbgassert cargo build --release -p differential --bin crash_fuzz
target/dbgassert/release/crash_fuzz --random 50000 --seed 12 -j 56 --timeout 8 \
  --keep-going --max-failures 20000 --save runs/crash-a
# B
cargo build --release -p differential --bin crash_fuzz
target/release/crash_fuzz --random 50000 --seed 11 -j 56 --timeout 5 --keep-going --save runs/crash-b
# C
CARGO_TARGET_DIR=target/alldense cargo build --release -p differential --bin crash_fuzz \
  --features pathmap/all_dense_nodes
target/alldense/release/crash_fuzz --random 10000 --seed 13 -j 56 --timeout 5 --keep-going
```

Survey B's release build was taken before the last `KNOWN_FAILURES` entry
(stand-alone `to_next_k_path`) existed.  The site that entry covers is listed
under "Known failures" below.

**Reproducing a fuzz input.**  Inputs are deterministic in (seed, index), so
"A #3620" means:

```sh
target/dbgassert/release/crash_fuzz --random 50000 --seed 12 --dump 3620 > in.bin
CRASH_TRACE=1 CRASH_BACKTRACE=1 target/dbgassert/release/crash_fuzz in.bin
```

`CRASH_TRACE=1` prints every op as it starts, so the last lines before the
failure name the call.  Indices are only valid for the op table at `7c61024`.
Replay a survey A input with the debug build and a B input with the release
build; the other build may fail at a different site or not at all.

**Minimal reproducers** for eight of the findings are compiled in
`differential/src/bin/crash_repros.rs`:

```sh
cargo run -p differential --bin crash_repros -- --list
cargo run -p differential --bin crash_repros -- <name>
```

## Summary

Counts are hits in survey A (debug) / survey B (release); `-` means none in
that survey.  Hangs are counted separately at the end.

| # | Site | A | B | Reached through | Repro |
|---|---|---|---|---|---|
| 1 | `zipper.rs:3616` unreachable_unchecked / SIGSEGV | 33 | 23 | `ZipperHeadOwned::write_zipper_at_exclusive_path` | `owned_head_second_exclusive_path` |
| 2 | `trie_node.rs:1021` unreachable_unchecked / SIGILL | 7 | 4 | `PathMap::join`, `WriteZipper::join_map_into` | A #3620, B #6905 |
| 3 | `malloc(): unaligned tcache chunk detected` (SIGABRT) | 1 | - | `ZipperHead`, then a read zipper | A #8814 |
| 4 | `trie_node.rs:3213` misaligned pointer dereference | 1 (earlier run) | - | `ZipperHead::write_zipper_at_exclusive_path` | - |
| 5 | `write_zipper.rs:2869` slice out of range | 176 | 128 | `ZipperHeadOwned::write_zipper_at_exclusive_path` | A #464 |
| 6 | `zipper_head.rs:347` unwrap on `None` | 24 | 27 | `write_zipper_at_exclusive_path` on a head from `WriteZipper::zipper_head` or `into_zipper_head` | `write_zipper_head_second_exclusive_path` |
| 7 | `write_zipper.rs:1337` assertion `origin_path` not a slice | 1,593 | - | `WriteZipper::zipper_head` on a zipper made by `write_zipper_at_path` | `write_zipper_head_second_exclusive_path` (debug) |
| 8 | `trie_node.rs:3209` make_unique on an empty sentinel | 1 | 16 | `ZipperHead::write_zipper_at_exclusive_path` | A #36325 |
| 9 | `write_zipper.rs:1284` assertion `at_root` | 4 | - | `ZipperHead::write_zipper_at_exclusive_path` | A #69 |
| 10 | `write_zipper.rs:1435` unwrap on `None` | - | 2 | `set_val` on a zipper from a nested `ZipperHead` | B #8504 |
| 11 | `write_zipper.rs:1453` unwrap on `None` | - | 7 | `remove_val` (via `deserialize_paths`) on a zipper from a nested `ZipperHead` | B #5364 |
| 12 | `zipper.rs:1871` explicit panic | 617 | 341 | `get_trie_ref` on a read zipper from a `ZipperHead` | `head_read_zipper_get_trie_ref` |
| 13 | `zipper.rs:2644` unwrap on `None` | 126 | 57 | `ProductZipper::is_shared` | `product_zipper_is_shared` |
| 14 | `zipper.rs:3048` unwrap on `None` | 3 | 3 | `ProductZipper::val_count` | `product_zipper_val_count` |
| 15 | `product_zipper.rs:178` assertion `focus_factor() == factor_count() - 1` | 77 | - | `ProductZipper::val_count` | `product_zipper_val_count` (debug) |
| 16 | `product_zipper.rs:502` assertion "must ascend" | 1,148 | - | `ProductZipperG` sibling moves, `to_next_val`, k-path walks | A #31, A #8704 |
| 17 | `dependent_zipper.rs:166` assertion "must ascend" | 1,163 | - | `DependentProductZipperG` sibling moves, `to_next_val`, k-path walks | A #16 |
| 18 | `overlay_zipper.rs:163` assertion (`focus_byte` of the two sides) | 884 | - | `OverlayZipper::to_next_step`, `to_next_step_observed` | A #17 |
| 19 | `overlay_zipper.rs:152` assertion (`depth` of the two sides) | 2 | - | `OverlayZipper` | A #9317 |
| 20 | `overlay_zipper.rs:330` assertion (`path` of the two sides) | 1 | - | `OverlayZipper::ascend_until` | A #21316 |
| 21 | `zipper.rs:557` subtract with overflow | 12 | - | `OverlayZipper::to_next_step_observed` | A #269 |
| 22 | `prefix_zipper.rs:448` assertion `path_exists()` | 64 | - | `PrefixZipper::descend_indexed_byte`, `descend_last_byte`, `to_next_step_observed` | A #400 |
| 23 | `prefix_zipper.rs:355` index out of bounds | 1 | 3 | `PrefixZipper::to_next_step`, `descend_indexed_byte` | A #46237, B #3769 |
| 24 | `write_zipper.rs:2557` / `2560` slice out of range | 32 | 20 | `graft_child_maps` under a root path of 48+ bytes | `graft_child_maps_long_root` |
| 25 | `zipper.rs:3328` assertion / `zipper.rs:3332` / `3330` slice out of range | 12 | 10 | `get_val_with_witness` on a `ReadZipperOwned` | `owned_read_zipper_witness` |
| 26 | `write_zipper.rs:1304` assertion `at_root` | 1 | - | `join_k_path_into` | A #22746 |
| 27 | `line_list_node.rs:1818` unwrap on `None` | 2 | - | `PathMap::merkleize` | A #4250, A #45491 |
| 28 | `trie_ref.rs:171` subtract with overflow | 2 | - | `trie_ref_at_path`, `get_focus_at` | A #17556, A #49829 |
| 29 | `write_zipper.rs:1132` slice out of range | - | - | `WriteZipperUntracked::path`, only with `all_dense_nodes` (survey C #3135) | C #3135 |

## Undefined behaviour from safe code

### 1. `ZipperHeadOwned` rooted below the map root, second exclusive path

```rust
let zh = sample().into_zipper_head(&[1u8]);
drop(zh.write_zipper_at_exclusive_path(&[]));
let _ = zh.write_zipper_at_exclusive_path(&[9u8]);
```

Release: SIGSEGV.  Debug: `unsafe precondition(s) violated:
hint::unreachable_unchecked must never be reached` at `zipper.rs:3616`.  The
first exclusive zipper at the head's own root, once dropped, leaves the head in
a state the next request walks off.  Sites 5 and 6 are panics from the same
function (`prepare_exclusive_write_path`), reached from differing states;
`write_zipper.rs:2869` is `KeyFields::root_prefix_path` slicing past the end of
the prefix buffer.  (`sample()` is the map `{[0], [1,2,1], [1,2,1,0],
[1,2,1,3,3], [2,2]}`, all values 7.)

### 2. `as_dense_unchecked` on a node that is not dense

Reached from `PathMap::join` and from `WriteZipper::join_map_into` (A #3620,
A #17025, B #6905).  `TaggedNodeRef::as_dense_unchecked` hits
`unreachable_unchecked` (`trie_node.rs:1021`); a release build executes it as
an illegal instruction (SIGILL).  In A #3620 the destination zipper is at a
path below a map built by earlier writes; no minimal repro yet.  The most likely
candidate is a node type the join dispatch assumes cannot occur there (e.g. a
`CellByteNode`, which `ZipperHead` creates), but that is not confirmed.

### 3. Heap corruption after `ZipperHead` writes

A #8814: a `ZipperHead` over a map, an exclusive write zipper doing
`join_k_path_into` and `subtract_into`, then a read zipper from the same head
calling `descend_last_path`.  The process aborts with `malloc(): unaligned
tcache chunk detected`.  Reproduces alone, in both builds (release: SIGABRT with the same message).

### 4. Misaligned pointer dereference

`trie_node.rs:3213`: `misaligned pointer dereference: address must be a
multiple of 0x4 but is 0xff19cac196ee4b9`, one hit in an earlier debug survey
(seed 11, #8513) against an older revision of the op table, in the same code
as site 8 (`make_unique`), from `ZipperHead::write_zipper_at_exclusive_path`.
That index no longer reproduces at `7c61024`, and survey A did not hit it.

## Panics with a minimal reproducer

### 6, 7. `zipper_head()` on a write zipper made with a borrowed path

```rust
let mut map = sample();
let mut wz = map.write_zipper_at_path(&[1u8]);
let zh = wz.zipper_head();
drop(zh.write_zipper_at_exclusive_path(&[]));
let _ = zh.write_zipper_at_exclusive_path(&[]);
```

Debug fails at once, in `zipper_head()`:
`!self.key.origin_path.is_slice() || self.key.origin_path.len() == 0`
(`write_zipper.rs:1337`, `as_static_path_zipper`).  `write_zipper_at_path` takes
the path by reference, so any non-empty root trips it.  Release carries on
and panics on the second exclusive path at `zipper_head.rs:347` (`root_val`
unwrap in `prepare_exclusive_write_path`).  Site 7 is the most frequent
failure in survey A.

### 12. `get_trie_ref` on a read zipper from a `ZipperHead`

```rust
let mut map = sample();
let zh = map.zipper_head();
let rz = zh.read_zipper_at_path(&[1u8]).unwrap();
let _ = rz.get_trie_ref();
```

`focus_parent_borrowed` calls `OwnedOrBorrowed::as_borrowed_ref`, which panics
on the owned root node a head's read zipper holds (`zipper.rs:1871`).  The same
path is reached from `get_focus_at` on those zippers.  Most frequent panic in
survey B.

### 13. `ProductZipper::is_shared`

```rust
let (a, b) = (sample(), sample());
let mut z = ProductZipper::new(a.read_zipper_at_path(&[1u8, 2, 1]), [b.read_zipper()]);
while z.to_next_step() {
    let _ = z.is_shared();
}
```

Once the focus is in the second factor, `ReadZipperCore::is_shared` looks the
focus up in the parent node of the *primary* trie and unwraps `None`
(`zipper.rs:2644`).

### 14, 15. `ProductZipper::val_count` outside the last factor

```rust
let mut a = PathMap::<u64>::new();
a.set_val_at([1u8, 2], 1);
let mut b = PathMap::<u64>::new();
b.set_val_at([3u8, 4], 1);
let mut z = ProductZipper::new(a.read_zipper(), [b.read_zipper()]);
loop {
    let _ = z.val_count();
    if !z.to_next_step() { break }
}
```

Debug: `focus_factor() == factor_count() - 1` (`product_zipper.rs:178`), i.e.
`val_count` is only implemented for the last factor.  Release:
`get_focus_at` unwraps `None` (`zipper.rs:3048`).

### 24. `graft_child_maps` under a long root path

```rust
let mut map = PathMap::<u64>::new();
let mut wz = map.write_zipper_at_path(&[0u8; 48]);
wz.graft_child_maps(ByteMask::from_iter([1u8]), [PathMap::single([2u8], 5)], false);
```

`range end index 49 out of range for slice of length 48`
(`write_zipper.rs:2560`; with a longer root, `2557`).  Roots of 47 bytes or
fewer work.  A fixed 48-byte buffer is being indexed by the full path length.

### 25. `get_val_with_witness` on an owned read zipper

```rust
let mut map = PathMap::<u64>::new();
map.set_val_at([1u8], 1);
let z = map.into_read_zipper(&[]);
let w = z.witness();
let _ = z.get_val_with_witness(&w);
```

Debug: `root_parent_key_start < usize::MAX` (`zipper.rs:3328`).  Release:
`range start index 18446744073709551615 out of range` (`zipper.rs:3332`, and
`3330` in another state).  The root path here is empty; a 3-byte root path
returns `None` without panicking.

### 23 (and a k = 0 case). `PrefixZipper`

```rust
let mut map = PathMap::<u64>::new();
map.set_val_at([0x22u8], 1);
let mut z = PrefixZipper::new(&[2u8, 3][..], map.read_zipper());
z.descend_to_byte(2);
z.descend_last_path();
z.descend_last_path();
z.descend_first_k_path(0);
```

`prefix_zipper.rs:571`, slice out of range: `descend_first_k_path` computes the
untaken part of the prefix as if the focus were still inside it, although the
zipper has moved into the source.
`k = 0` is in `KNOWN_FAILURES` (degenerate) and is skipped by default, but a
slice panic is not a degenerate answer.  Related, without minimal repros:
site 22, `descend_indexed_byte` / `descend_last_byte` landing on a path that
does not exist (`prefix_zipper.rs:448`, A #400); site 23, index out of bounds in
`to_next_step` / `descend_indexed_byte` (`prefix_zipper.rs:355`, B #3769: "the
len is 0 but the index is 0").

## Findings with fuzz inputs only

### 16, 17. `ProductZipperG` and `DependentProductZipperG`: "must ascend"

`to_sibling_byte` gets `Some` from `focus_byte()` and then `ascend(1)` returns
0 (`product_zipper.rs:502`, `dependent_zipper.rs:166`).  Reached from
`to_next_sibling_byte`, `to_prev_sibling_byte`, `to_next_step`, `to_next_val`
and k-path walks (A #31, #8704; A #16).  In release the assertion is gone, and
these zippers hang instead: most hangs in survey B are in these two types.

### 18–21. `OverlayZipper`: the two sides drift apart

The overlay moves both source zippers in step and asserts they agree.  They
stop agreeing on `focus_byte` (site 18, A #17), `depth` (19, A #9317) and
`path` (20, A #21316: `[0, 0, 2, 0, 1]` against `[2, 0, 1]`).  From there,
`to_next_step_observed` reports more ascent to the observer than it descended
(21, A #269: `Vec<u8>` observer underflow at `zipper.rs:557`, with the observer
started from the zipper's current path), and in release `to_next_step` hangs.
Not diagnosed; a move that succeeds on one source and not the other is the
obvious suspect.

### 8, 9. `ZipperHead` exclusive paths

- Site 8, `Attempted to make_unique on an empty sentinel node`
  (`trie_node.rs:3209`, from `make_cell_node` in `prepare_exclusive_write_path`):
  A #36325, B #1730.  Seen after an exclusive zipper did `take_map`,
  `graft_child_maps` or `set_val` at a path and was dropped.  A direct attempt
  (`take_map` then a new exclusive zipper at the same path) did not reproduce.
- Site 9, assertion `self.at_root()` (`write_zipper.rs:1284`): A #69.

### 10, 11. Writes through a zipper from a nested `ZipperHead`

A head made by `WriteZipper::zipper_head()` on a write zipper at a long root,
then `set_val` (`write_zipper.rs:1435`, B #8504) or `remove_val` inside
`deserialize_paths` (`write_zipper.rs:1453`, B #5364) on a zipper it hands out.
Both unwrap `None`.  Release only: in a debug build these inputs stop earlier
at site 7.

### 26. `join_k_path_into`: assertion `at_root`

`write_zipper.rs:1304`, A #22746.

### 27. `PathMap::merkleize`

`line_list_node.rs:1818`, `node_replace_child` unwraps `None` from
`get_child_mut`: A #4250 (`PathMap<bool>`), A #45491 (`PathMap<u64>`).
The list node cannot find the child `merkleize` asks it to replace.

### 28. `trie_ref_at_path` / `get_focus_at`: subtract with overflow

`trie_ref.rs:171`, A #17556, A #49829.  Release wraps silently.

### 29. `all_dense_nodes`: `WriteZipperUntracked::path`

`write_zipper.rs:1132`, `range start index 3 out of range for slice of length
2`, survey C #3135 only.  The default build passes this input.

## Hangs

| Survey | Hangs | Where (last op before the timeout) |
|---|---|---|
| A (debug) | 1,178 | as below; many B hangs fail an assertion (16–21) in A instead |
| B (release) | 1,392 | classified on a 3,000-input sample: `ProductZipperG` / `DependentProductZipperG` sibling moves and k-path walks; `OverlayZipper::to_next_step`; `ProductZipper` k-path walks (k ≥ 1) |
| C (all_dense) | 581 | same kinds |

Hangs are infinite rather than slow: ten sampled inputs were all still running
after 40 s single-threaded, and one after 5 minutes, where a `to_next_step` or a `k ≤ 5` k-path step
should take microseconds.  The simple cases (two small maps, a whole
`to_next_step` or k-path walk over a product or overlay zipper) do not hang;
the hanging inputs move the zipper first.  Shrunk inputs are in
`.fuzzcorpus/crash/shrunk-h*.min.bin` locally; they were not minimised to Rust.

## Not reproduced

- A #30871: SIGABRT in the survey, runs clean alone (3 tries).  Possibly
  caused by another thread's failure in the same process.

## Known failures (steered around by default)

These are `KNOWN_FAILURES` in `differential/src/crash.rs`.  `--include-known`
runs them.

- `val_count` is `todo!()` on `OverlayZipper` (`overlay_zipper.rs:173`) and
  `unimplemented!()` on `ProductZipperG` (`product_zipper.rs:699`) and
  `DependentProductZipperG` (`dependent_zipper.rs:360`).
- `TrieRef::fork_read_zipper` at a missing path unwraps `None`
  (`trie_ref.rs:322`; commented upstream as issue #96).
- `k == 0` for k-path iteration, `join_k_path_into` and `drop_head`: spins on
  several zipper kinds, trips `debug_assert!(byte_cnt > 0)` in
  `LineListNode::drop_head_dyn`, and panics in `PrefixZipper` (above).
- `to_next_k_path` without a preceding `descend_first_k_path`: underflows
  `path_len` (`zipper.rs:2841`, overflow check) and reaches
  `unreachable!()` in `EmptyNode` from `k_path_internal` on a fork of a write
  zipper (`empty_node.rs:70`, survey B, 9 hits).
- `meet_k_path_into` spins when the focus has no children, and escapes it
  when `k == 0`.

## Not covered by the crash table

`viz`, `old_cursor`, `bridge_nodes`, ACT file operations
(`dump_from_zipper`, `open_mmap`, `merge_zipper_into_file`), a `ZipperHead`
shared between threads, custom allocators, `PolyZipper`, `SplitCata` and
`counters`.
