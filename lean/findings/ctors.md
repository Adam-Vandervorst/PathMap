# ctors: alternative constructors and the functions no op called

Workstream branch `cov/ctors` (round 2).  The 2026-11-09 re-measurement listed
public functions that no fuzzer op calls.  This workstream's share was mostly
*alternative constructors* of components that are already modelled, so the
approach is the one `head.rs` and `prefix.rs` use: derive a construction
variant from bytes the input already has (the decoder position after the
header, the header roots, or spare high bits of an operand byte), so the wire
format does not change, and hold every construction to the same view.

## What changed

Zipper sources (`differential/src/sources/`, `lean/PathMapModel/Sources/`):

| source | change | model |
|---|---|---|
| `tracker` | `PathTracker::new(map1.read_zipper_at_path(root1))` when `(|root0| + |root1|)` is odd, else `with_origin(.., root1)` | `new` presents map1's subtrie at root1 as a trie of its own, rooted at `[]` (`trackerNew`) |
| `empty-new` (new) | `PathTracker::with_origin(EmptyZipper::new(), root)` | `empty`'s view; tracker caps (no fork, no read-only iteration) |
| `product` | `hdr % 3`: `ProductZipper::new`, or `new_with_primary` + `new_factors(both)`, or `new_with_primary` + `new_factors` once per factor and once empty | unchanged: one zipper |
| `diff-product` (new) | `DiffZipper::new(PZ::new(..), PZ::new_with_primary(..)+new_factors(..), false)`, `ZipperProduct` read through `DiffZipper` | `product`'s view, info and skips; no read-only values |
| `owned` | `MAP1` is `rz.into_map()` (`ReadZipperOwned::into_map`) | unchanged: the map it was given |

Map fuzzer (`differential/src/mapfuzz/`, `lean/PathMapModel/MapFuzz/`):

| op | change |
|---|---|
| 1 | map byte `/3 % 2`: `PathMap::insert` instead of `set_val_at` (alias, same answer); `/6 % 4 = 3`: path `++ longTail` (48 bytes), so keys outgrow a `LineListNode` key buffer (42 bytes with `slim_ptrs`) and `set_child_0/1` run (Lean: `longTail`) |
| 17 | kind byte `/5 % 2`: kinds 0–2 built by `WriteZipperOwned::new` / `new_in` + `descend_to` + `set_val` + `into_map` (same map as `single`) |
| 18 | kind byte `/3 % 2`: kinds 0–1 read as `PathMap::trie_ref_at_path(p)` (`&Vec` and `&[u8]` keys) + `fork_read_zipper` dump (same dump) |
| 48 | adds the unit-valued `ArenaCompactTree::read_zipper()`: a walk with value flags (`val` vs `get_val`), `val_at(q)` vs `get_val_at(q)` from the root, `fork_read_zipper` at `q` (Lean: `unitWalk`) |
| 55 | each closure call reports `<path>#<TrieBuilder::len>.<TrieBuilder::child_mask>` after it ran (Lean: `anaGo` records each call's pushed first bytes) |
| 60 | session kind 4's bool byte `/2 % 2`: `read_zipper_at_borrowed_path_unchecked` for a reader (path in the session arena); same zipper, same `skip:unchecked-conflict` rule |

## Semantic decisions

* **A construction variant is the same zipper.**  `ProductZipper::new` and
  `new_with_primary` + `new_factors` (in one call, or one factor per call, or
  with an empty list) present one view; `insert` is `set_val_at`; a map built
  by `WriteZipperOwned::new[_in]` + `descend_to` + `set_val` + `into_map` is
  `PathMap::single`; `trie_ref_at_path(p)` + `fork_read_zipper` reads what
  `read_zipper_at_path(p)` reads; `read_zipper_at_borrowed_path_unchecked` is
  `read_zipper_at_path_unchecked`.  So most variants need no model change at
  all: the existing answer is the specification.
* **`PathTracker::new` re-roots.**  Its doc says it tracks "the path from the
  zipper's root" with an empty `root_prefix_path`, so around a read zipper at
  root1 it presents map1's subtrie at root1 as a whole trie rooted at `[]`
  (root value included).  `with_origin` keeps the absolute coordinates.
* **`EmptyZipper` is a zipper at a missing location** (the open question in
  [prefix.md](prefix.md)).  Decision: `new()` and `new_at_path(p)` are the
  same zipper with different root prefixes, and `path_exists` is `false`
  everywhere, the root included, exactly as `empty_zipper.rs` implements and
  as `new_at_path` was already modelled.  That a read zipper over an *empty
  `PathMap`* reports its root as existing is not a contradiction: a `PathMap`'s
  root always exists, an `EmptyZipper` has no map.  The model cannot place a
  missing location at `[]` (its tries always contain `[]`), so `new()` is
  checked behind `PathTracker::with_origin(EmptyZipper::new(), root)`: the
  tracker only resets the zipper and keeps the path above it, and every other
  answer (`path_exists`, `child_mask`, `at_root`, the moves, the values) is
  `new()`'s own, held to `empty`'s view.  The `empty` source's known
  `to_next_val_no_rewind` reproduces through it (the tracker forwards
  `to_next_val` to `EmptyZipper`), and the `["src:empty", ...]` KNOWN keys
  match `src:empty-new` too, as they should.  Remaining open: whether the
  crate *intends* `EmptyZipper::new()` to model "an empty map" (then its root
  should exist); nothing in its docs says so.
* **`TrieBuilder::len` / `child_mask`** after an anamorphism closure ran: the
  number of children pushed (`push`, `push_byte`, `graft_at_byte`, or the
  children of `set_child_mask`) and the set of their first bytes.
* **The unit-valued ACT zipper** (`ArenaCompactTree::read_zipper`) reads the
  same trie as the `u64` one with every value replaced by `()`: same locations,
  value where there is a value; `get_val`/`get_val_at` agree with
  `val`/`val_at`; `fork_read_zipper` is `None` exactly where the path is
  missing.

## Campaigns

`-j 8`, 50k inputs per seed; no new divergences anywhere.  (The zipper sources ran before op 1's tail grew from 16 to 48 bytes, a map-only change.)

| source | inputs (seeds) | agree | known |
|---|---|---|---|
| `diff-product` | 100k (11, 12/maxlen 900) | 92 685 | 7 315, all `trie_ref_owned_empty_node` (write side) |
| `empty-new` | 100k | 68 924 | 31 076, nearly all `to_next_val_no_rewind` (the `empty` bug) + `trie_ref_owned_empty_node` |
| `tracker` | 100k | 92 069 | 7 931 |
| `product` | 100k | 90 745 | 9 255 |
| `owned` | 100k | 40 474 | 59 526, mostly `owned_clone_resets_focus` (`RCLONE`/`WCLONE`, after `MAP1`) |
| `map` | 100k (11, 12) | 85 691 | 14 309, serialization bugs of map-serial.md, `map_join_into_layout_status` |

Final sweep (seed 21, final binaries): every zipper source 10k inputs, `map`
100k (seed 13), all with 0 new divergences (`native` 9418 agree / 582 known,
`act` 9638/362, `tracker` 9638/362, `overlay` 9596/404, `overlay-filter`
9471/529, `diff` 9638/362, `dependent` 9627/373, `dependent-lazy` 3924/6076,
`head` 9418/582, `owned` 4717/5283, `empty` 7540/2460, `empty-new` 8390/1610,
`prefix` 8061/1939, `product` 9605/395, `productg` 9675/325, `product-full`
8036/1964, `productg-full` 8946/1054, `diff-product` 9675/325, `map`
92631/7369).  The map corpus files still reproduce (`map-join_into-status-*`
known, `act-open_mmap-short-file-panics` agrees under its skip): op 1's new
variants only use bits of a byte that was read as `% 3` before.

## Crate bugs

None new.  Everything that diverged was an already-known bug, checked per
class as above.

## The round-2 list, function by function

Coverage below is from an instrumented build of this branch
(`-C instrument-coverage`), 8 000 inputs per zipper source and 40 000 map
inputs (seed 31); counts are calls.

| function | status |
|---|---|
| `ReadZipperOwned::new_with_map` (`pub(crate)`) | reached through `into_read_zipper` and `clone()` in `owned` (74k); answer-checked by every op on `rz` and by `RCLONE` |
| `ReadZipperOwned::into_map` | already called in `owned` (`hdr / 2` odd); now also `MAP1` is `rz.into_map()` (19k) |
| `fork_read_zipper` on `ReadZipperTracked` / `ReadZipperOwned` | already reached: op 26 `dump` on the read side of `head` / `owned` (3.7k each); caps.fork is `true` for both.  The re-measurement's "never called" was a matching artefact (the 2026-11-09 data, cov-new.json, has them at 73k) |
| `Drop for ReadZipperTracked` | already reached in `head` (41k); an empty `fn drop` (it only fixes when the tracker field drops), nothing of its own to check |
| `ReadZipperTracked::new_with_node_and_cloned_path_in` | `pub(crate)`; left |
| `ReadZipperUntracked::new_with_node_and_path_in` | `pub(crate)`; left |
| `WriteZipperOwned::new_in` (+ `new`) | map op 17 (2.3k / 40k) |
| `ZipperCreation::read_zipper_at_borrowed_path_unchecked` | map op 60 kind 4 (915) |
| `PathMap::trie_ref_at_path` | map op 18, `&Vec` and `&[u8]` keys (4.1k) |
| `PathMap::insert` | map op 1 (15.7k) |
| `goat_val_count` closures | already reached by map op 12 (74k / 48k) |
| `ProductZipper::new_with_primary`, `new_factors` | `product` (`hdr % 3`) and `diff-product` (11k each).  `ProductZipperG` has only `new` |
| `PathTracker::new` | `tracker` (`trackerNew`) (3.7k) |
| `PathTracker::is_val` / `child_mask` / `depth` | reached through the per-step fingerprint (480k) |
| `EmptyZipper::new` | `empty-new` (7.4k) |
| `DiffZipper` `focus_factor` / `factor_count` / `path_indices` | `diff-product`, through `source_info` (439k); `child_mask` through the fingerprint (480k) |
| `TrieBuilder::len` / `child_mask` | map op 55 (39k) |
| `new_map_from_ana_jumping` | does not exist any more: it was in `morphisms.rs` at f3e442e (the 2026-11-07 baseline) and has been removed |
| `ArenaCompactTree::read_zipper` (unit) | map op 48 (23k), with the unit `val`, `val_at`, `get_val`, `get_val_at`, `fork_read_zipper` (all previously never run) |
| `ACTZipper::child_mask` | the fingerprint in `act` mode (480k) |
| `ArenaCompactTree::counters` | not checkable: `Counters`' fields are private, it is only `Debug`-printable, it counts nothing unless the `act_counters` feature is on (off in the harness), and what it counts is encoding sizes (representation, not meaning) |
| `line_list_node.rs` `set_child_0` / `set_child_1` | reachable: a key longer than `KEY_BYTES_CNT` (42 with the default `slim_ptrs`) stored in one `LineListNode` (into an empty node: slot 0; next to a short key: slot 1).  Map op 1's long variant; checked by its answer and every later dump.  The fuzzers' paths were never longer than ~10 bytes before |
| `dense_byte_node.rs` `convert` (2) | unreachable: `HeteroLattice::convert` is only called by the trait's default `join_into`, which both implementations (`Cf`, `ByteNode`) override |
| `dense_byte_node.rs` `Default` for `OrdinaryCoFree` / `CellCoFree` | unreachable: only there to satisfy `CoFree: Default`; nothing calls `default()` / `mem::take` on a cofree |
| `dense_byte_node.rs` `both_mut` (2) | unreachable: no caller in the crate except `CellCoFree::both_mut` delegating to `OrdinaryCoFree::both_mut` |
| `dense_byte_node.rs` `convert_to_cell_node` for a cell node | `unreachable!()` by design |
| `trie_node.rs` `TaggedNodeRef::as_list` | unreachable in the harness: called only by `counters.rs` (feature `counters`, a node-statistics module) and inside `debug_assert!`s |
| `trie_node.rs` `TaggedNodeRefMut::as_cell_node` | no caller anywhere in the crate |
| `trie_node.rs` `TaggedNodeRefMut::node_get_val_mut` | no non-test caller (the crate uses `node_into_val_ref_mut`) |

## Not done

* `ProductZipperG` has no alternative constructor to drive.
* The `empty-new` source inherits `empty`'s high known rate
  (`to_next_val_no_rewind` ends the comparison of an input at its first
  `to_next_val`), as `empty` does.
