# All crate bugs found by the coverage-models fuzzers

One list, grouped by what goes wrong, with entries that are the same defect
merged.  `#n` is the number in [README.md](README.md)'s index; the workstream
file named after it has the minimal repro (corpus `.bin` and/or standalone Rust)
and the reasoning.  Found on `fix/fvc-leftovers` (ad250b9) via
`spec/coverage-models`.

## Panics (release builds)

| | bug | # | file |
|---|---|---|---|
| 1 | `ProductZipper::val_at` panics (`zipper.rs:3353`, `focus_parent` unwrap) with the focus on a joint or in the first node of a secondary factor | 10 | product |
| 2 | `ArenaCompactTree::open_mmap` panics on a file shorter than 8 bytes (empty included) instead of returning `Err` | 28 | map-serial |
| 3 | `cleanup_write_zipper` on a `ZipperHead` taken from a write zipper whose focus is below its root resolves the path against the parent's root: panics at `zipper_head.rs:347`, can prune the wrong location, resets the parent | 30 | map-morph |
| 4 | `into_read_zipper` on an `_unchecked` writer panics (`write_zipper.rs:541`, missing tracker) | 31 | map-morph |
| 5 | `TrieBuilder::graft_at_byte` panics (`morphisms.rs:1238`) when the zipper's focus is an existing leaf | 37 | ptree |

## Wrong answers: product zippers (`ProductZipper`, `ProductZipperG`, `DependentProductZipperG`)

`ProductZipperG` and `DependentProductZipperG` share the factor-entry and
`val_at` code; `ProductZipper` has its own but the same faults.

| | bug | # | file |
|---|---|---|---|
| 6 | A childless factor root (incl. the primary's root) is entered only after some descend, and `reset` forgets it; `descend_to([])` changes `child_count` | 4, 7 | dependent, product |
| 7 | An empty middle factor: `ProductZipper` never enters the factor after it; the generic ones enter it only on a later call, so iteration skips that subtrie | 5, 8 | dependent, product |
| 8 | `val_at` / `get_val_at` do not follow a path across a joint into the next factor (answer `None`) | 6, 9 | dependent, product |
| 9 | `ProductZipper::descend_to_check(&[])` returns `true` at a non-existent focus | 11 | product |
| 10 | Doc mismatch: `path_indices().len()` is `focus_factor() + 1` at a joint, against the trait doc | (D4, P6) | dependent, product |

## Wrong answers: `PrefixZipper`, `OverlayZipper`, `EmptyZipper`

| | bug | # | file |
|---|---|---|---|
| 11 | `PrefixZipper`: merges from a focus inside the prefix read the source's root node (`get_focus`/`get_focus_at` delegate unadjusted; upstream 1e95979 fixes most of it, still loses the dangling stem over an empty source) | 12 | prefix |
| 12 | `PrefixZipper::get_focus_at` / `try_borrow_focus` / `trie_ref_at_path` pass the path to the source without accounting for the prefix | 17, 35 | prefix, ops |
| 13 | `PrefixZipper::descend_until(_max_bytes)` runs past the seam when the source root has a value or branches | 13 | prefix |
| 14 | `PrefixZipper` sibling moves return `None` one byte off the prefix, so `to_next/prev_step` stop | 14 | prefix |
| 15 | `PrefixZipper::val_count` off the prefix returns the source's whole count instead of 0 | 15 | prefix |
| 16 | `PrefixZipper::make_map` returns the whole source off the prefix, and drops the dangling stem inside the prefix over an empty source | 16 | prefix |
| 17 | `OverlayZipper::ascend_until` / `ascend_until_branch` climb past a branch formed by the union, and stop at a value the mapping filtered out | 2 | overlay-exp |
| 18 | `OverlayZipper::descend_until(_max_bytes)` stops at a source value the mapping filtered out | 3 | overlay-exp |
| 19 | `EmptyZipper::to_next_val` / `to_next_get_val` do not rewind to the root (issue #137 class; b5a0fb9 fixed only `to_next_k_path`) | 19 | prefix |

## Wrong answers: empty nodes left behind (layout-dependent state)

All one family: an operation leaves an empty node (or a dangling stump) where
the logical trie has none, and a later prune/remove then depends on whether
that node is there.

| | bug | # | file |
|---|---|---|---|
| 20 | After an empty `graft_masked_branches`, `remove_val(prune=true)` keeps the path | 1 | corpus `remove_val-prune-after-empty-graft-masked.bin` |
| 21 | After an empty `graft_masked_branches`, `remove_unmasked_branches(prune=true)` at a missing focus one byte below prunes the dangling parent (with `remove_branches(false)` instead of the graft it does not) | 36 | ops |
| 22 | A `ZipperHead` writer dropped without cleanup leaves a stump; a later `remove` at a non-existent path below prunes it, where an ordinary dangling path survives | 32 | map-morph |
| 23 | A `ZipperHead` reader at a leaf head root leaves an empty node; afterwards `remove(root)` no longer prunes | 33 | map-morph |
| 24 | `WriteZipperCore::try_borrow_focus` returns `Some` (the dangling path's empty node) at a missing focus below a dangling path; the read core answers `None` (debug builds assert at `write_zipper.rs:1435`) | 34 | ops |
| 25 | `TrieRefOwned::new_with_node_and_val_in(None, val)` returns an invalid ref and drops `val`: `TrieRef::from(map)` of a childless map, and every write zipper's `get_trie_ref()` at a childless focus, say not-exists and `val() == None` | 20 | head-owned |

## Wrong answers: other

| | bug | # | file |
|---|---|---|---|
| 26 | `meet_2` of dangling-only sources creates the destination focus and copies the dangling paths | 18 | prefix |
| 27 | `ReadZipperOwned::clone` / `WriteZipperOwned::clone` come back at the root, not at the original's focus | 21 | head-owned |
| 28 | `ZipperHead`: opening a reader from a head whose root path does not exist creates that path | 29 | map-morph |
| 29 | `serialize_paths` never writes the focus value (round trip loses the root value and clears the destination's focus value) | 25 | map-serial |
| 30 | `write_trie` from a zipper below the map root drops path bytes (treats the absolute `origin_path` as relative; `MAX_PATH_LEN` counts the prefix) | 26 | map-serial |
| 31 | `write_trie` rolls back a duplicate last record without truncating the file; `deserialize_file` then rejects it | 27 | map-serial |
| 32 | `Debug for PathMap` omits the root value (a map holding only a root value prints `{}`) | 23 | map-core |
| 32a | `ByteMask::set_`/`clear_`/`toggle_inclusive_bit_range` read `start()`/`end()` of a `RangeInclusive` iterated to its end (empty; std calls the bounds unspecified) and act on bit `end`; `ByteMask::from` of the same range is correctly empty | 40 | u-mask |

## Imprecise `AlgebraicStatus` (contents correct)

| | bug | # | file |
|---|---|---|---|
| 33 | `PathMap::pjoin` / `psubtract` / `join_all` report `Element` when the result equals `self` | 22 | map-core |
| 34 | `PathMap::join_into` / `ZipperWriting::join_into` / `join_into_take` report `Element` for an unchanged map whose source has a different node layout (possibly allowed by the docs; recorded, not accepted) | 24 | map-core, ops |
| 34a | `Lattice::join_all` (trait default) over all-empty arguments answers `Identity(1 << (n-1))` for odd `n`, `None` for even (`ByteMask`, `[u64; 4]`, any type using the default); the contract allows both, `None` "should" win | 39 | u-mask |

## Debug builds only

| | bug | # | file |
|---|---|---|---|
| 35 | `SplitCata` / `SplitCataJumping` assert a childless valueless location is the root; a dangling leaf trips it | 38 | ptree |
| 36 | `deserialize_file` asserts `!path_node.is_empty()` on a `write_trie` file containing a dangling path (release drops it, matching the model) | (map-serial 5) | map-serial |
| 36a | `ByteMask::set_`/`clear_`/`toggle_inclusive_bit_range` `debug_assert!(start <= end)` on an empty `a..=b` (`a > b`); release correctly does nothing, and `from_range` documents `start >= end` as empty | 41 | u-mask |

36 entries: 35 defects and one doc mismatch, from the 38 numbered index rows
plus 2 notes, with 4 duplicate pairs merged (4/7, 5/8, 6/9, 17/35).  Bug 24's
debug assertion is listed with it, not separately.
