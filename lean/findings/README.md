# Findings from the coverage-models fuzzers

Branch `spec/coverage-models` (off `fix/fvc-leftovers`) adds Lean models and
differential fuzzers for the crate components that the 2026-11-07 coverage
measurement found were never run or only crash-checked. Each workstream's file
has the details: semantics modelled, standalone Rust repros, campaigns, and what
is and is not covered. This page is the index.

| file | components | sources / ops |
|---|---|---|
| [overlay-exp.md](overlay-exp.md) | `OverlayZipper`, `DiffZipper` (`FullZipper`/`NullZipper` are private) | `overlay`, `overlay-filter`, `diff` |
| [dependent.md](dependent.md) | `DependentProductZipperG` | `dependent`, `dependent-lazy` |
| [product.md](product.md) | `ProductZipper`, `ProductZipperG` | `product`, `productg`, `product-full`, `productg-full` |
| [prefix.md](prefix.md) | `PrefixZipper`, `EmptyZipper` | `prefix`, `empty` |
| [head-owned.md](head-owned.md) | tracked / owned zippers, `ZipperHead` creation, `TrieRef*` | `head`, `owned`, zipper op 60 `trie_ref_probe` |
| [map-core.md](map-core.md) | the `PathMap` surface, whole-map lattice ops | `map` ops 0–28 |
| [map-serial.md](map-serial.md) | `.paths` and `write_trie` serialization, ACT files, merge, stream | `map` ops 30–48 |
| [ops.md](ops.md) | functions no zipper op called: `drop_head`, `join_into_take`, `get_focus_at`/`try_borrow_focus`, witness iteration, k-path overrun, `into_path(_iter)`, deprecated aliases | zipper ops 76-81, checks folded into 7, 20, 51, 52, 75 |
| [map-morph.md](map-morph.md) | catamorphisms, anamorphisms, `ZipperHead` sessions and conflicts | `map` ops 50–60 |
| [ctors.md](ctors.md) | alternative constructors (`PathTracker::new`, `EmptyZipper::new`, `ProductZipper::new_with_primary`, ...), and the round-2 list of uncalled functions | `tracker`, `empty-new`, `product`, `diff-product`, `owned`, `map` ops 1, 17, 18, 48, 55, 60 |

Plus the `tracker` source (`PathTracker`), written as the template.

## Crate bugs

`file`, then the tag used in `lean/differential.py` KNOWN or the skip name.

| # | bug | where |
|---|---|---|
| 1 | `remove_val(prune=true)` keeps the path after an empty `graft_masked_branches` left an empty node (found on the baseline) | corpus `remove_val-prune-after-empty-graft-masked.bin` |
| 2 | `OverlayZipper::ascend_until(_branch)` climbs past a union branch / stops at a filtered value | overlay-exp |
| 3 | `OverlayZipper::descend_until` stops at a filtered value | overlay-exp |
| 4 | `DependentProductZipperG`: a root joint is entered only by a descend; `reset` forgets it (D1) | dependent |
| 5 | `DependentProductZipperG`: a factor after an empty factor appears only on a later call (D2) | dependent |
| 6 | `DependentProductZipperG::val_at`/`get_val_at` look only in the focus factor (D3) | dependent |
| 7 | `ProductZipper(G)`: a childless primary root is not entered, or only until `reset` (P1, the same code as 4 in G) | product |
| 8 | `ProductZipper(G)`: an empty middle factor is a dead end / entered late (P2, ~5) | product |
| 9 | `ProductZipper(G)::val_at` does not cross a joint (P3, ~6) | product |
| 10 | `ProductZipper::val_at` panics (`zipper.rs:3353` unwrap) with the focus at a joint (P4) | product |
| 11 | `ProductZipper::descend_to_check(&[])` is `true` at a missing focus (P5) | product |
| 12 | `PrefixZipper`: merges from inside the prefix read the source root node (P1; upstream 1e95979 fixes most of it) | prefix |
| 13 | `PrefixZipper::descend_until` crosses the seam (P2) | prefix |
| 14 | `PrefixZipper` sibling moves fail one byte off the prefix (P3) | prefix |
| 15 | `PrefixZipper::val_count` off the prefix reports the whole source (P4) | prefix |
| 16 | `PrefixZipper::make_map` off the prefix / over an empty source (P5) | prefix |
| 17 | `PrefixZipper::trie_ref_at_path` ignores the prefix (P6) | prefix |
| 18 | `meet_2` of dangling-only sources creates the focus and keeps the dangling paths (W1) | prefix |
| 19 | `EmptyZipper::to_next_val` does not rewind (E1, issue #137 class) | prefix |
| 20 | `TrieRefOwned` from an empty node drops the location and its value (`TrieRef::from(map)`, write zippers' `get_trie_ref`) | head-owned |
| 21 | `ReadZipperOwned::clone` / `WriteZipperOwned::clone` return to the root | head-owned |
| 22 | `PathMap::pjoin`/`psubtract`/`join_all` report `Element` for a result equal to `self` | map-core |
| 23 | `Debug for PathMap` omits the root value | map-core |
| 24 | `PathMap::join_into` / `ZipperWriting::join_into` report `Element` for an unchanged map with a different layout (may be allowed imprecision) | map-core |
| 25 | `serialize_paths` never writes the focus value | map-serial |
| 26 | `write_trie` below the map root drops path bytes | map-serial |
| 27 | `write_trie` leaves a stale tail after rollback, so the file does not read back | map-serial |
| 28 | `ArenaCompactTree::open_mmap` panics on a file shorter than 8 bytes | map-serial |
| 29 | `ZipperHead`: a reader at a missing head root creates it (H1) | map-morph |
| 30 | `cleanup_write_zipper` on a head from an off-root write zipper resolves against the wrong root; can panic (H2) | map-morph |
| 31 | `into_read_zipper` on an `_unchecked` writer panics in release (H3) | map-morph |
| 32 | a writer dropped without cleanup leaves a stump that a later `remove` below prunes (H4) | map-morph |
| 33 | a reader at a leaf head root leaves an empty node that blocks pruning (H5, family of 1) | map-morph |
| 34 | `WriteZipperCore::try_borrow_focus` is `Some` at a missing focus below a dangling path (O1) | ops |
| 35 | `PrefixZipper::get_focus_at`/`try_borrow_focus` ignore the prefix (O2, same defect as 17) | ops |
| 36 | `remove_unmasked_branches(prune=true)` at a missing focus prunes a dangling parent left by an empty `graft_masked_branches` (O3, family of 1) | ops |

Also a doc/code mismatch: `path_indices().len()` is `focus_factor() + 1` at a
joint (dependent D4, product P6). There is also a debug-only assertion in
`deserialize_file` on a dangling path (map-serial 5).

## Open semantic questions

Collected from the workstream files; each says which reading the model takes.

* ProductZipper vs Zippy's `Composition` (cartesian product of valued paths):
  the model is leaf-based; `Product.semantics := .composition` flips it.
* Is a childless factor root a joint (product, dependent)? Modelled yes.
* Is the focus value part of `.paths` serialization? Modelled yes (bug 25).
* Should catamorphisms and `hash` see dangling paths? Modelled yes; the crate
  agrees, but a `cata_test2` comment says otherwise.
* Is `Element` for an unchanged map with a different layout allowed (bug 24)?
* `EmptyZipper`: a zipper at a missing path, or over an empty map?
* Does the prefix stem exist over an empty source?
* Which lock a `ZipperHead` `Conflict` reports.
* Does `into_path_iter` stop at the end of the focus's subtrie, and include a
  leaf focus?  Modelled no / no: it continues the zipper's traversal (ops).
* May `get_focus_at` return an (empty) node at a childless location?
  Modelled yes (ops).

## Running

```bash
./lean/differential.py --source NAME --random N --seed S -j J
```

`NAME` is any row of `SOURCES` in `differential/src/sources/mod.rs`, or `map`.
When an input hits a known bug, comparison stops at the first divergence, so
the rest of that input goes unchecked. The frequent ones are 20 (~6% of inputs,
every source) and 25 (~10% of map inputs). Named skips avoid that where a bug
would mask everything after it.
