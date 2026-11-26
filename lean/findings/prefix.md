# PrefixZipper and EmptyZipper (workstream `prefix`)

Read sources `--source prefix` (`differential/src/sources/prefix.rs`,
`lean/PathMapModel/Sources/Prefix.lean`) and `--source empty`
(`sources/empty.rs`, `Sources/Empty.lean`).

## The models

**PrefixZipper.**  `PrefixZipper::new(P, map1.read_zipper_at_path(s))`, root
prefix set to `P[..k]` with `set_root_prefix_path` or `with_origin`.  `P`, `s`
and `k` come from the two header roots (`config` / `prefixConfig`): `P` is `[]`
(as in the crate's tests), root0, `[2,1] ++ root0` or root1; `s` is root1 or
`[]` (so `P = s = root1` is the native view); `k ∈ [0, |P|]`.

The view is the source's subtrie (from the source root, root value included)
moved under `P`, rooted at `P[..k]` (`PathMap.prependPath`):

* `root_prefix_path = P[..k]`, `origin_path` = absolute path, `path` = the rest
  (which may still be inside the prefix) — the crate's doc example.
* Every location along `P` exists iff the source root does (always, here: the
  header creates it).  This is the crate's own rule since PR #147
  (`path_exists` inside the prefix = `source.path_exists()`).
* Locations strictly above `P` carry no value and have exactly one child (the
  next prefix byte); the value at `P` is the source's root value
  (`prefix_zipper_val_at_test`).  Any other byte leaves the trie.
* A focus inside the prefix is an ordinary location of that trie: its subtrie is
  "rest of the prefix, then the source", its `val_count` the source's total, and
  a merge, `make_map`, fork or trie ref from it reads exactly that.

Everything else is the native read-zipper specification on the view.  Caps: all
(fork, make_map, merge, get_val, get_val iteration, val_count, trie_ref).

**EmptyZipper.**  `EmptyZipper::new_at_path(p)`, `p` = root1 or `[3]`: the
empty trie, rooted at `p`, which does not exist.  Caps: fork (always `None`),
get_val, get_val iteration, val_count; no subtries, so no make_map, merges or
trie refs (`skip:empty`).

## Framework changes (shared files)

* `Source.mergeAt` (Lean) / the second arm `full_read_source!(skip, merge_at)`
  (Rust): a per-focus veto on merges, rendered as `skip:<name>`.  `St` carries
  `mergeAt` (from the header) and `St.canMerge` replaces the ten
  `!s.src.caps.merge` guards.  `join_map_into` stays gated on `make_map` only.
* `full_read_source!` used `fork_read_zipper()` as if it were not an `Option`;
  fixed to use clones (the same fix landed upstream on spec/coverage-models).
* `differential.py`: `divergence_shape`'s `DANGLING-FOCUS-KEPT` also covers
  `meet_2`.  Source-keyed KNOWN entries use `src:<source>` (merged from
  spec/coverage-models).

## How the bugs were confirmed

Each class below was checked by patching a *scratch copy* of the crate (never
this branch) with the obvious fix and re-running the campaign: with all six
`prefix_zipper.rs` fixes (plus upstream's `get_focus` fix 1e95979 and merges
from the stem re-enabled) the prefix source agrees with the model on 30k inputs
with zero read-side known hits, the only remaining hits being write-side
known bugs (finding 8 status, `join_into_empty_dst`, `meet_2` below,
`trie_ref_owned_empty_node`).  That also validates the model of merges *from the
stem*, which this branch skips.

Standalone repros (all run against this branch's crate; output shown):

```rust
use pathmap::{PathMap, zipper::*};
fn paths(m: &PathMap<u64>) -> Vec<Vec<u8>> { let mut z = m.read_zipper(); let mut v = vec![]; while z.to_next_step() { v.push(z.path().to_vec()); } v }
```

## Bug P1: merges from inside the prefix read the source's root node (skipped)

`ZipperInfallibleSubtries::get_focus` / `get_focus_at` / `try_borrow_focus`
delegate to the source zipper, which sits at its own root while the focus is in
the prefix.  So `graft`, `graft_src_at`, `join_into`, `meet_into`,
`subtract_into`, `restrict`, `restricting`, `graft_masked_branches` and
`meet_2` from a focus strictly inside `P` read the source root node instead of
"rest of the prefix, then the source"; from a focus that has left `P` they read
the whole source instead of nothing.

```rust
let src: PathMap<u64> = [(&[7u8][..], 1u64)].into_iter().collect();
let pz = PrefixZipper::new(&[1u8, 2][..], src.read_zipper());
let mut dst = PathMap::<u64>::new();
dst.write_zipper().graft(&pz);
// dst = [[7]]   want [[1],[1,2],[1,2,7]]
```

**Already fixed upstream** by Luke's 1e95979 ("grafting from the stem of a
prefix zipper too"), which this branch's base does not contain.  It corrupts
map0 for the rest of a run, so merges are skipped unless the focus is at or
below `P` (`merge_at` in `prefix.rs`, `prefixMergeAt` in `Prefix.lean`).
Residual in 1e95979: over a source whose trie is empty (root exists, nothing
below it), its `get_focus` builds a map without the dangling prefix chain, so a
graft from the stem creates nothing where the model (and `path_exists`) say the
chain exists — same root cause as P5.  Remove the veto once 1e95979 is merged.

## Bug P2: `descend_until` crosses a valued seam

`descend_until_observed` consumes the rest of the prefix and then always lets the
source continue, even when the source root (the location at `P`) carries a value
or branches.  `descend_until_max_bytes` inherits it.  The spec ("descends until
a branch or a value is encountered") stops at `P`.

```rust
let src: PathMap<u64> = [(&[][..], 5u64), (&[3u8, 4][..], 6)].into_iter().collect();
let mut pz = PrefixZipper::new(&[1u8][..], src.read_zipper());
pz.descend_until();   // path = [1,3,4], val Some(6);  want [1], Some(5)
```

Corpus: `lean/corpus/prefix-descend_until-crosses-seam-value.bin` (`--source prefix`).
Fix: after `consume_prefix`, return `true` if `source.is_val() || source.child_count() != 1`.

## Bug P3: no sibling one byte off the prefix

`to_next_sibling_byte` / `to_prev_sibling_byte` return `None` unless the focus is
in the source.  At a missing focus one byte off the prefix (`PrefixOff{invalid:1}`)
the parent exists and its one child, the prefix byte, *is* a sibling; the
documented `to_next_step` ("from a non-existent path, moves to the next existing
path") and `to_prev_step` therefore stop instead of moving.

```rust
let src: PathMap<u64> = [(&[9u8][..], 1u64)].into_iter().collect();
let mut pz = PrefixZipper::new(&[2u8][..], src.read_zipper());
pz.descend_to_byte(0);
pz.to_next_sibling_byte();   // None; want Some(2)
// to_next_step from the same place: false, path []; want true, [2]
```

Corpus: `lean/corpus/prefix-sibling-off-prefix.bin`.  (At the seam itself — the
source at its root — sibling moves correctly return `None`; checked.)

## Bug P4: `val_count` off the prefix

`val_count` returns `source.val_count()` in every position; off the prefix the
source is at its root, so a missing focus reports the source's whole count.

```rust
let src: PathMap<u64> = [(&[9u8][..], 1u64), (&[8u8][..], 2)].into_iter().collect();
let mut pz = PrefixZipper::new(&[2u8][..], src.read_zipper());
pz.descend_to_byte(0);
pz.val_count();   // 2 (path_exists false); want 0
```

Corpus: `lean/corpus/prefix-val_count-off-prefix.bin`.  The most frequent class
(~10% of inputs): every step fingerprint prints `n`.  Its shape is
`DANGLING-KEPT`, which the generic `meet_keeps_dangling` entry used to swallow
until the `READ-SIDE` tag existed.

## Bug P5: `make_map` off the prefix, and over an empty source

* Off the prefix (`prefix_path_below_focus() == None`), `make_map` /
  `try_make_map` return the source's whole map; want an empty map.
* Inside the prefix over an empty source, `make_map` grafts an empty map below
  the remaining prefix, which creates nothing: the dangling chain that
  `path_exists`/`child_count` report is lost.

```rust
// off the prefix (pz from P4): paths(&pz.make_map()) = [[8],[9]]; want []
let empty = PathMap::<u64>::new();
let pz = PrefixZipper::new(&[2u8, 3][..], empty.read_zipper());
// pz.path_exists() = true, child_count() = 1, make_map() = []; want [[2],[2,3]]
```

Corpus: `prefix-make_map-off-prefix.bin`, `prefix-make_map-drops-empty-stem.bin`
(both via `join_map_into`).  The second is frequent here because the source is
often the dangling path root1 alone.

## Bug P6: `trie_ref_at_path` ignores the prefix

`ZipperReadOnlySubtries::trie_ref_at_path(p)` is `source.trie_ref_at_path(p)`:
inside the prefix it does not strip the remaining prefix bytes from `p` (so it
reads the source at the wrong path), and off the prefix it reads the source
anyway.  A path that ends inside the prefix cannot be expressed with the
source's `TrieRefT` at all, so the fix needs a different associated type (or
`TrieRef::from(make_map())` like `get_trie_ref` does).  `get_trie_ref`
(op 75 mode 1) and the `make_map`-based modes 2/3 inherit P5.

Corpus: `lean/corpus/prefix-trie_ref_at_path-ignores-prefix.bin` (P=[1], source
root value 5: the crate reports the source root as the zipper's root).

## Bug W1 (write side, newly reachable): `meet_2` keeps dangling-only sources

`meet_2` of two sources that hold only dangling paths creates the destination
focus and copies the dangling paths in (status `None`); the model's meet has no
dangling paths.  Same family as `meet_keeps_dangling`.  The native source can
never present dangling paths below its root (the header only seeds values); the
prefix source can (source at `[]`, root1 created), which is why it shows up now.

```rust
let mut m1 = PathMap::<u64>::new(); m1.create_path(&[1u8, 0]);
let mut m0 = PathMap::<u64>::new();
let mut wz = m0.write_zipper_at_path(&[0u8]);
wz.meet_2(&m1.read_zipper(), &m1.read_zipper());   // None
// map0 = [[0],[0,1],[0,1,0]]; want []
```

Corpus: `prefix-meet_2-keeps-dangling.bin`.

## Bug E1: `EmptyZipper::to_next_val` does not rewind

`to_next_val_observed` and `to_next_get_val_observed` return `false`/`None`
without moving; the trait says they return `false` having "encountered the
root", i.e. the zipper is back at its root (the native zipper, and
`PrefixZipper` since 70d3dd3, rewind).  The same class as issue #137, which
fixed `to_next_k_path` on both zippers (b5a0fb9) but not `to_next_val`.

```rust
let mut ez = EmptyZipper::new_at_path(&[3u8]);
ez.descend_to(&[0u8, 1]);
<EmptyZipper as ZipperIteration>::to_next_val(&mut ez);   // false, path [0,1]; want []
```

Corpus: `lean/corpus/empty-to_next_val-no-rewind.bin` (`--source empty`).

## Earlier PrefixZipper fixes

None of the earlier fixes regressed: the missing-source rule (PR #147), fork at
the focus (#96 / 5866a4e), `to_next_val` from a missing path (70d3dd3) and
`descend_first_k_path(0)` / `to_next_k_path` (b5a0fb9) all agree with the model.

## Open questions

* **EmptyZipper at `[]`.**  `EmptyZipper::new()` reports `path_exists() == false`
  at its root, whereas a read zipper over an empty `PathMap` reports `true`.  The
  model always contains the absolute root `[]`, so it cannot express that view;
  the source roots EmptyZipper at a non-empty path.  Is an `EmptyZipper` meant to
  be "a zipper at a missing path" (then `new()` is fine) or "a zipper over an
  empty map" (then its root should exist)?
* **The stem over an empty source.**  The model follows `path_exists` (PR #147):
  the prefix chain exists whenever the source root does, even with nothing below
  it, so `make_map`/merges from the stem must produce a dangling chain (P5, P1
  residual).  If the intent is instead that an empty source makes the whole prefix
  vanish, `path_exists`/`child_count` are the ones to change.
* A source whose root does not exist (the crate's `prefix_zipper_over_missing_source`)
  is not generated: the header creates root1, and with an empty prefix the native
  source would escape its root (the known `root_escape`).

## Covered / not covered

Answer-checked now (`--source prefix`): every read, movement and iteration op on
the view, including `consume_prefix` (descend_until, to_next_val,
descend_last_path, descend_first_k_path), `ascend_n` / `ascend_until_n`,
`adjust_lookup_path` (val_at, get_val_at), `prefix_path_below_focus`,
`fork_read_zipper` (dump), `make_map` (op 25, join_map_into, op 75 modes 2/3),
`get_trie_ref` / `trie_ref_at_path` (op 75), and the merges' `get_focus` /
`get_focus_at` from a focus in the source.  `--source empty`: every EmptyZipper
method the harness reaches.

Not covered: merges from a focus inside the prefix (skipped, P1); `take_core`,
`borrow_raw_parts`, `ZipperConcrete` (`shared_node_id`, `is_shared`) and the
witness/conditional traits (no op uses them); a missing source root; `Cow::Borrowed`
prefixes (the source always passes an owned `Vec`).

Campaigns (after merging spec/coverage-models, run through the overlay
workstream's `known_dump.py` with `UNHIDE=1`, so no other entry can absorb a
read-side divergence): `--source prefix` 10 seeds x 10k = 100k inputs, 0 new
divergences, ~80% agree outright, known hits: P4 9360, `trie_ref_owned_empty_node`
4924, P5 stem 3550, P3 732, P2 337, P6 232, P5 off-prefix 140, finding-8 status
118, W1 27, `join_into_empty_dst` 22.  `--source empty` 5 x 20k = 100k, 0 new,
E1 21395, `trie_ref_owned_empty_node` 3143.  `native`, `map`, `tracker` 5k each:
0 new.
