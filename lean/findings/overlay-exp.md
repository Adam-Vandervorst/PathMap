# Workstream overlay-exp: `OverlayZipper`, `DiffZipper`, `FullZipper`/`NullZipper`

Sources added: `overlay`, `overlay-filter`, `diff` (`differential/src/sources/{overlay,diff}.rs`,
`lean/PathMapModel/Sources/{Overlay,Diff}.lean`).  Map-fuzzer ops 70–79 (`Exp`) stay `nop`: see
"Not reachable" below.

## What the sources are

### `overlay` / `overlay-filter`

`OverlayZipper` over `a = map1.read_zipper_at_path(root1)` and
`b = snap0.read_zipper_at_path(root0)`, where `snap0 = map0.clone()` right after the header (the
write zipper's later edits to map0 never reach the overlay).  The sources are at **different roots**
on purpose: that is the crate's `overlay_sources_at_different_roots` case, and it makes the two
halves independent.  The overlay is presented at root1.

* `overlay`: `OverlayZipper::new` (default mapping `a.or(b)`).
* `overlay-filter`: `OverlayZipper::with_mapping(a, b, b_unless_a)`, `b`'s value only where `a`
  has none.  A mapping that removes values, so it checks argument order, locations that exist with
  no value, and every op that must look at the *overlay's* values rather than the sources'.

Model (`Sources/Overlay.lean`): the union of the two subtries' locations (dangling paths of either
source included), value `mapping (valA p) (valB p)` at every location, the root included (root value
= `mapping (map1 @ root1) (map0 @ root0)`).  Every op is then the native `Zip` spec on that trie.
This is read off the crate's accessors and doc comments: `path_exists = a || b`,
`child_mask = a | b`, `val = mapping(a.val(), b.val())`, and `is_val` is defined as
`val().is_some()` precisely because "the mapping function has the ability to nullify the value".
`descend_to_val` stops at the first location strictly below the focus where the **overlay** has a
value, as the crate's own `overlay_descend_to_val_skips_values_filtered_by_mapping` test requires.

Capabilities, from the traits it implements (`Zipper`, `ZipperMoving`, `ZipperPath`,
`ZipperValues`, `ZipperValuesAt`, `ZipperIteration`): no fork, make_map, merge, get_val,
get_val iteration; `val_count` is `todo!()` so `valCount = false`.

`OverlayZipper` has no `ZipperAbsolutePath`, which the harness requires.  `Abs` in overlay.rs adds
it from outside (`origin = root1 ++ path()`, refreshed after every move) and forwards every other
trait method, overridable defaults included, so nothing falls back to a default the overlay would
not have used.

### `diff`

`pathmap::utils::debug::DiffZipper` is public (`pub mod utils` → `pub mod debug` →
`pub use DiffZipper`).  It is a debugging zipper: it runs two zippers in lockstep and `assert_eq!`s
every answer, returning the first one's.  Source: `DiffZipper::new(map1.read_zipper_at_path(root1),
map1.clone().read_zipper_at_path(root1), false)`.  View: native (map1 at root1).

`DiffZipper` forwards `Zipper`, `ZipperMoving` (with `val_count`), `ZipperPath`,
`ZipperAbsolutePath`, `ZipperPathBuffer`, `ZipperIteration` and `ZipperProduct`, but has **no
`ZipperValues`/`ZipperValuesAt`**.  The adapter `DiffSrc` answers `val`/`val_at` with map1's value at
the `DiffZipper`'s reported `origin_path()` (`++ k`), so those answers check the path, not a value
method (there is none).  Caps: valCount true, everything else false.

## Crate bugs

### 1. `OverlayZipper::ascend_until` / `ascend_until_branch` stop only where a *source* stops

KNOWN key `["src:overlay", "ascend_until"]`, note `[overlay_ascend_until_union_branch]`.
Corpus: `lean/corpus/overlay-ascend_until-misses-union-branch.bin` (`--source overlay`),
`lean/corpus/overlay-filter-ascend_until-stops-at-filtered-value.bin` (`--source overlay-filter`).

Each source ascends to *its own* nearest value/branch and the overlay takes the shallower stop.
Two consequences:

* **Branches formed by the union are climbed past.**  `a = {[1,0,0,0]}`, `b = {[1,1,0,0]}`: `[1]`
  has two children in the overlay (`child_count() == 2`) but one in each source, so from `[1,0]`
  `ascend_until()` returns 2 and lands at the root instead of returning 1 at `[1]`.  Same for
  `ascend_until_branch()`.  Hits the default mapping too (127 of 20 000 random inputs).
* **A value the mapping filtered out stops the ascent.**  With `b_unless_a`,
  `a = {[2]=0, [2,0,0,0,0]=0}`, `b` empty: the overlay has no values, yet from `[2,0,0]`
  `ascend_until()` stops at `[2]` (ret 2) instead of the root (ret 3).

```rust
let mut a = PathMap::<u64>::new(); a.set_val_at(&[1u8, 0, 0, 0], 0);
let mut b = PathMap::<u64>::new(); b.set_val_at(&[1u8, 1, 0, 0], 0);
let mut z = OverlayZipper::new(a.read_zipper(), b.read_zipper());
z.descend_to(&[1u8, 0]);
assert_eq!(z.ascend_until(), 1);   // fails: 2, z.path() == []
```

Why a bug: `ZipperMoving::ascend_until` is "ascend to the nearest ancestor that is a value or a
branch" of the zipper's own trie, and the overlay's trie is the union; its own `child_count()` at
`[1]` says 2.  The filtered-value half is the same class as the `descend_to_val` bug fixed on
`fix/overlay-zipper-root-and-descend-to-val` (PR #144, commit 7eed493: "skips values filtered by
mapping"); `ascend_until` was not touched there.

### 2. `OverlayZipper::descend_until` stops at a source value the mapping filtered out

KNOWN key `["src:overlay-filter", "descend_until"]`, note `[overlay_descend_until_filtered_value]`.
Corpus: `lean/corpus/overlay-filter-descend_until-stops-at-filtered-value.bin`.

`descend_until_observed` drives each source's `descend_until_max_bytes_observed`, which stops at
that source's values; a stop is taken as the overlay's stop without asking the overlay whether it
has a value there.  Same trie as above (`a = {[2]=0, [2,0,0,0,0]=0}`, `b` empty, `b_unless_a`):
`descend_until()` stops at `[2]` (`is_val() == false`, `child_count() == 1`) instead of descending
to `[2,0,0,0,0]`.  `descend_until_max_bytes` inherits it.  The default mapping cannot show it (it
has a value wherever either source does), and union branches are handled correctly (the
common-prefix logic stops at them).

```rust
fn b_unless_a<'a>(a: Option<&'a u64>, b: Option<&'a u64>) -> Option<&'a u64> { if a.is_some() { None } else { b } }
let mut a = PathMap::<u64>::new(); a.set_val_at(&[2u8], 0); a.set_val_at(&[2u8, 0, 0, 0, 0], 0);
let b = PathMap::<u64>::new();
let mut z = OverlayZipper::with_mapping(a.read_zipper(), b.read_zipper(), b_unless_a);
z.descend_until();
assert_eq!(z.path(), &[2u8, 0, 0, 0, 0]);   // fails: [2]
```

Why a bug: "descends until a branch or a value is encountered"; the overlay defines its own value
(`is_val` via the mapping) and the crate already fixed `descend_to_val` for the same reason.

**Both bugs explain every divergence.**  With a scratch (uncommitted) adapter that replaced the
overlay's `ascend_until`, `ascend_until_branch` and `descend_until_observed` by the obvious
byte-at-a-time versions over the overlay's own `is_val`/`child_count`, 20 000 inputs on each of
`overlay` and `overlay-filter` (seed 2) agreed with the model with zero divergences and zero known
hits.

## Not reachable: `FullZipper`, `NullZipper` (map ops 70–79)

`src/experimental.rs` declares `struct FullZipper` and `struct NullZipper` without `pub`, inside
`pub mod experimental`, and nothing public constructs or returns one.  They cannot be named from
outside the crate, so `MapFuzz/Exp.lean` / `mapfuzz/exp.rs` stay `nop` (comment added at both).
Reading the code anyway, for whoever makes them public:

* `FullZipper` (every path exists, `is_val()` is `true` everywhere but it has no `ZipperValues`):
  its `to_prev_sibling_byte` decrements the **first** byte of the path rather than the last
  (`self.path.first_mut()`), and `descend_until`/`ascend_until`/`ascend_until_branch` are marked
  "not sure?" in the source (the infinite trie has 256 children everywhere, so `descend_until` should
  arguably not move at all; it descends one `0` byte).
* `NullZipper`: `get_val_or_set_mut[_with]` leak a `Box` per call; `zipper_head` is `todo!()`;
  `take_root_prefix_path`/`alloc` are `unimplemented!()`.

## Open questions

* A mapping can return a `&'static` value where neither source has one (the signature allows it).
  The overlay would then report `is_val() == true` at a location where `path_exists()` is false.
  The model's mapping is only ever applied at existing locations; neither variant fuzzed here does
  this.  Is that mapping legal?
* `val_count` is `todo!()`.  The obvious meaning is the number of overlay values below the focus.

## Framework changes (shared files)

* `lean/differential.py`, `record()`: `classify` now sees the message prefixed with
  `src:<source>\n`, so a KNOWN entry for a virtual source's own defect can be keyed on its source
  and cannot hide the same-looking divergence of another source.  Two overlay entries added just
  before the generic `["ascend_until"]` entry.
* **The generic `["ascend_until"]` KNOWN entry (write-zipper bug `ascend_until_wz`) matches any
  `ascend_until` divergence, read side included.**  Before the overlay entries existed, all 21
  overlay divergences in a 3 000-input run were absorbed by it.  Every source with a read-side
  `ascend_until` bug will be silently "known".  I checked for this with a scratch wrapper around
  `differential.classify` that reports any known-classified message whose `R=` fingerprint differs
  between model and crate; the overlay/diff campaigns below were run through it with those
  re-reported as failures.  Recommend the other workstreams do the same, or that the entry be
  narrowed.

## Campaigns

All through the `R=`-unhiding wrapper (a known entry hit with a differing read side counts as a
new divergence unless it is one of the two overlay entries).

| source | inputs | agree | known | new |
| --- | --- | --- | --- | --- |
| `overlay` (seeds 11–15 × 20 000) | 100 000 | 99 474 | 526 (bug 1) | 0 |
| `overlay-filter` (seeds 11–15 × 20 000) | 100 000 | 98 233 | 1 767 (bugs 1, 2) | 0 |
| `diff` (seeds 11–15 × 20 000) | 100 000 | 100 000 | 0 | 0 |
| `overlay`, bugs patched in a scratch adapter (seeds 2, 11–13) | 80 000 | 80 000 | 0 | 0 |
| `overlay-filter`, bugs patched (seeds 2, 11–13) | 80 000 | 80 000 | 0 | 0 |

Plus earlier exploratory runs (seeds 1–3, ~49 000 inputs) with the same classes and nothing else.

`native`, `map`, `tracker`: 10 000 each, seed 1, no new divergences.

## Coverage

Answer-checked now: every `OverlayZipper` method except `val_count` (both constructors, the
default `identity_ref` mapping and a custom one, every `ZipperMoving`/`ZipperIteration` method,
`val`, `val_at`), and every `DiffZipper` method in `Zipper`, `ZipperMoving`, `ZipperPath`,
`ZipperAbsolutePath`, `ZipperIteration`.

Not covered: `OverlayZipper::val_count` (`todo!()`), `DiffZipper`'s `ZipperPathBuffer` and
`ZipperProduct` forwarding, `log_moves = true` (prints only), `FullZipper`, `NullZipper`.
