# u-mask: `ByteMask`, `BitMask`, and the rest of `src/utils/mod.rs`

Util fuzzer (`--source util`) ops 0–29: `differential/src/utilfuzz/mask.rs`,
`lean/PathMapModel/UtilFuzz/Mask.lean` (the op table and the semantic
decisions are in that file's header).

## The model

A `ByteMask`, and a `[u64; 4]` used through `BitMask`, is a **set of bytes**.
The model is `Basic.lean`'s `ByteMask` (ascending, duplicate-free list of
members), extended in `UtilFuzz/Mask.lean` with the set algebra (`union`,
`inter`, `diff`, `symm`, `compl`, ranges, `subsetOf`) and the queries
(`indexOf`, `indexedBitRev`, `runs`, `words`/`ofWords`).  Every answer is the
set-level meaning: `or` is union, `andn` difference, `index_of b` the number of
members below `b`, `range_iter` the maximal runs, and so on.  The raw words
appear only where the API exposes them (`into_inner`, `AsRef`, `Borrow`,
`From`), against the layout `from_range`'s doc states.  The harness builds and
renders masks with its own word arithmetic, never the crate's methods.

`AlgebraicResult` is rendered by `showAlgResult` / `show_alg_result`
(`UtilFuzz/Base.lean`, `utilfuzz/mod.rs`) for the u-lattice workstream to reuse:
`None`, `Identity(<mask>)`, `Element(<v>)`.

Key decisions (details in the `Mask.lean` header):

* Lattice ops (`pjoin`/`pmeet`/`psubtract`) answer the **strongest result the
  `AlgebraicResult` contract allows**: `None` iff the result is empty (None
  "should take precedence"), else `Identity` with `SELF_IDENT` / `COUNTER_IDENT`
  for every operand equal to the result, else `Element`.  The contract permits
  reporting fewer identities; a bit set always knows, and the crate does report
  them all.  `#guard`s check the model honours the contract (non-zero mask, in
  arity, two bits only for equal operands, `psubtract` never `COUNTER_IDENT`)
  and `IDEMPOTENT`'s promises.
* `join_into` is `self := self ∪ other` with the `AlgebraicStatus` meaning
  (Identity = unchanged).  `join_all` is the n-ary version of the above
  (bit `i` for every argument equal to the union).
* An inclusive range is the set its `RangeInclusive` contains: `a..=b` with
  `a > b`, and a range iterated to its end, are empty.
* `Debug for ByteMask` is std's `debug_set` format; `ByteMaskBinaryFmt` is bit
  255 first, `Display` grouped by 8 (crate test pins 256 / 287 chars).  The
  iterators' `Debug` prints `type_name`, which std does not promise; the model
  pins today's text.

`#guard` batteries in `Mask.lean`: Boolean-algebra laws (commutativity,
absorption, De Morgan, distributivity, associativity), canonical form
preserved, words round trip and layout, query consistency (`index_of` ↔
`indexed_bit`, `next_bit`/`prev_bit` as least/greatest member beyond,
`indexed_bit::<false>` as the mirror, runs partition the mask), `subset` rows,
`from_range` edge cases, format lengths, the crate's own lattice unit test,
`join_into` = `pjoin` in place, `join_all [a, b]` = `pjoin a b`.

## M1: `join_all` over empty masks answers by the parity of the argument count

`Lattice::join_all` (the trait default in `ring.rs`) on `ByteMask` or
`[u64; 4]` with every argument empty:

| arguments | crate | model |
|---|---|---|
| `[∅]` | `Identity(1)` | `None` |
| `[∅, ∅]` | `None` | `None` |
| `[∅, ∅, ∅]` | `Identity(4)` | `None` |

`FatAlgebraicResult::join` turns `pjoin(∅, ∅) = None` into "no element", and
the next argument then restarts the result as `Identity(1 << i)` of that
(empty) argument.  `AlgebraicResult`'s doc says `None` *should* take
precedence over `Identity` but that either "can be considered correct", so this
is not a contract violation, only an inconsistency: the same set of operands
gives different results depending on how many there are.  Recorded, not
treated as a crate bug.

Handling: `skip:join-all-empty` (op 25, both sides, documented at both sites
and in `lean/README.md`'s skip table).  When every argument is empty and the
crate answers `None` or an in-range `Identity`, both sides render the token; an
`Element` or an out-of-range identity bit still diverges.  Corpus:
`lean/corpus/util-join_all-empty-parity.bin` (`--source util`; three `join_all`
calls of 1, 2, 3 empty masks).  Standalone:

```rust
use pathmap::{ring::{AlgebraicResult, Lattice}, utils::ByteMask};
let e = ByteMask::EMPTY;
assert_eq!(<[u64; 4] as Lattice>::join_all(&[e]), AlgebraicResult::Identity(1));
assert_eq!(<[u64; 4] as Lattice>::join_all(&[e, e]), AlgebraicResult::None);
assert_eq!(<[u64; 4] as Lattice>::join_all(&[e, e, e]), AlgebraicResult::Identity(4));
```

The same mechanism applies to every `Lattice` type using the default
`join_all`, so the u-lattice workstream may see it on other types.

## M2: the inclusive-range edits act on an exhausted `RangeInclusive`

`ByteMask::set_inclusive_bit_range` / `clear_` / `toggle_` take a
`RangeInclusive<u8>` and read only `start()` and `end()`.  A `RangeInclusive`
that has been iterated to its end is empty (`is_empty()` is true; std says its
`start()`/`end()` are then unspecified, and today they are both `end`), but
the methods act on bit `end`.  `ByteMask::from(range)` / `from_range` go
through `RangeBounds`, which reports such a range as empty, and get it right,
so the two halves of the API disagree on the same value.  Minor (who passes a
spent range?), but the method denotes "the bits in this range", and this range
has none.

Corpus `lean/corpus/util-incl_range-exhausted-range.bin` (`--source util`);
KNOWN `[u-mask M2: incl_range_exhausted]`, keyed on op 20's `x` shape tag so
it cannot cover the other range shapes.  Standalone (passes on the crate):

```rust
use pathmap::utils::{BitMask, ByteMask};
let mut r = 5u8..=9;
for _ in r.by_ref() {}
assert!(r.is_empty());
assert_eq!(ByteMask::from(r.clone()), ByteMask::EMPTY);   // honoured here
let mut m = ByteMask::EMPTY;
m.set_inclusive_bit_range(r);
assert!(m.test_bit(9));                                    // but bit 9 is set here
```

Fix: return early on `range.is_empty()` (which also covers M3).

## M3 (debug builds only): an empty `a..=b` with `a > b` trips a `debug_assert`

`BlockRange::new` has `debug_assert!(start <= end)`, so
`m.set_inclusive_bit_range(5..=4)` panics in a debug build
(`src/utils/mod.rs:362`).  `5..=4` is an ordinary empty `RangeInclusive`, and
`from_range` documents `start >= end` as the empty mask; in release the masks
come out unchanged, which is the right answer (the fuzzer checks release on
`a > b`, op 20 shape `g`).  If `start <= end` is meant as a precondition, it is
undocumented.  Same standalone, debug build:

```rust
let mut m = pathmap::utils::ByteMask::EMPTY;
m.set_inclusive_bit_range(5..=4);   // debug: "assertion failed: start <= end"
```

## Open questions

* **How strong must lattice results be?**  The contract permits `Identity`
  bits to be missing and `Identity` in place of `None`.  The model requires the
  strongest answer (all identities, `None` for an empty result).  Every binary
  op agrees; only `join_all` over empty arguments (M1) uses the latitude.
* **The iterators' `Debug`** prints `core::any::type_name`, not promised
  stable by std; pinned as `pathmap::utils::ByteMaskIter` /
  `ByteMaskRangeIter`.

## Coverage: every public item in `src/utils/mod.rs`

Op numbers are util-fuzzer selectors.  "Both" = the `ByteMask` impl and the
`[u64; 4]` impl, each called and checked separately.

| item | op |
|---|---|
| `ByteMask` derives: `Clone`, `Copy`, `Default`, `PartialEq`/`Eq` | 3 (`clone() ==`, `default()`, `==`), copies everywhere |
| `ByteMask::EMPTY`, `FULL`, `new` | 26 |
| `ByteMask::subset` | 1 |
| `ByteMask::from_range` at `Range`, `RangeInclusive` (incl. exhausted), `RangeFrom`, `RangeTo`, `RangeToInclusive`, `RangeFull`, `(Bound, Bound)` ×3 | 2 |
| `into_inner` | 3 |
| `iter` | 18, 26 |
| `range_iter` | 19, 26 |
| `fmt_binary`; `Debug` / `Display for ByteMaskBinaryFmt` | 22 |
| `index_of` | 15 |
| `indexed_bit::<true>`, `::<false>` | 16 |
| `next_bit`, `prev_bit` | 17 |
| `set_`/`clear_`/`toggle_inclusive_bit_range` | 20, 28 |
| `Debug for ByteMask` (`{:?}` and `{:#?}`) | 21 |
| `BitMask` (both): `count_bits`, `is_empty_mask` | 4 |
| `BitMask` (both): `test_bit` | 5 |
| `BitMask` (both): `set_bit`, `clear_bit`, `toggle_bit` | 6, 7, 8 (and 28 for `ByteMask`) |
| `BitMask` (both): `make_empty` | 9 |
| `BitMask` (both): `or`, `and`, `xor`, `andn`, `not` | 10, 11, 12, 13, 14 |
| `Borrow<[u64; 4]>`, `AsRef<[u64; 4]> for ByteMask` | 3; `AsRef` also as `join_all`'s argument bound in 25 |
| `From<u8>` | 1 |
| `From<Range<u8>>`, `From<RangeInclusive<u8>>` | 2 |
| `From<[u64; 4]> for ByteMask`, `From<ByteMask> for [u64; 4]` | 3 |
| `FromIterator<u8>` | 0 |
| `PartialEq<ByteMask> for [u64; 4]`, `PartialEq<[u64; 4]> for ByteMask` | 3 |
| `BitOr` (owned and `&`), `BitOrAssign`, `BitAnd` (owned and `&`), `BitAndAssign`, `BitXor`, `BitXorAssign`, `Not` | 10, 11, 12, 14, 28 |
| `Lattice` (both): `pjoin`, `pmeet`; `DistributiveLattice` (both): `psubtract` | 23 |
| `Lattice` defaults instantiated at both: `join_into` | 24 |
| `Lattice` defaults instantiated at both: `join_all` | 25 (over `ByteMask` via `AsRef<[u64; 4]>`, and over a local `AsRef<ByteMask>` wrapper) |
| `ByteMaskIter`: `new`, `From<[u64; 4]>`, `From<ByteMask>`, `next` (fused), `Debug` | 18, 26 |
| `ByteMaskRangeIter`: `new`, `From<[u64; 4]>`, `From<ByteMask>`, `next` (fused), `Debug` | 19, 26 |
| `IntoByteMaskIter` (deprecated) for `ByteMask`, `[u64; 4]`, `&[u64; 4]` | 18 |
| `empty_mask` (deprecated) | 26 |
| `find_prefix_overlap` (deprecated re-export of `fast_slice_utils`) | 27, strings up to 71 + 39 bytes to reach the SIMD paths |

Not covered, and why:

* `Lattice::IDEMPOTENT` / `DistributiveLattice::IDEMPOTENT` on both: an
  associated `const` (the default `true`), "informational only" per its doc;
  nothing to call.  The `#guard`s check the promise it makes holds for the model,
  and op 23 with `b := a` (pair shape 0) checks the crate keeps it.
* `ByteMaskBinaryFmt`'s derived `Clone`/`Copy`: derives, no behaviour.
* `BlockRange`, `bitmask_algebraic_result`, `u64_4_raw_set_bit` /
  `u64_4_raw_clear_bit`, `ByteMask::SUBSET`: private (all reached through the
  public ops above).
* `utils::debug::DiffZipper`: a zipper; the `diff` read source covers it
  (overlay-exp.md).
* `utils::debug::CatamorphismDebug::into_cata_jumping_cached_fallible_debug`
  (impls for `PathMap` and for zippers): needs a trie and the jumping-cata
  model, which live in the map fuzzer's morph group (`mapfuzz/morph.rs` ops
  52/53 already check `into_cata_jumping_cached(_fallible)`; this is the same
  fold with the full path passed to the closure).  It belongs there as one
  more flavour; that file is not this workstream's.  Not done.
* `utils::debug::render_debug_path`, `PathRenderMode`: `pub(crate)`.
* `utils::ints`: the u-ints workstream.

## Campaigns

`--source util`, `-j 6`:

| seeds | inputs | maxlen | result |
|---|---|---|---|
| 1, 2 | 40k | 300 | all agree (before ops 2/20 gained the empty/exhausted range shapes) |
| 3–7 | 500k | 300 | all agree (same) |
| 8, 9 | 100k | 3000 | all agree (same) |
| 21–25 | 500k | 300 | 0 new; ~4.3% hit M2 (the only KNOWN hit) |
| 26, 27 | 100k | 3000 | 0 new; ~23% hit M2 |

A KNOWN hit stops the comparison of that input at the hit, which is why the
first 640k inputs (without the exhausted-range shape) matter: every other op
ran unmasked there.  Sanity, unchanged framework: `--source native` 5k (0 new;
known: trie_ref_owned_empty_node, wz_try_borrow_focus_below_dangling),
`--source map` 3k (0 new; known map-serial / map-core entries).

During development the only divergences were M1 (before the skip) and M2;
no model mistakes surfaced in the campaigns.
