# u-lattice: `ring.rs` (lattice impls, `AlgebraicResult`, `AlgebraicStatus`, `SetLattice`)

Util fuzzer (`--source util`) ops 30–59: `differential/src/utilfuzz/lattice.rs`
(decode, call, render) and `lean/PathMapModel/UtilFuzz/Lattice.lean` (the
model, op table, and the `#guard` law batteries).

## What is modelled

Every value op is checked on a table of 24 concrete types (`ltys`; 20 of them
also `DistributiveLattice`, `dtys`): `()`, `bool`, `u8`, `u16`, `u32`, `u64`,
`usize`, `Option<()>`, `Option<bool>`, `Option<u64>`, `Option<Option<bool>>`,
`Option<Option<u64>>`, `Box<u64>`, `Box<Option<bool>>`, `HashSet<u8>`,
`HashMap<u8, _>` of `()`, `bool`, `u64`, `HashSet<u8>`, `Option<u64>`,
`HashMap<u8, bool>`, `u8`, plus `Option<HashSet<u8>>`, `Box<HashMap<u8, u16>>`.

Each type has a meaning and, within the freedoms `AlgebraicResult`'s doc
gives (a clear identity bit asserts nothing; for a bottom result `None` and
`Identity` are both correct), the impl's stated choice:

| type | meaning | choice |
|---|---|---|
| `()` | the single present value | join/meet `Identity(3)`, subtract `None` |
| `bool` | Boolean algebra, `∨` / `∧` | one bit only: `SELF` when `self` is the answer, else `COUNTER` (never both); subtract: equal values cancel (`None`), else `Identity(SELF)` — which is `a ∧ ¬b` with `false` as bottom |
| `u8`…`usize` | opaque tokens; documented "GOAT trash" left projection | join `Identity(3)` if equal else `Identity(1)`; meet always `Identity(1)`; subtract (`u16`, `u64`) cancels equal values |
| `Option<V>` | `V` plus a new bottom (absent) | absent is the join identity (named by the other's bit; two absents `None`), meet annihilator; subtract from absent is `None`, subtracting absent `Identity(SELF)`; `join_into` overridden to do the same in place |
| `Box<V>` | `V` | |
| `HashSet<K>` | finite set: `∪`, `∩`, `\` | `None` iff empty; identity bits name every operand equal to the answer (maximal) |
| `HashMap<K,V>` | finite map, pointwise value op; a key whose value op annihilates is dropped | a bit iff no key is added/removed relative to that operand and every shared key's value result carries that bit |

`AlgebraicResult` / `AlgebraicStatus` methods are modelled from their docs
(`status` names `self` only; `invert_identity` swaps bits 0/1 and drops the
rest; `into_option`/`unwrap`/`unwrap_or`/`map_into_option`/`unwrap_or_else`
resolve an identity to `trailing_zeros(mask)`, with slice-index panics and
`unwrap(None)` rendered as `panic`; `AlgebraicStatus` is ordered
`Element < Identity < None`; `AlgebraicStatus::merge` is defined semantically:
annihilated iff both fields are, changed if a field changed or was *made*
absent, else unchanged — a `#guard` checks it against the crate's table).
`join_all` is the left fold of `pjoin` with the identity-bit bookkeeping its
code comments describe; on sets a `#guard` proves it equals the n-ary union
with maximal bits (except M1 below). `merge` is modelled by its case analysis
(the combinator is defined by it), and its *soundness* is checked separately
(L2).

Law batteries (`Laws.lawFails`, pinned per type by `#guard`): join/meet
idempotence, commutativity, associativity, absorption, distributivity; the
subtraction laws `a − a = ⊥`, `(a − b) ∧ b = ⊥`, `(a − b) ∨ (a ∧ b) = a`;
truthfulness of every identity mask (non-zero, arity-2 bits, `COUNTER`
never for subtract, both bits only for equal operands); the `IDEMPOTENT`
promise. Results: `()`, `HashSet`, `HashMap` of `()` / sets, `Option` of those:
everything holds. The integers (and `Option`/`HashMap` of them): commutativity
fails for join and meet, and `(a − b) ∧ b = ⊥` fails (left projection: the
documented choice). `bool` and containers of `bool`/integers: only the
`IDEMPOTENT` promise fails (L3).

`Basic.u64Ops` (the trie model's value instance) is checked against `u64Ty`:
same values, its bits a subset (it drops `COUNTER` on equal joins — allowed;
left unchanged since the trie model's statuses depend on it). Its doc comment
says `psubtract` returns `Element(*self)`; the crate and both models return
`Identity(SELF)` (stale comment in a shared file, not edited).

## Campaigns

`--source util`, seeds 11–14, 60 000 inputs each (240 000), `-j 8`: **0 new
divergences**. Known hits: u-mask M2 in ~2.9% of inputs (every one of seed
11's 1 731 masked inputs was re-run comparing only `ring_*` lines: no hidden
divergence in these ops), and L1 19× (all via `ring_pmeet!`, each checked to be
the operand swap). `--source native` and `--source map`, 3 000 each, seed 1:
0 new divergences (known hits only). Op mix in random inputs: every op appears, `skip:setlattice-meet-swap`
on ~23% of map meets, `skip:join-all-empty` on ~25% of `join_all`s.

## L1 (crate bug): `SetLattice` meet passes the value operands swapped

`set_lattice!`'s `pmeet` (so `HashMap<K, V>`, `HashSet<K>` and any user type
using the macro) iterates the smaller set and calls
`smaller_val.pmeet(larger_val)`. When `self` is not the smaller (`len(self) >=
len(other)`) that is `other's.pmeet(self's)`; the flags are swapped back
afterwards, so the *mask* is consistent, but the *value* comes from the
value type's `pmeet` with its arguments reversed. For a value type whose meet
is not symmetric — the integers' documented left projection, `bool`'s single
identity bit, `Option`s and maps of them — the answer at a shared key depends on
which map has more keys:

```rust
use pathmap::ring::*; use std::collections::HashMap;
let a: HashMap<u8, u64> = [(1, 1)].into();
let b: HashMap<u8, u64> = [(1, 2)].into();
let c: HashMap<u8, u64> = [(1, 2), (2, 0)].into();
assert_eq!(1u64.pmeet(&2), AlgebraicResult::Identity(SELF_IDENT));   // u64: self wins
assert_eq!(a.pmeet(&b), AlgebraicResult::Identity(COUNTER_IDENT));   // {1: 2}: other wins
assert_eq!(a.pmeet(&c), AlgebraicResult::Identity(SELF_IDENT));      // {1: 1}: self wins
// bool: {1:true}.pmeet({1:true}) is Identity(COUNTER) though true.pmeet(true) is Identity(SELF)
```

Why a bug: a map's meet is the pointwise meet of its values, `V::pmeet(self's,
other's)`; nothing documents a size-dependent orientation, and `PathMap<u64>`'s
own meet keeps `self`'s values. Same class as the trie's value-bias-by-layout
findings. Fix: call `pmeet(self_val, other_val)` in the original orientation
(or `.invert_identity()` the swapped call's result, as `trie_node.rs` does).

Handling: `skip:setlattice-meet-swap` on `ring_pmeet` / `ring_lref` when the
value type's meet is not symmetric (`Ty.meetSym` / `Val::MEET_SYM`), a key is
shared, and the swap happens (`Ty.hazard`, same predicate both sides). The
`ring_pmeet` op's first byte = 255 selects `ring_pmeet!`, the same op without
the skip. KNOWN `["src:util\n", " ring_pmeet! ret="]`; corpus
`lean/corpus/util-setlattice-meet-swapped-operands.bin` (the three calls above).

## L2 (latent API hazard): `AlgebraicResult::merge` is unsound for a meet

`merge` composes a pair's result from two field results. When one field
annihilated (`None`) and the other is `Identity(mask)`, it asks
`self_idents(0)` / `b_idents(0)` — argument **0**'s field — whether the
annihilated field was already absent, and if so returns `Identity(mask)` for
whatever arguments `mask` names. That is right for join (only absent ∨ absent
is absent, so both arguments' fields are absent) and for subtract (only `SELF`
is ever named), but a meet annihilates when *either* side is absent:

```rust
let (a1, a2): (Option<bool>, Option<u64>) = (Some(true), None);
let (b1, b2): (Option<bool>, Option<u64>) = (Some(false), Some(5));
let f1 = a1.pmeet(&b1).flatten();   // Identity(COUNTER): false
let f2 = a2.pmeet(&b2).flatten();   // None
let m = f1.merge(f2, |i| [a1, b1][i], |i| [a2, b2][i], |x, y| AlgebraicResult::Element((x, y)));
assert_eq!(m, AlgebraicResult::Identity(COUNTER_IDENT));
// claims the meet is (Some(false), Some(5)); it is (Some(false), None)
```

Not reachable through the crate today: its two `pmeet` callers (`PathMap`'s
`pmeet` in `trie_map.rs`) pass closures that always return `Some(..)`, so the
shortcut never fires, and `dense_byte_node.rs` uses `merge` only for join. The
closures are `FnOnce`, so `merge` cannot ask more than one argument: a fix
needs the API to change (or the doc to restrict `merge` to ops that only
annihilate from absent ∨ absent). In the Lean file: `mergeSound` (`#guard`
true for join and subtract, false for meet) and `mergeMeetUnsound`. The fuzzer
models `merge`'s case analysis, so it does not diverge on this.

## L3 (doc mismatch): `IDEMPOTENT = true` with non-`Identity(3)` self-results

`Lattice::IDEMPOTENT` (default `true`, never overridden) is documented as the
implementor asserting `pjoin(self) -> Identity(SELF_IDENT | COUNTER_IDENT)` and
`pmeet(self) -> Identity(SELF_IDENT | COUNTER_IDENT)`. `bool::pjoin(true,
true)` is `Identity(SELF)`; every integer's `pmeet(x, x)` is `Identity(SELF)`;
`Option`s and `HashMap`s of those inherit it. The constant is documented as
informational only (nothing consults it), so nothing misbehaves today; it
becomes a bug the day an "implementation shortcut" trusts it. (`None` for a
bottom, e.g. an empty set, is accepted by the battery: NOTE 1 lets `None` win.)
Repro: `<bool as Lattice>::IDEMPOTENT == true && true.pjoin(&true) ==
Identity(SELF_IDENT)`. Not a fuzzer divergence (the ops render the impls'
answers; the promise is checked by the `idempotent-promise` law).

## M1 reused (u-mask): `join_all` over bottoms

`ring_join_all` applies u-mask's `skip:join-all-empty` rule to every type:
when every argument is a bottom (its self-join is `None`: empty sets/maps,
absent options) and the crate answers `None` or an in-range identity, both
sides render the token. The Lean fold reproduces the parity exactly (`#guard`s
for `[∅]`, `[∅,∅]`, `[∅,∅,∅]`), so the skip only keeps the two models'
statements consistent.

## Open questions

* `bool`'s `psubtract` (equal values cancel) and its `pjoin`/`pmeet` (`∨`,
  `∧`, never `None`) agree only if `false` is read as a bottom that may be
  reported either as `None` or as an identity. If `false` is meant as a proper
  element, `false − false = None` is odd; if as the bottom, `false ∨ false`
  should "prefer" `None`. Modelled as implemented; both readings are sound.
* `invert_identity` of a mask with bits above 1 returns `Identity(0)`, which
  NOTE 2 forbids. The doc says it is for arity-2 results, so modelled as
  documented; arguably it should `debug_assert`.
* Integer `pmeet` reports `SELF` only even for equal operands while `pjoin`
  reports both; allowed, but inconsistent (feeds L3).

## Coverage: every public item of `src/ring.rs`

| item | op (selector) |
|---|---|
| `AlgebraicResult` derives `Clone`, `Copy`, `Debug`, `Default`, `PartialEq`/`Eq` | `ring_ar_query` (clone ==, `{:?}`), `ring_consts` (`default()`), `ring_ar_eq` (`==`, `!=`) |
| `is_none`, `is_identity`, `is_element`, `identity_mask`, `status` | `ring_ar_query` |
| `invert_identity` | `ring_ar_invert` |
| `map`, `as_ref` | `ring_ar_map` |
| `map_into_option`, `unwrap_or_else` | `ring_ar_closures` |
| `into_option`, `unwrap`, `unwrap_or` | `ring_ar_unwrap` |
| `merge` | `ring_ar_merge` (raw), `ring_merge_fields` (composite join/meet/subtract) |
| `from_status`, `flatten` | `ring_ar_status` (`flatten` also in `ring_merge_fields`) |
| `From<FatAlgebraicResult>` | via `ring_join_all` (`FatAlgebraicResult` is `pub(crate)`: not nameable outside) |
| `SELF_IDENT`, `COUNTER_IDENT` | `ring_consts` |
| `AlgebraicStatus` derives (incl. `Ord`), `is_*`, `merge` | `ring_status` (`cmp`, `max`, `{:?}`), `ring_consts` (`default()`) |
| `Lattice::pjoin` / `pmeet` for `()`, `bool`, `u8`, `u16`, `u32`, `u64`, `usize`, `Option<V>`, `Box<V>`, `HashMap`, `HashSet` | `ring_pjoin`, `ring_pmeet` (each type) |
| `Lattice::join_into` (default; `Option`'s override) | `ring_join_into` |
| `Lattice::join_all` (default) | `ring_join_all` |
| `Lattice::IDEMPOTENT`, `DistributiveLattice::IDEMPOTENT` | `ring_consts` (every type) |
| `DistributiveLattice::psubtract` for `()`, `bool`, `u16`, `u64`, `Option<V>`, `Box<V>`, `HashMap`, `HashSet` | `ring_psubtract` |
| `LatticeRef` for `&V`, `Option<&V>` | `ring_lref` |
| `DistributiveLatticeRef` for `&V`, `Option<&V>` | `ring_dref` |
| `SetLattice` for `HashSet<K>`: all 10 methods | `ring_setlattice_set` (and inside every set op) |
| `SetLattice` for `HashMap<K, V>`: all 10 methods | `ring_setlattice_map` (and inside every map op) |
| `HashSetIterWrapper` (`Iterator::next`) | `ring_setlattice_set` `iter`, every `HashSet` lattice op |
| `set_lattice!`, `set_dist_lattice!` | through the crate's `HashMap`/`HashSet` instantiations (a fuzzer-side instantiation would add only code compiled into `differential`) |
| `set_lattice_update_ident_flags_with_result`, `set_lattice_integrate_into_result` (`pub`, `#[doc(hidden)]`) | through the macros (every map/set join and meet) |
| `left_biased_pjoin`, `in_place_default_impl`, `set_lattice_subtract_element` | private; through the integer joins, `join_into`, map/set subtract |
| `Quantale`, `HeteroLattice`, `HeteroDistributiveLattice`, `HeteroQuantale`, `FatAlgebraicResult` | `pub(crate)`: not callable from outside (no impls in `ring.rs`) |

Not covered: `Lattice` impls for types outside `ring.rs` (`PathMap`, `ByteMask`,
nodes) belong to other groups.
