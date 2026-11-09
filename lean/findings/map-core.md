# Map fuzzer, `PathMap` surface and whole-map lattice ops (map-core)

Workstream `map-core`: map-fuzzer ops 0–19 (`MapFuzz/Core.lean`,
`differential/src/mapfuzz/core_ops.rs`) and 20–29 (`MapFuzz/Lattice.lean`,
`differential/src/mapfuzz/lattice.rs`).  The op tables and the semantic
decisions are in the headers of the two Lean files.

All three bugs below are about *what is reported*, not what is stored: the
maps themselves agreed with the model on every input run (~1.2M inputs, see the
end).

## Bug: `pjoin` / `psubtract` / `join_all` on `PathMap` report `Element` for a result equal to `self` [map_alg_ident_closures]

`impl Lattice for PathMap` (`pjoin`, `pmeet`) and `impl DistributiveLattice`
(`psubtract`) in `src/trie_map.rs` combine the root-node result and the
root-value result with `AlgebraicResult::merge`, passing ident closures
written as

```rust
|which_arg| match which_arg { 0 => Some(self.root().cloned()), 1 => Some(other.root().cloned()), .. }
|which_arg| match which_arg { 0 => Some(self.root_val().cloned()), 1 => Some(other.root_val().cloned()), .. }
```

`merge` asks the closure for the *other* component to decide whether a `None`
result on one side still leaves an identity ("if `self_ident.is_none()` →
`Identity(mask)`"), but these closures always return `Some(..)`, wrapping an
inner `None`.  So whenever one component's result is `None` — two maps with no
root value, which is nearly every map — the merge falls through to `merge_f`
and returns a fresh `Element`, even when the result is exactly `self`.

```rust
let mut a = PathMap::<u64>::new();
a.set_val_at([1u8], 5);
assert!(a.pjoin(&a).is_element());                 // should be Identity(SELF_IDENT)
assert!(a.psubtract(&PathMap::new()).is_element()); // should be Identity(SELF_IDENT)
```

Why a bug: the result is identical to `self`, and the crate's own
`map_root_value_test3` asserts `is_identity()` for `pjoin`/`psubtract` of maps
in this position (it passes only because its maps all have root values).
`join_all` inherits it through `FatAlgebraicResult::join`.  Contents are right;
`PathMap::join`/`subtract` (via `result_into_map`) are unaffected except for an
unnecessary clone.  Likely fix: return `self.root().cloned().map(Some)` style
(`None` when the component is absent) from the closures.

Frequency: about a fifth of all map-fuzzer inputs.  Behind the named skip
`skip:map-ident`: the class of a `pjoin`/`psubtract`/`join_all` result equal to
`self` renders as the skip token on both sides; the result dump is still
compared, and so is every other class.  No corpus file (the skip makes any input
agree); the snippet above is the reproducer.

## Bug: `Debug` for `PathMap` omits the root value [map_debug_omits_root]

`impl Debug for PathMap` walks `while rz.to_next_val()`, which starts *after*
the root, so the root value is never printed:

```rust
let mut b = PathMap::<u64>::new();
b.set_val_at([], 7);
b.set_val_at(b"x", 8);
assert_eq!(format!("{b:?}"), r#"{"x": 8}"#);  // the model says {"": 7, "x": 8}
```

Why a bug: a map's contents are its key/value pairs and `""` → 7 is one of them
(`iter()` yields it; a map holding only a root value prints as `{}`).  Minor:
diagnostics only.  Behind the named skip `skip:debug-root-val` (the `Debug` op
on a map with a root value), about a tenth of inputs otherwise.

## Bug / open question: `join_into` reports `Element` for an unchanged map when the source's layout differs [map_join_into_layout_status]

`PathMap::join_into` (and `ZipperWriting::join_into`, same behaviour) returns
`AlgebraicStatus::Element` although the destination's contents did not change,
when the source holds the same contents in a different node layout:

```rust
// a dangling path at a key that holds a value in the destination
let mut c = PathMap::<u64>::new();
c.set_val_at([1u8], 0);
let mut dng = PathMap::<u64>::new();
dng.create_path([1u8]);
assert_eq!(c.join_into(dng), AlgebraicStatus::Element);   // contents unchanged

// equal contents, source built with a sibling inserted and removed again
let p = [1u8, 0, 0, 0, 0];
let mut src = PathMap::<u64>::new();
src.set_val_at(p, 0);
src.set_val_at([1u8, 0, 0, 1, 0], 9);
src.remove([1u8, 0, 0, 1, 0]);
let mut x = PathMap::<u64>::single(p, 0);
assert_eq!(x.join_into(src), AlgebraicStatus::Element);   // contents unchanged
```

Corpus (`--source map`): `lean/corpus/map-join_into-status-dangling-at-valued-key.bin`,
`lean/corpus/map-join_into-status-after-sibling-removed.bin`.  KNOWN entry keyed
`src:map` + `join_into ret=Identity/` (model) + `join_into ret=Element=SELF/`
(crate): the crate side tags `Element=SELF` only when the status is `Element`
and the map is unchanged, so the entry cannot absorb a content divergence.
About 0.06% of inputs.

Open question: `AlgebraicStatus`'s doc says lower values are "still correct"
and that `join` may return `Element` "if the internal representation was
changed".  If adopting the source's node shape counts, this is allowed
imprecision.  The model follows the zipper fuzzer's `join_into` rule (Identity
iff unchanged), so it is recorded rather than accepted.

## Semantic decisions (also in the Lean headers)

* `pmeet`/`meet`: dangling paths in a meet result are unspecified (the fvc meet
  rule; `PathMap::meet` has no prune flag), so results are rebuilt from their
  values on the crate side, and a meet's class is decided by values
  (`Identity` iff values equal `self`'s; `Element` is then also accepted).
* `AlgebraicResult` rendering: class = `status()` with an empty result shown as
  `None` ("None should take precedence"); `SELF_IDENT` compared exactly;
  `COUNTER_IDENT` / other mask bits are sound-only (checked on the crate side,
  `UNSOUND-MASK` otherwise); accessors (`is_*`, `identity_mask`, `unwrap`,
  `unwrap_or`, `unwrap_or_else`, `into_option`, `status`) are checked for
  consistency (`ACCESSOR-MISMATCH`) and used to resolve the map.
* `is_shared` is documented as unreliable, so it is not compared.  Equal
  `shared_node_id`s must mean equal contents (checked after every `clone`);
  copy-on-write is checked by the later ops and the final dumps.
* `merkleize` must preserve contents; its hash is layout-dependent and not
  compared.
* `get_val_mut_at` never creates a path; the `_with_at` closure runs exactly
  when there is no value.

## Covered / not covered

Answer-checked now: `get`, `insert`, `remove`, `contains`, `path_exists_at`,
`contains_path`, `val_at`, `get_val_at`, `ZipperValues::val`, `remove_val_at`
(both prunes), `get_val_mut_at`, `get_mut`, `get_val_or_set_mut_at`,
`get_val_or_set_mut_with_at`, `remove_branches_at` (both prunes),
`prune_path`, `create_path`, `val_count`, `goat_val_count`, `is_empty`,
`merkleize` (content only), `iter`, `Debug` (maps without a root value),
`FromIterator` (owned pairs, `&(K, V)`, `&[u8]` into `PathMap<()>`),
`IntoIterator` (of a clone and of the map itself), `clone`,
`shared_node_id` (soundness), `single`, `From<(K, V)>`, `single_in`, `new`,
`default`, `read_zipper_at_borrowed_path`, `read_zipper_at_path`,
`into_read_zipper` + `ReadZipperOwned::into_map`, `into_write_zipper` +
`WriteZipperOwned::into_map`; `PathMap::join` / `meet` / `subtract` /
`restrict`; `Lattice::pjoin` / `pmeet` / `join_into` / `join_all`,
`DistributiveLattice::psubtract`; `AlgebraicResult` accessors.

Not covered: `Quantale::prestrict` (`pub(crate)`; only through
`PathMap::restrict`); `u16`/`bool`/`u8`/`u32`/`usize` lattice impls (need a
different value type; the map fuzzer is `u64`-only); `new_from_ana` (Morph
group); `zipper_head` / `into_zipper_head` (Head group); `trie_ref_at_path`,
`read_zipper_with_buffer`, `write_zipper_with_buffer`, `write_zipper_at_path`
(zipper/source workstreams); `is_shared`'s value; `merkleize`'s hash and
counters; `Debug`'s non-ASCII fallback (paths are bytes 0–3, always valid
UTF-8).

## Campaigns

Before merging spec/coverage-models (ops 0–29 only): seeds 11, 12, 13 at 200k
each and seed 14 at 100k with `--maxlen 1500`: 0 new divergences, only
`map_join_into_layout_status` (195 / 209 / 197 / 714).  After the merge (ops
0–48 with map-serial): seeds 21 (20k), 22, 23 (200k each): 0 new divergences;
known = this group's `join_into` entry plus map-serial's.  `--source native`
20k: 0 new.
