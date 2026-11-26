# `ProductZipper` and `ProductZipperG` (workstream `product`)

Sources: `--source product` (`ProductZipper`) and `--source productg`
(`ProductZipperG`) are the campaign sources; `--source product-full` /
`productg-full` are the same zippers without this source's two skips, and
reproduce everything below.  Rust: `differential/src/sources/product.rs`;
model: `lean/PathMapModel/Sources/Product.lean`; standalone reproducers:
`cargo run --release -p differential --bin product_repros` (P1–P6 below).

## Set-up

Both zippers are built over the same three factors:

* primary: `map1.read_zipper_at_path(r)`, where `r` is the longest prefix of
  root1 at which map1 has children (`[]` if none).  Not root1 itself: the
  header always creates root1, and a random root1 is nearly always a fresh
  dangling leaf, so the primary would almost always be empty.  With `r`, the
  primary holds root1 as a dangling leaf (a joint), and the childless primary
  root is left to inputs where map1 is empty.
* a `PathMap` clone of map0 taken right after the header, before any op runs
  (it shares structure with the live map0 the write zipper then mutates);
* map1 at its root.

Every secondary is a root-level zipper (clear of the documented "secondary
factors must be at node roots" panic).  `ProductZipperG::new(primary, [..])`.

## The semantics modelled

One view for both zippers (they are two implementations of one meaning):

* `prod [t] = t`; `prod (t :: fs) = t` with `prod fs` grafted below every
  **leaf** of `t`: every existing path with no children, valued or dangling.
* The joint keeps `t`'s value or its absence; the root value of `prod fs` is
  never visible (`enroll_next_factor`: "the value from the earlier zipper
  takes precedence"; `ProductZipperG`'s `factor_idx(true)` does the same).
* A valued path with children is not a joint (`product_zipper_test3/4`).
* **A factor's root is a leaf like any other path when it has no children.**
  So a childless primary root is a joint, and a factor with nothing below its
  root is transparent (the next factor is grafted at the same place).

The view is map1 with everything strictly below `r` replaced by
`prod [map1.subtrie r, snap, map1]`, rooted at `r`.  Every read, movement and
iteration op is the native read zipper's spec on that view; `val_at(p)` is
`descend_to(p); val()` on it.

`ZipperProduct` is compared every step (`P<factor_count>:<focus_factor>:<path
indices above the focus>`, `Product.info`): the factors entered strictly above
the focus, where the walk along the focus path enters factor k+1 at the depth
the existing part of the path in factor k ends at a leaf (an empty factor is
entered and left at the same depth, so its start repeats).  At a joint the focus
is in the earlier factor (whose value it shows).

Capabilities (from the trait impls): neither type has `ZipperForking`,
`ZipperSubtries` (the closing comment of `product_zipper.rs` says why it cannot
be a merge source) or `ZipperReadOnlyIteration`, so `dump`, `make_map`, every
merge and `to_next_get_val` read `skip:product[g]`.  `ProductZipper` has only
`ZipperReadOnlyConditionalValues`, checked in `get_val_agrees` as
`get_val_with_witness` against `val` (the `at` component is `val_at`, there is
no witnessed `get_val_at`); `ProductZipperG` has `get_val`/`get_val_at`.
`ProductZipper::val_count` is checked; `ProductZipperG::val_count` is
`unimplemented!()` (`Caps.valCount = false`).

## Open question: the empty factor (settled as above, flagged for review)

The crate never says what a factor with no children at its root does.  Two
readings: (A) its root is a leaf, so the factor is transparent and a childless
primary root is a joint; (B) a factor's root is never a joint, so an empty
factor ends the product there and a childless primary presents nothing.

The model takes (A), because:

* both implementations' own stitch test is "path exists and has no children"
  with no exception for a factor's root (`ensure_descend_next_factor`,
  `enter_factors`); each of them applies it at a factor root in some code path
  (P1, P2 below), so neither consistently implements (B) either;
* (A) is associative (`prod2 (prod2 a b) c = prod2 a (prod2 b c)`, checked over
  a battery in `Product.lean`); (B) is not (with `b` empty, left-nesting grafts
  `c` below `a`'s leaves, right-nesting does not);
* the doc's "extending each path in a primary trie with the root of the next
  secondary trie": a primary rooted at a leaf has exactly one path, the empty
  one;
* the relation to Composition below (prefix-free `T1 = {[]}` gives
  `keys T2`) only holds under (A).

The `dependent` workstream reached the same reading for
`DependentProductZipperG` independently.

## Crate bugs

Each is reproduced by `product_repros` and, through `product-full` /
`productg-full`, by a corpus file.

### P1. A childless primary root is not entered, or only until `reset` (both)

`ProductZipper::new` / `ProductZipperG::new` never test the primary's root.
`ProductZipper` enters the next factor there only as a side effect of a
`descend_first_byte` that fails (`ensure_descend_next_factor` after the core
returns `None`), after which the same root reports the secondary's children;
`reset` clears `factor_paths` and the root is childless again.
`ProductZipperG` reports a childless root, yet `descend_to(x)` enters the
factor and lands on an existing path (`enter_factors` runs at the top of
`descend_to_existing`).  Observations at one focus depend on history either
way, so this is a bug under either reading.  Corpus:
`lean/corpus/product-childless-primary-root-not-entered.bin` (both `-full`
sources).  Same defect as the dependent workstream's D1.

### P2. An empty factor is a dead end (`ProductZipper`) or entered lazily (`ProductZipperG`)

`ProductZipper::ensure_descend_next_factor` refuses to enroll a factor at the
depth where the last one was enrolled ("We don't want to push the same factor
on the stack twice"), so after an empty factor the next one is never entered.
`ProductZipperG::enter_factors` enters one factor per call, so after an empty
factor the joint reports no children until a later call at the same place
pushes the next factor; iteration (`to_next_val`, the `SRC` walk) skips that
subtrie.  Corpus: `lean/corpus/product-empty-middle-factor-not-transparent.bin`
(both `-full` sources).  Same as dependent D2.

### P3. `val_at` does not follow a path across a joint (both)

`ProductZipperG::val_at`/`get_val_at` (product_zipper.rs:625, :648) ask only the
focus factor's zipper; `ProductZipper::val_at` asks the core zipper, which only
sees the current node stack.  `val_at(p)` answers `None` whenever `focus ++ p`
lies past a joint, though `descend_to(p); val()` finds the value.  Corpus:
`lean/corpus/product-val_at-misses-next-factor.bin` (both `-full` sources).
Same as dependent D3.

### P4. `ProductZipper::val_at` panics inside a secondary factor

`ReadZipperCore::get_val_at` calls `focus_parent`, which looks `parent_key` up
in the previous node on the stack; after `enroll_next_factor` pushed a
secondary's root that lookup goes to the primary's node and
`node_get_child(..).unwrap()` panics (src/zipper.rs:3353), or would find an
unrelated node.  Happens with the focus on a joint, and anywhere inside the
first node of a secondary (`val_at([])` at `a` and at `ab` for primary `{a}`,
secondary `{bcd, bce}`).  Corpus: `lean/corpus/product-val_at-panics-at-joint.bin`
(`product-full`).

### P5. `ProductZipper::descend_to_check(&[])` is `true` at a missing focus

The override returns whether `descend_to_existing` consumed the whole key;
an empty key is always consumed, so it answers `true` at a non-existent focus.
The trait doc (and the native zipper) say it returns whether the new focus
exists.  ~1% of inputs.  KNOWN `product_descend_to_check_empty`; corpus:
`lean/corpus/product-descend_to_check-empty-path-at-missing-focus.bin`
(`product`).

### P6. `path_indices()` has one entry too many at a joint (both; doc mismatch)

`ZipperProduct::path_indices` is documented to have length `focus_factor()`;
at a joint both types report `focus_factor() = k` and `k + 1` indices (the
start of the factor entered at the focus).  The trace compares only the indices
strictly above the focus, so this one is reproduced by `product_repros` only.
Same as dependent D4.  (Which side is wrong is a doc question: the extra index
is harmless and arguably useful.)

## Named skips and KNOWN entries

* `skip:product-empty-factor` (whole input; Rust `SKIP_EMPTY_FACTOR`, Lean
  `Product.inputSkip`): map0's or map1's root has no children (P1, P2).  ~9%
  of random inputs.
* `skip:product-val-at-joint` (ops 24 `val_at`, 51 `get_val_agrees`, read side;
  Rust `val_at_skip_at`, Lean `Product.valAtSkip`): the path from the focus
  crosses a joint (P3); for `ProductZipper` also any focus at or below a joint
  (P4: where the first node of a secondary ends is a layout matter, so the
  whole region is declined).  `val_at` stays checked within the primary for
  both and within a factor for `ProductZipperG`.
* KNOWN `["src:product\n", "descend_to_check ret=1 "]` (P5), and for the
  `-full` sources, per bug where the line says which (P3, P4) and a
  source-wide catch-all for the empty-factor class (P1, P2): every input on
  which `-full` differs from the skipping source is one of those.

## Relation to Zippy's `Composition` (semantic decisions, not bugs)

`Composition s t` (`lean/PrunedModel/Zippy.lean`) folds over the keys `u` of
`s`: `descend_to u; join_map_into t`, i.e. on value paths `keys(s)·keys(t)`.
The product is leaf-based instead, and `Product.lean` checks (over every pair
of a 12-shape battery):

    keys (prod2 T1 T2) = keys T1 ∪ { l ++ q | l ∈ leaves T1, q ∈ keys T2, q ≠ [] }

When `T1`'s keys are prefix-free and it has no dangling path (its leaves are
then exactly its keys) this is `keys T1 · (keys T2 ∪ {[]})`, and it equals
`Composition` exactly when `T2` also has a root value (for non-empty `T1`).
The four ways `ProductZipper` differs from `Composition`, each a `#guard`:

1. **Internal keys of `T1`** get no copy of `T2`: a valued path with children
   is not a joint.  Composition grafts `T2` below every key.
2. **`T1`'s leaf values are kept** even when `T2` has no root value
   (Composition keeps `u` only if `[] ∈ keys T2`); and `T2`'s root value is
   never visible at the joint.
3. **An empty `T2`** leaves `T1` unchanged; Composition with an empty `T2` is
   empty.
4. **Dangling leaves of `T1` are joints**; Composition only extends keys.

To make `Composition` the spec instead: set `Product.semantics := .composition`
in `Product.lean`.  Both sources' views then use `composition` (right-nested
over the three factors; the view keeps map1's value at `r`), and the
`ZipperProduct` report switches off, since factor boundaries are not defined
under it.  The skips stay keyed on the leaf structure and would need revisiting.

## The stated spec: graft at values (2026-11-10)

The spec, as given:

    map(PZ(x, y)) = values(x).map(wz.descend_to(-).graft(y))

Starting from `x`, for each value path `u` of `x` in iteration order (a key
before its extensions), descend a write zipper to `u` and `graft` `y` there:
everything below `u` becomes `y`'s content and the value at `u` becomes `y`'s
root value (cleared if `y` has none).  n factors nest to the right.  It is
`Product.graft2` / `graftProd` in `Sources/Product.lean`, written literally
with the model's write-zipper operations, selectable as `Semantics.graft`.

**How the crate deviates.**  `ProductZipper` / `ProductZipperG` implement the
leaf product (`prod2`), which differs from the spec in three ways (each a
`#guard`):

1. **A value with children below it is a joint** in the spec, and `y`
   replaces those children.  The crate joins only at leaves and keeps the
   children.
2. **A dangling leaf is not a joint** in the spec (it is not a value); the
   crate joins there.
3. **The joint shows `y`'s root value** in the spec; the crate keeps `x`'s
   (the "one change" above).

With the product sources pointed at the spec (`semantics := .graft`), 1 726 of
10 000 random `product` inputs agree.  The rest diverge, nearly all through
these three; they are not recorded as KNOWN entries, since the sources stay on
`.leaf` (what the crate does) so that campaigns keep finding the crate's other
bugs.

**Relations** (`#guard`s over the battery):

* When `x` has values exactly on its leaves (`leafValued`), the joints
  coincide: the spec is the leaf product with only the joint value changed
  (`prod2AtJoint`), and it is Zippy's `Composition`.  So for such factors the
  minimal crate change is change 3.
* With nested keys the spec is **not** `Composition`: the deeper graft
  replaces what the shallower graft put there (the deepest key wins), where
  `Composition` takes the union.  `x = {a:1, ab:2}`, `y = {b:9}` gives
  `{abb:9}`; `Composition` gives `{ab:9, abb:9}`.
* `x`'s dangling paths outside every key survive; those below a key are
  replaced.  (`CompositionZipper` keeps both.)
* The spec is associative over every triple of the battery.

**Implementing it as a zipper.**  Changes 2 and 3 are local: test `is_val`
rather than "no children" for a joint, and read the next factor's root value
there.  Change 1 is the hard one.  Below a joint `u`, the result holds `y`'s
copy plus the paths leading to `x`'s deeper keys (created by the later
`descend_to`s), but not `x`'s other content.  For a cursor in `x`, "does a key
lie below this location" is a search of the subtrie, which is the O(N)-per-step
cost the composition design avoided.  It is O(1) when `x` has no dangling paths
(every existing path then leads to a key), so a zipper for this spec is cheap
on pruned factors and needs a search, or a cached per-node flag, otherwise.

## What is covered / what is not

Answer-checked now (previously never run or crash-only): `new`,
`has_next_factor`, `enroll_next_factor`, `ensure_descend_next_factor`,
`fix_after_ascend`, every `ZipperMoving` method of both types (all `descend_*`,
sibling steps, `ascend*`, `reset`, `ProductZipper::val_count`), `factor_idx`,
`is_path_end`, `exit_factors`, `enter_factors`, `ascend_cond`,
`to_sibling_byte`, `Zipper`/`ZipperValues`/`ZipperValuesAt`/`ZipperPath`/
`ZipperAbsolutePath` of both, `ZipperReadOnlyValues` (G) and
`ZipperReadOnlyConditionalValues` (both), the default `ZipperIteration`
methods over both, and `ZipperProduct` (`factor_count`, `focus_factor`,
`path_indices` above the focus) of both.

Not covered: `ZipperConcrete` (`shared_node_id`, `is_shared`; the op table has
no sharing op), `ZipperPathBuffer`, `Debug`, `new_with_primary`,
`new_factors`, the deprecated `reserve_path_buffer`, `OneFactor`, secondaries
not at a node root (documented to panic), factors with a root prefix, and more
than three factors.

## Framework changes (shared files)

Three optional hooks, each a no-op for every other source:

* `ReadSource::source_info` / `Source.info`: a string appended to the read
  zipper's per-step fingerprint (here `ZipperProduct`).
* `ReadSource::val_at_skip` / `Source.valAtSkip`: a named skip for `val_at`
  (op 24) and `get_val_agrees` (op 51) on the read side, decided per call
  from the focus and the path.
* `Source.inputSkip`: a named skip for a whole input; the trace is that one
  token (the Rust runner returns the same line itself).

## Campaigns (after merging spec/coverage-models 90eb33a)

| source | inputs | new | known (by entry) |
|---|---|---|---|
| product | 120k (seeds 31–33) | 0 | descend_to_check ×1081, trie_ref_owned_empty_node ×4133 |
| productg | 120k (seeds 31–33) | 0 | trie_ref_owned_empty_node ×4157 |
| product-full | 20k (seed 34) | 0 | empty factor ×1777, val_at panic ×2046, val_at across joint ×104, descend_to_check ×135 |
| productg-full | 20k (seed 34) | 0 | empty factor ×2056, val_at across joint ×103 |

Earlier runs before the merge: another 80k per zipper (seeds 1, 2, 11), clean.
No known hit on product/productg differs on the read side (checked with the
overlay workstream's `known_dump.py`).  `native` and `map` 20k each: no new
divergence.  About 9% of inputs are `skip:product-empty-factor`.
