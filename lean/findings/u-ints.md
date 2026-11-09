# Util fuzzer: `utils/ints.rs`, the path sorters, `viz`, `random`, `counters` (ops 60–99)

Workstream `u-ints`.  Model: `lean/PathMapModel/UtilFuzz/Ints.lean` (ops
60–79), `UtilFuzz/Misc.lean` (ops 80–94); crate side:
`differential/src/utilfuzz/ints.rs`, `utilfuzz/misc.rs` (op tables and
operand formats in their headers).  Run with
`./lean/differential.py --source util`.

> **The differential crate now enables pathmap's `viz`, `random` and
> `counters` features** (`differential/Cargo.toml`, plus a `rand = "0.9"`
> dependency for seeded RNGs).  This affects every build of the differential
> crate.  Checked safe: `viz` and `random` only add modules; `counters` adds two
> `Relaxed` atomic increments to `TrieNodeODRc::make_unique` and some
> `item_count` methods.  The traces of 6000 `native` and 4000 `map` inputs are
> byte-identical with and without the three features (A/B of two
> `pathmap_trace` builds), and write benchmarks (`shakespeare`, `sparse_keys`,
> `cargo bench`, with and without `--features counters`) moved by -20%..+16%
> per benchmark in both directions, i.e. within the noise of a shared machine;
> the clearest single number, `shakespeare_words_insert`, went 55.4 → 64.5 ms.

## What is modelled

### `utils/ints.rs` (ops 60–79), every op for each of `u8 u16 u32 u64 usize u128`

* **Bits of Byte** (`indices_to_bob` / `bob_to_indices`): the bit transpose of
  up to 8 integers, most significant bit first, `steps` = the largest bit
  length, appended to the caller's vector.  The decoder reads any string of at
  most `8N` bytes.  Ops render the encoding *and* its decoding (round trip),
  and decode arbitrary byte strings.  `#guard`: `unbob ∘ bob = id`.
* **Weave** (`indices_to_weave` / `weave_to_indices`): big-endian bytes,
  round robin, **always `N` bytes per integer** (see D2 / open question 1),
  each `usize` input reduced to its low `N` bytes.  `#guard`:
  `unweave ∘ weave = (· mod 2^(8N))`.
* **`gen_int_range(_in)`**: the map holding the value at the `N`-byte
  big-endian encoding of every `start + k*step < stop`, nothing else (no other
  values, no dangling paths: op 78 counts every location).  Op 78 lists small
  ranges in full; op 79 builds ranges of up to 2^128 elements (power-of-two
  steps, or up to 4096 elements with an arbitrary step) and checks
  `val_count`, the first 4 entries, and the value at 9 probes around the range
  (start, start+step, last, last+step, stop−1, stop, 3 grid points ±1).
  `start >= stop` is the empty map.  `step = 0` is not generated (finding U3).

### `sort_paths` / `sort_paths_par` (ops 80–84)

The model is the input's path **set**, in strictly increasing byte order
(`.paths` has no values or auxdata, so stability has nothing to apply to), plus
the documented contract: budget < 1 MiB → `InvalidInput`; a path over
`budget / 16` → `InvalidData`; `SerializationStats` of the output
(`path_count`, `bytes_in` = Σ(4 + len), `bytes_out` = bytes written); the
caller's scratch directory left empty on success and on error.  For a stream
that ends partway through a record the serial sorter keeps the complete
records and the parallel one fails with `InvalidData` (both documented); a
stream cut at a record boundary (no trailer) is accepted by both.  The
parallel sorter is held to the same model, so to the serial one, in every op;
82–84 run both on the same input.

* 80/81: small lists (≤ 23 paths, alphabets of 2, 4 or 256 bytes, so
  duplicates and shared 8-byte prefixes are common), budgets 1–4 MiB or just
  under 1 MiB.
* 82: generated lists of up to 40000 paths (≈1.3 MB of records) at 1–2 MiB, so
  both sorters spill runs and merge them (checked with `strace`: the serial
  sorter wrote 7 run files, the parallel one 3, for one such input).  Answer:
  count, `bytes_in`, FNV-1a of the output, first/last path.
* 83: a stored-block zlib stream built by the harness (`78 01`, one stored
  block, Adler-32), cut at any point: inside the headers, inside the records,
  inside the trailer, or not at all.
* 84: one path of 65535, 65536 or 65537 bytes at a 1 MiB budget (limit 65536).

Every call gets its own scratch directory (`<tmp>/pathmap-utilfuzz-<pid>-<n>`,
created with `create_dir`), which the harness empties and removes after
counting what the sorter left there.

### `viz` (ops 85–87)

For maps whose nodes are unshared (every op builds 1–3 maps from scratch):

* the **logical** rendering is a radix tree: nodes at the root and at every
  location that branches or (unless `hide_value_paths`) holds a value and has
  one child; other locations fold into labelled edges; values at nodes are
  drawn on the node, values at leaves as edges.  Labels are the bytes as a
  string (`ascii_path` and valid UTF-8; the alphabet `a b c3 a9` makes both
  cases common) or `[b, b]`.
* **ASCII** (op 85): the exact text (box-drawing tree, `PathMap[i] = v`
  headers, `(empty)`, blank line between maps, `minimize_values`,
  `hide_value_paths`).  `color` only colours shared-node markers, which never
  appear for unshared maps.
* **Mermaid logical** (op 86): node ids are address hashes, so the output is
  parsed back into a graph and compared as one (edges in label order, value
  texts).  `DrawConfig::default()` is used for one config value in eight.
* **Mermaid physical** (op 87): only what the layout must show: concatenating
  edge labels from the root reaches exactly the map's values.

### `random` (ops 88–92)

Answers that do not depend on the RNG: `RandomTrie` with scripted path/value
distributions is exactly the fold of `set_val_at`; each sampler returns a
candidate of its documented kind (any value; the first value on a descent; any
location with its value; a leaf with its value), exactly when there is one
candidate; two samples from equally seeded `StdRng`s agree; the two policies'
choices are exactly the child bytes, and `unbiased_descend_last_policy`'s
`db` / `dy` are "has children" / the value there.

### `counters` (ops 93–94)

`CowCounters`: unshared writes clone nothing; a write through a `clone()`d map
clones at least one node (if the map has any node); none after the clone is
dropped; `cow_clones <= make_unique_calls`.  `Counters::new()` is zero;
`count_ocupancy` counts ≥ 1 node and ≥ nodes − 1 child items.

## Crate bugs

None of these has a corpus file: each would end the comparison of a large
share of inputs (or panic), so the ops avoid or skip it under a named skip
(same token on both sides), and the standalone repros below are the record.
All were confirmed in release and debug builds
(`pathmap` at this branch's base, a93bb60).

### U1. `indices_to_weave::<16, u128>` repeats the low 8 bytes  [`weave_u128_shift_overflow`, `skip:weave-u128-shift`]

`indices_to_weave` takes `xs: &[usize]` and emits `(xs[i] >> c*8) as u8` for
`c` in `0..NUM_SIZE`.  For `NUM_SIZE = 16` the shift reaches 120 bits on a
64-bit `usize`: release builds mask the shift amount, so byte positions 15..8
repeat positions 7..0 instead of being zero; debug builds panic ("attempt to
shift right with overflow").  The decoded round trip is `x << 64 | x`.

```rust
let mut w = vec![];
indices_to_weave::<16, u128>(&[0x0102usize], &mut w);
// release: 00000000000001020000000000000102 (want 14 zero bytes, then 01 02)
// debug:   panic
```

Op `weave_u128` renders only the prefix and the lower 8 byte positions (still
checked) and `;skip:weave-u128-shift`.  As a KNOWN entry it ended ~20% of
inputs early.  `weave_to_indices::<16, u128>` itself is correct (`unweave_u128`).

### U2. `weave_to_indices` accepts more than `N` bytes per integer  (no op)

`bob_to_indices` asserts `bob.len() <= NUM_SIZE * 8`; `weave_to_indices` has no
counterpart.  With more than `NUM_SIZE` rounds the shift overflows: release
ORs the excess bytes into the wrong positions, debug panics.

```rust
let mut xs = [0u8];
weave_to_indices::<1, u8>(&[1, 2], &mut xs); // release: xs = [3]; debug: panic
```

The ops stay inside `steps <= N`.  Minor: an input-validation gap, the analogue
of the assertion its sibling has.

### U3. `gen_int_range` with `step = 0` hangs (`u8`) or panics (wider types)  (no op)

The `u8` special case loops forever (`i.saturating_add(0)`); the other widths
divide by zero in `gen_child_level_in`.  Not documented as a precondition.

```rust
gen_int_range::<(), 2, u16>(0, 10, 0, ());  // panic: attempt to divide by zero
gen_int_range::<(), 1, u8>(0, 10, 0, ());   // never returns
```

### U4. `viz_maps` panics on a map with nothing below its root  [`viz_no_root_node`, `skip:viz-no-root-node`]

All three renderers start from `btm.root().unwrap()`; an empty `PathMap`, or
one holding only a root value, has no root node.  The ASCII renderer has an
explicit `(empty)` case, so empty maps are meant to render.

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at([], 7);   // or leave it empty
viz_maps(&[m], &DrawConfig { mode: VizMode::Ascii, ..Default::default() }, &mut vec![]);
// panic: called `Option::unwrap()` on a `None` value
```

### U5. Mermaid renderings never draw the root value  [`viz_mermaid_drops_root_value`, `;skip:viz-mermaid-root-value`]

`viz_zipper_logical` starts with `to_next_step()`, so the value at the root is
never visited; `viz_map_physical` draws only the root *node*, and the root
value lives outside it.  The ASCII renderer draws it (`PathMap[0] = 1`).

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at([], 1); m.set_val_at(b"a", 2);
// Mermaid, logical or physical: one value node, labelled "2"; the 1 is missing.
```

Ops on maps with a root value are named `viz_mermaid_rv` / `viz_phys_rv`; the
model leaves the root value out of those and appends the skip token, so the
rest of the graph is still compared (as a KNOWN entry it ended ~15% of inputs
early).

### U6. Mermaid physical rendering of four or more maps panics  (no op)

`color_for_bitmask` handles 3 map bits and ends in `todo!()`; the physical
renderer colours every node with its map's bit, so the fourth map panics.  The
logical renderer happens not to reach it for independent maps.  `viz_maps`
does not document a limit.

```rust
let maps: Vec<PathMap<u64>> = (0..4).map(|i| PathMap::single([b'a' + i as u8], i)).collect();
viz_maps(&maps, &DrawConfig { logical: false, ..Default::default() }, &mut vec![]);
// panic: not yet implemented
```

The ops draw at most 3 maps.

### U7. `FairTrieValue` panics on, and never returns, a root value  [`fair_trie_value_root_value`, `skip:fair-value-root-value`]

`sample` draws `target` in `0..rz.val_count()`, which counts the root value,
then walks `rz.to_next_get_val()`, which starts *below* the root.  So the root
value is never returned and the last index falls off the end into
`unreachable!()`.

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at([], 7);
FairTrieValue { source: m }.sample(&mut StdRng::seed_from_u64(0)); // panic: unreachable
// with {[] => 7, "a" => 8}: 112 of 200 seeds panic, the rest return ("a", 8)
```

### U8. `Counters::count_ocupancy` panics on a map without a root node  [`count_ocupancy_no_root_node`, `;skip:counters-no-root-node`]

Same `map.root().unwrap()` as U4.

```rust
Counters::count_ocupancy(&PathMap::<u64>::new()); // panic: unwrap on None
```

### Doc mismatches (no divergence; the model follows the code)

* **D1.** The doc comment of `indices_to_bob` and the printed results in the
  `bob_and_weave_simple` test list the bytes least-significant bit first
  (`["0", "11", "110", "11", "10", "100", "100"]` for `[10, 30, 100]`); the
  encoder emits the most significant first (the reverse), and only that order
  is inverted by `bob_to_indices`.  The model's fixtures are the doc's lists
  reversed.
* **D2.** `indices_to_weave`'s doc says "Does not pad to number byte length"
  and the test's comments print unpadded weaves (`[13, 0, 3, 5, 30, 232]` for
  `[3333, 30, 1000]`); the code writes exactly `NUM_SIZE` bytes per integer,
  the unpadded length computation being commented out.

## Open questions

1. **Weave width.**  Modelled as the code does it: `N` bytes per integer
   (`Ints.lean`).  Reasons: the unpadded form was deliberately commented out;
   only fixed width makes the weaves of equal-arity tuples equal-length and so
   prefix-free trie paths; the decoder accepts both.  If the doc is the intent,
   every weave op diverges.
2. **Corrupt `.paths` input.**  A stream with a zlib data error: the parallel
   sorter returns `InvalidData` ("corrupt .paths stream"); the serial one ignores
   `Z_DATA_ERROR` (as `for_each_deserialized_path` does) and sorts what it got.
   Neither is documented; not fuzzed.
3. **A stream that stops at a record boundary** without its zlib trailer:
   modelled as accepted by both sorters (the parallel sorter's code says "the
   stream stopped short; accept its whole records"; the docs only speak of
   stopping partway through a path).

## Coverage: every public item

| item | how |
|---|---|
| `PathInteger` (marker trait) and its impls for `u8`, `u16`, `u32`, `u64`, `usize`, `u128` | every ints op family runs for all six |
| `indices_to_bob`, `bob_to_indices` | 60–65 (encode + round trip), 72–77 (decode arbitrary bytes) |
| `indices_to_weave` | 66–71 (`u128`: lower half only, U1) |
| `weave_to_indices` | 66–70 round trip, 72–77 arbitrary bytes, all six |
| `gen_int_range` | 78, 79 |
| `gen_int_range_in` | 78 (with `global_alloc()`, one call in two) |
| `gen_value_level_in`, `get_from_cache` (private), `gen_child_level_in` (`pub(crate)`) | through `gen_int_range`, every width ≥ 2 |
| `paths_serialization::sort_paths` | 80, 82–84 |
| `paths_serialization::sort_paths_par` | 81–84 |
| `viz::viz_maps` | 85 (ASCII), 86 (Mermaid logical), 87 (Mermaid physical) |
| `viz::DrawConfig` (all fields), `Default for DrawConfig`, `viz::VizMode` (both variants) | 85–87 decode every field; 86 uses `DrawConfig::default()` one time in eight |
| `random::RandomTrie` (`Distribution<PathMap>`) | 88 |
| `random::FairTrieValue` | 89 |
| `random::DescendFirstTrieValue`, `unbiased_descend_first_policy` | 90 |
| `random::FairTriePath` | 91 |
| `random::DescendTriePath`, `unbiased_descend_last_policy` | 92 |
| `random::*` re-exports of `distr_combinators` | third-party code, not pathmap's; `Categorical`, `Choice2`, `Degenerate`, `Mapped` are exercised through the two policies |
| `counters::CowCounters`, `cow_counters`, `reset_cow_counters` | 93 |
| `counters::Counters::new`, `total_nodes`, `total_child_items`, `count_ocupancy` | 94 (invariants only: the counts are node-layout statistics with no logical model) |
| `Counters::print_histogram_by_depth`, `print_run_length_histogram`, `print_list_node_stats`, `counters::print_traversal` | **not called**: they print to stdout, which is the trace channel of the server-mode harness, and print layout statistics (or, for `print_traversal`, value paths) with no stable format |
| derived `Clone`/`Debug`/`Default` impls | not separately checked |

## Campaigns

`--source util`, `-j 6`, default 300-byte inputs unless noted (ops 0–59 were
still `nop`s on this branch, so about 40% of ops were this workstream's):

| seeds | inputs | result |
|---|---|---|
| 1–7 (during development) | 143,000 | the weave_u128 and Mermaid-root-value divergences (U1, U5), then all agree |
| 11, 12, 13, 14 | 4 × 60,000 | all agree, 0 known |
| 15, `--maxlen 2000` | 20,000 | all agree, 0 known |
| 21, 22 (final build, with `DrawConfig::default`) | 2 × 40,000 | all agree, 0 known |

So 340,000 inputs on the finished op set, with no divergence.  A 300-byte input
runs about 60 ops; ~1 in 4 `sort_big` ops spills runs to disk.  No scratch
directory was left in `$TMPDIR` after any campaign.

Sanity runs after the feature change: `--source native` 5000 inputs (0 new;
known: `trie_ref_owned_empty_node` ×195, `try_borrow_focus` ×65), `--source
map` 5000 inputs (0 new; 302 known, all existing map-serial / map-core
entries).

`differential.py`: `classify` now applies only `src:util` KNOWN entries to util
traces, as it already did for `src:map` (the old op-name keys could otherwise
swallow a util divergence).  This workstream adds no KNOWN entries: every bug
found is either avoided by the operand ranges (U2, U3, U6) or under a named
skip.
