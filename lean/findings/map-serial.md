# Map fuzzer: serialization (ops 30–33) and ArenaCompactTree (ops 40–48)

Workstream `map-serial`.  Model: `lean/PathMapModel/MapFuzz/Serial.lean`,
`MapFuzz/Act.lean`; crate side: `differential/src/mapfuzz/serial.rs`,
`mapfuzz/act.rs`.  Run with `./lean/differential.py --source map`.

## Ops

| op | name | what it checks |
|---|---|---|
| 30 | `ser_paths` | `serialize_paths` (read zipper at `p` of map i) → `deserialize_paths` (constant value) into a write zipper at `q` of map j; path counts |
| 31 | `ser_paths_aux` | the `_with_auxdata` pair: values carried by index, the `(k, path)` handed to both closures agree |
| 32 | `for_each_path` | `for_each_deserialized_path`: the exact path list and order, index sequence, both stats' byte counts |
| 33 | `write_trie` / `write_trie_at` | `experimental::serialization::write_trie` → `deserialize_file` (zero-compressed or raw file; minimal-LE `Encode` or 8-byte `Read` value encoding); `meta.json` `VAL_COUNT`, `MAX_PATH_LEN` |
| 40 | `act_dump` | `dump_from_zipper` to a file; same bytes as `from_zipper` |
| 41 | `act_open` | `from_zipper` → file → `open_mmap`; same bytes; `open_mmap` of a truncated file |
| 42/43 | `act_merge`, `act_merge2` | `merge_zipper_into_file` once / twice into the same file; result and `root_history().len()` |
| 44 | `act_stream` | `ACTOutputStream` (`new`, `with_cache_limit(0/1/2)`) fed a map's values in order |
| 45 | `act_stream_raw` | `ACTOutputStream` fed arbitrary `(path, value)`s with `push`/`push_val`: which are rejected, and the result |
| 46 | `act_cached` | `from_zipper_cached` over a map with another map grafted at 1–3 prefixes (structural sharing) |
| 47 | `act_get` | `get_val_at` and deprecated `get` at several paths; `iter()` |
| 48 | `act_zipper_at` | `read_zipper_at_borrowed_path_u64` / `read_zipper_at_borrowed_path` dumps |

ACT ops use a value mapping (identity, `v * 0x0101010101010101`, `!v`) so 8- and
9-byte varints are exercised.  Files live in a per-op scratch directory under
`$TMPDIR` (`pathmap-mapfuzz-<pid>-<seq>-<op>`), removed file by file on drop,
including while unwinding.

## Semantic decisions

* **`.paths` keeps `vals` only**, the focus value included (as the empty path),
  dangling paths dropped; values are whatever the deserializer supplies.
* **Deserializing into a map is `graft_map`** at the write zipper's focus
  (`Zip.graftMap`): it replaces the focus subtrie *and* the focus value; it is
  not a join.  (That is what the code does and what `graft_map` documents.)
* **`write_trie` keeps `vals` only.**  A dangling path is written as an empty
  node and reads back as nothing in a release build (but see the debug
  assertion below).  The root value is kept.
* **ACT keeps the whole trie**, root value and dangling paths included (same
  view as `Source.act`), for `from_zipper`, `from_zipper_cached`,
  `dump_from_zipper`, `open_mmap`.  `ACTOutputStream` can only hold values.
* **`merge_zipper_into_file` is a join with the zipper's value winning**, paths
  united (dangling included), per the method doc; `root_history` grows by one
  exactly when the merged trie differs from the base ("if the zipper adds
  nothing, the file is left untouched").
* **`ACTOutputStream` order rule**: a path must be strictly greater than the
  last *accepted* one; a rejected push is `InvalidInput` and changes nothing.
* Not observable: `Counters` (only count with `act_counters`); ACT
  `val_count` and `descend_last_path` (known bugs, unused here).

## Crate bugs

### 1. `serialize_paths` never writes the focus value  [`serialize_paths_drops_focus_value`]

`serialize_paths_with_auxdata` iterates with `rz.to_next_val()`, which moves
off the focus before it looks for a value, so the value *at* the read zipper's
focus is never written.  The format can carry it (a zero-length record; the
deserializer's `set_val_at(&[], v)` turns it into the grafted map's root value),
the doc says "each value's path from the focus", and `ArenaCompactTree::iter`
deliberately yields the root value — so a round trip
`serialize_paths(m.read_zipper())` → `deserialize_paths(m2.write_zipper())`
silently loses `m`'s root value (and, since `graft_map` replaces the focus
value, also *clears* the destination's).

* Corpus: `lean/corpus/serialize_paths-drops-focus-value.bin`
  (`0 ser_paths ret=0,0;r=0` vs model `ret=1,1;r=1`).
* KNOWN: `["src:map", ";r=1 n=", ";r=0 n="]` — the `;r=` ret field says whether
  the stream held a zero-length record, so only this loss is matched.
* Standalone:
  ```rust
  let mut m = PathMap::<u64>::new();
  m.set_val_at([], 5); m.set_val_at([1u8], 6);
  let mut buf = vec![];
  let s = serialize_paths(m.read_zipper(), &mut buf).unwrap();
  assert_eq!(s.path_count, 2); // fails: 1
  ```
* Hits ~11% of 300-byte inputs; inputs that hit it are only checked up to it.

### 2. `write_trie` below the map root drops path bytes  [`write_trie_below_root_drops_prefix_bytes`]

The catamorphism hands `alg_f` the **absolute** `origin_path` (documented in
`Catamorphism`); `write_trie` treats it as relative to the trie it writes.  Its
"does this jump reach the root?" test `origin_path.len() == jump_length` is
never true for a read zipper rooted below the map root, so the leading
single-child chain's bytes are left in `jump_sub_slice` and never written:
`{[0,0]: 7}` written from a zipper at `[0]` reads back as `{[]: 7}` instead of
`{[0]: 7}`.  `MAX_PATH_LEN` likewise counts the zipper's root prefix.

* Corpus: `lean/corpus/write_trie-below-root-drops-prefix-bytes.bin`.
* The fuzzer gives this case its own op name, `write_trie_at`, that only renders
  the result (never grafts it), so it cannot corrupt later steps; KNOWN
  `["src:map", "write_trie_at"]` therefore covers the whole below-root case.
  `write_trie` from the map root is checked in full.
* Standalone: `write_trie("x", m.read_zipper_at_path([0]), enc, dir)` then
  `deserialize_file` for `m = {[0,0]: 7}`.

### 3. `write_trie` leaves a stale tail after rolling back its last record  [`write_trie_stale_tail_after_rollback`]

`serialize_with_rollback` writes a record, hashes it, and on a hash hit seeks
back (`seek_relative`) so the next record overwrites it.  When the rolled-back
record is longer than whatever is written after it, and nothing else follows,
its tail stays in the file: the file is never truncated to the final position.
`deserialize_file` then reads the leftover `000…0` line and fails with
"Malformed serialized ByteTrie, expected `<tag byte><space>`".

For `{[1,1]: 5, [1,2]: 7, [2]: 6}` (8-byte LE values) the raw file ends
```
c 6000000000000000000000000000000000000000000000000000000000000000
B x0000000000000008x0000000000000007
v 0600000000000000
V x000000000000000Ax0000000000000002
b x0000000000000009x000000000000000B
B x0000000000000008x000000000000000C
00000000000000000000000000000
```
— the second `c 6000…` (the root's child mask, equal to node 7's) was rolled
back and overwritten by the shorter `B` line.  Both the raw and the
zero-compressed files are affected.

* Corpus: `lean/corpus/write_trie-stale-tail-after-rollback.bin`
  (`0 write_trie ret=err:tag`).
* KNOWN: `["src:map", "write_trie ret=err:tag"]`.  The op renders a
  deserialization error as `ret=err:<why>` instead of panicking.

### 4. `ArenaCompactTree::open_mmap` panics on a file shorter than the magic  [`act_open_short_panics`]

`open_mmap` returns `io::Result` and rejects a wrong magic with `Err`, but
slices `&memmap[..MAGIC_LENGTH]` before checking the length, so a 0–7-byte
file panics ("range end index 8 out of range for slice of length N").  The same
unchecked slice is in `dump_from_zipper`'s re-open (not reachable with a
well-formed dump).

* Corpus: `lean/corpus/act-open_mmap-short-file-panics.bin` (agrees since the fix).
* Fixed by PathMap #200: `open_mmap` (and `dump_from_zipper`'s re-open) now
  return `Err` for a file shorter than the 16-byte header.  Op 41's `trunc=`
  field checks it directly: `err` below 16 bytes, `ok` from 16 on.  (Before the
  fix a named skip `skip:act_open_short` covered `k < 8`, and 8–15-byte prefixes
  opened, then panicked on the first root read.)
* Standalone:
  ```rust
  std::fs::write(&f, b"ACT")?;
  ArenaCompactTree::open_mmap(&f) // panics instead of Err
  ```

### 5. (debug builds) `deserialize_file` asserts on a file with a dangling path

`write_trie` writes a dangling leaf as an empty branch node; `deserialize_file`
has `debug_assert!(!path_node.is_empty())` when grafting a path node, so with
debug assertions on, `write_trie` of `{[1]: 3}` plus a dangling `[2,2]` panics
at `src/experimental/serialization.rs:830` on reading back.  In release the
dangling path is silently dropped, which is what the model expects (the fuzzer
runs the release build, so this is not exercised by the campaigns).  Writer
and reader disagree on whether empty nodes can occur; one of them is wrong.

## Open questions

1. **Is the focus value part of a `.paths` serialization?**  Modelled as yes
   (bug 1).  If the intended contract is "values strictly below the focus",
   the doc should say so, and `deserialize_paths` should probably not clear the
   destination's focus value.
2. **`write_trie`'s `MAX_PATH_LEN` below the root**: relative (the file's trie)
   or absolute (the source map)?  Modelled as relative, compared only for a
   zipper at the map root; below the root it is bug 2's territory.
3. **`PATHS_COUNT` in `meta.json`** is never incremented (always 0).  Not
   compared; its intended meaning (locations? values?) is undocumented.
4. **Should `write_trie` keep dangling paths?**  Modelled as dropped (bug 5 shows
   the reader does not expect them).

## Coverage

Answer-checked now: `serialize_paths`, `serialize_paths_with_auxdata`,
`serialize_paths_from_funcs`, `deserialize_paths`,
`deserialize_paths_with_auxdata`, `for_each_deserialized_path` and both stats
structs; `write_trie` (both `ValueSlice` variants), the zero compressor,
`deserialize_file` (both files) and the `VAL_COUNT`/`MAX_PATH_LEN` metadata;
ACT `dump_from_zipper`/`dump_arena_tree`/`FileDumper` (incl. `line_matches`),
`open_mmap`, `get_data`, `from_zipper`, `from_zipper_cached`/`CachedBuilder`,
`merge_zipper_into_file`/`ZipperMerger` (single and chained, `root_history`),
`ACTOutputStream` (`new`, `with_cache_limit`, `push`, `push_val` incl. order
rejection, `collapse_to`, `seal`, `finish`), `get_val_at`, `get`, `iter`,
`read_zipper_at_borrowed_path[_u64]`.

Not covered: `Counters`/`SiCount` Display (no-ops without `act_counters`);
`dbg_hex_line_numbers`; `sort_paths`/`sort_paths_par` (not in scope);
`paths_serialization_nightly`; `experimental/tree_serialization.rs` (not in
this tree).  Dangling paths reach these ops only through `deserialize_paths`
grafting an empty map over an existing subtrie; once Core grows
`create_path`-style ops, merges/dumps of dangling paths will be exercised much
more.

## Campaigns

`--source map`, release build, `-j 6`, 0 new divergences after the three KNOWN
entries and the skip:

* seeds 10–14 × 20 000 (default `--maxlen 300`): ~14% of inputs end at a known bug
  (≈2 290 focus-value, ≈490 `write_trie_at`, ≈20 stale tail per 20 000);
* seed 15 × 20 000 at `--maxlen 1200`;
* seeds 21–28 × 50 000 at `--maxlen 600` (400 000 inputs; ~28.6% known, ≈140
  stale-tail hits per 50 000);
* `--source native` 20 000 and `--source act` 5 000 unchanged.

Every known hit was checked with `-v` to come from a `src:map` entry; no
zipper-fuzzer entry matched.  No `pathmap-mapfuzz-*` directories are left in
`$TMPDIR` after the runs.
