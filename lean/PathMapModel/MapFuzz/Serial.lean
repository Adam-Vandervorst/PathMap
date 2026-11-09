import PathMapModel.MapFuzz.Base
import PathMapModel.Write

/-!
# Map fuzzer, ops 30–39: serialization round trips

Two formats, each a round trip whose model is "the map you started with, or
exactly the part the format preserves":

* **`.paths`** (`src/paths_serialization.rs`): `serialize_paths[_with_auxdata]`
  walks the values at and below a read zipper's focus and writes each one's
  path (relative to the focus) into a zlib stream;
  `deserialize_paths[_with_auxdata]` builds a map from those paths and
  `graft_map`s it at a write zipper's focus.  The format holds *paths of
  values* and nothing else: values come back as the caller supplies them (a
  constant, or an index into a side table filled by the `_with_auxdata`
  serializer), and dangling paths do not survive.  The value at the focus
  itself is a value whose path is empty; the format can encode it (a
  zero-length record, which `deserialize_paths` turns into the grafted map's
  root value) and "each value's path from the focus" includes it, so the model
  keeps it.  (The crate does not: `lean/findings/map-serial.md`.)
* **`write_trie` / `deserialize_file`** (`src/experimental/serialization.rs`):
  a hashed, shared node file.  It holds values (encoded by the caller) and the
  branching structure, but a dangling path serializes as an empty node and
  reads back as nothing, so it too preserves `vals` only.  `meta.json`'s
  `VAL_COUNT` is the number of values and `MAX_PATH_LEN` the length of the
  longest location written.  The catamorphism hands `write_trie` absolute
  `origin_path`s (its documented contract) while `write_trie` treats them as
  relative to the trie it writes; from a zipper below the map root it then
  drops path bytes and counts the root prefix into `MAX_PATH_LEN` (finding
  `write_trie_below_root_drops_prefix_bytes`).  That case is its own op name,
  `write_trie_at`, which only renders the result.

Deserializing *into* a map is `graft_map` at a write zipper's focus: the
format's map replaces the focus's subtrie and value (`Zip.graftMap`); it is
not a join.

`experimental/tree_serialization.rs` does not exist in this tree.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool dumpAt)

namespace Serial

/-- `t.write_zipper_at_path(q).graft_map(s)`. -/
def graftAt (t : PathMap V) (q : Path) (s : PathMap V) : PathMap V :=
  (({ trie := t, root := q, path := [] } : Zip V).graftMap s).trie

/-- What a values-only format keeps of `t`: its values, no dangling paths. -/
def valsOnly (t : PathMap V) : PathMap V := PathMap.mk' t.vals []

/-- The paths `serialize_paths` writes for a read zipper at `p` of `t`: every
value's path relative to the focus, the focus's own (empty) one included, in
depth-first order. -/
def serKeys (t : PathMap V) (p : Path) : List Path := (t.subtrie p).vals.map (·.1)

/-- `SerializationStats::bytes_in`: each record is a 4-byte length plus the path. -/
def serBytes (ks : List Path) : Nat := (ks.map (fun k => 4 + k.length)).foldl (· + ·) 0

/-- `MAX_PATH_LEN` of `write_trie`'s metadata: the longest location visited. -/
def maxPathLen (t : PathMap V) : Nat := (t.paths.map List.length).foldl max 0

end Serial

open Serial in
/-- `;r=1` when the stream carries a zero-length record (the focus value),
`;r=0` when not.  Its own field so the known root-value loss is classifiable
on its own (`serialize_paths_drops_focus_value`). -/
def rootRec (ks : List Path) : String := if ks.contains [] then ";r=1" else ";r=0"

open Serial in
def stepSerial (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 30 => do -- `serialize_paths` → `deserialize_paths` (constant value) into map j at q
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map; let (q, d) ← d.path 4
      let (v, d) ← d.val
      let ks := serKeys (s.get i) p
      let n := toString ks.length
      let m := PathMap.mk' (ks.map (·, v)) []
      some (("ser_paths", n ++ "," ++ n ++ rootRec ks, s.set j (graftAt (s.get j) q m)), d)
  | 31 => do -- `serialize_paths_with_auxdata` → `deserialize_paths_with_auxdata`
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map; let (q, d) ← d.path 4
      let sub := (s.get i).subtrie p
      let n := toString sub.vals.length
      some (("ser_paths_aux", n ++ "," ++ n ++ rootRec (serKeys (s.get i) p),
             s.set j (graftAt (s.get j) q (valsOnly sub))), d)
  | 32 => do -- `serialize_paths` → `for_each_deserialized_path`; stats agree
      let (i, d) ← d.map; let (p, d) ← d.path
      let ks := serKeys (s.get i) p
      let u := toString (serBytes ks)
      some (("for_each_path", showPaths ks ++ ";u=" ++ u ++ "," ++ u ++ ";c=ok" ++ rootRec ks, s), d)
  | 33 => do -- `write_trie` → `deserialize_file` (raw or zero-compressed)
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map; let (q, d) ← d.path 4
      let (_enc, d) ← d.mod 2; let (_file, d) ← d.mod 2
      let sub := (s.get i).subtrie p
      let v := "v" ++ toString sub.vals.length
      if p.isEmpty then
        -- From the map root: grafted into map j at q, so later ops see it.
        let ret := v ++ ",l" ++ toString (maxPathLen sub)
        some (("write_trie", ret, s.set j (graftAt (s.get j) q (valsOnly sub))), d)
      else
        -- From a zipper below the root the crate loses path bytes
        -- (`write_trie_below_root_drops_prefix_bytes`), which would corrupt
        -- every later step: the result is only rendered, under its own name,
        -- and `MAX_PATH_LEN` (which the crate counts from the map root) is not
        -- compared.
        some (("write_trie_at", v ++ ";" ++ dumpAt (valsOnly sub) [], s), d)
  | _ => some (("nop", "-", s), d)

/-! ## Fixtures -/

namespace Serial

private def fx : PathMap V :=
  PathMap.mk' [([], 7), ([1, 2], 3), ([1, 3], 4)] [[2, 2, 2]]

#guard serKeys fx [] == [[], [1, 2], [1, 3]]
#guard serKeys fx [1] == [[2], [3]]
#guard serBytes (serKeys fx []) == 4 + 6 + 6
#guard (valsOnly fx).paths == [[], [1], [1, 2], [1, 3]]
#guard maxPathLen fx == 3
-- Grafting replaces the focus value too: an empty map clears it.
#guard (graftAt fx [] PathMap.empty).vals == []
#guard (graftAt fx [1] (PathMap.mk' [([], 9)] [])).valAt [1] == some 9
#guard (graftAt fx [1] (PathMap.mk' [([], 9)] [])).valAt [1, 2] == none

end Serial

end MapFuzz
end PathMapModel
