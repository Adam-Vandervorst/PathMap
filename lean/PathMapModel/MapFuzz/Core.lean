import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 0–19: the `PathMap` surface

`PathMap`'s own methods, against `Map.lean`.  Mirrors
`differential/src/mapfuzz/core_ops.rs`.

| op | method(s) | operands | ret |
|---|---|---|---|
| 0 | `get` | map, path | the value |
| 1 | `insert` / `set_val_at` (by the map byte), on the path or the path ++ `longTail` | map, path, val | the replaced value |
| 2 | `remove` | map, path | the removed value |
| 3 | `contains` | map, path | value at the path? |
| 4 | `path_exists_at`, `contains_path`, `val_at`, `get_val_at`, `val` | map, path | `e\|e\|v\|v\|rootval` |
| 5 | `remove_val_at` | map, path, prune | the removed value |
| 6 | `get_val_mut_at` / `get_mut` (by a bool), then write through | map, path, bool, val | the old value |
| 7 | `get_val_or_set_mut_at`, then `+1` through the reference | map, path, default | the value seen |
| 8 | `get_val_or_set_mut_with_at`, then `+1` through it | map, path, default | `value:closure-ran` |
| 9 | `remove_branches_at` | map, path, prune | anything removed? |
| 10 | `prune_path` | map, path | bytes removed |
| 11 | `create_path` | map, path | created? |
| 12 | (`merkleize` by a bool), `val_count`, `goat_val_count`, `is_empty` | map, bool | `n,n,e` |
| 13 | `iter` / `Debug` (by a bool) | map, bool | pairs / the `{:?}` string |
| 14 | `FromIterator`: owned pairs, `&(K, V)` pairs, `&[u8]` keys into `PathMap<()>` | dst, src, kind | the result |
| 15 | `IntoIterator` of a clone (the original must survive), or of the map itself, rebuilt with `collect` | map, bool | pairs |
| 16 | `clone` | dst, src | soundness of `shared_node_id` |
| 17 | `single`, `From<(K, V)>`, `single_in`, `new`, `default`; or (by `kind / 5`) kinds 0–2 built with `WriteZipperOwned::new`/`new_in` + `descend_to` + `set_val` + `into_map` | map, kind, path, val | the new map |
| 18 | `read_zipper_at_borrowed_path`, `read_zipper_at_path`, `into_read_zipper` + `into_map`; or (by `kind / 3`) kinds 0–1 as `trie_ref_at_path` + `fork_read_zipper` | map, kind, path | dump at the path |
| 19 | `into_write_zipper(p)`, `descend_to(q)`, `set_val`, `into_map` | map, p, q, val | `old\|dump at p` |

A single-map path operand is `Dec.mpath`: half the time an existing location
of that map (a value, a dangling tip, or any), so the ops land on them (17 and 19 take fresh
paths).

Every return renders the whole answer: a value, a flag, or the resulting map
(capped as `dumpAt` caps).

## Semantic decisions

* `get_val_mut_at` must not create the path (as `ZipperWriting::get_val_mut`);
  the closure of `get_val_or_set_mut_with_at` runs exactly when there is no
  value (as `get_val_or_set_mut_with`, `Write.lean`).
* `iter` and `IntoIterator` yield every value, the root value included, in
  depth-first (lexicographic) order: `Map.iter`.  `ReadZipperIter` and
  `OwnedZipperIter` both report the focus value first.
* `FromIterator` is `set_val_at` per pair, so the result has no dangling paths.
* `Debug` renders `{"<key>": <val>, ...}` over every value, the root value
  included (its key is `""`), capped at 100 entries.  A map's contents are its
  key/value pairs, and the root value is one of them.  (The crate omits it;
  `skipDebugRootVal`.)
* `clone` is checked through what `ZipperConcrete` documents as meaningful:
  equal `shared_node_id`s mean the same node, so two maps reporting the same id
  must hold the same contents.  `is_shared` is documented as unreliable ("your
  code must never rely on the return value"), so it is not compared.
  Copy-on-write is checked by every later op and the final dumps: a write to one
  clone that leaked into another shows up there.
* `merkleize` must not change what the map holds; its hash is
  layout-dependent, so only the content is compared.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool dumpAt)

/-- What op 1 appends to a long path (`LONG_TAIL` in `core_ops.rs`): 16
bytes, longer than a `LineListNode` key slot (14), so the crate has to build
continuation nodes.  A representation matter only; the meaning is a path. -/
def longTail : Path := [1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0]

/-- Rust's `str` `Debug` escaping of one byte of an ASCII key. -/
def debugEscByte (b : UInt8) : String :=
  let n := b.toNat
  if n == 0 then "\\0"
  else if n == 9 then "\\t"
  else if n == 10 then "\\n"
  else if n == 13 then "\\r"
  else if n == 34 then "\\\""
  else if n == 92 then "\\\\"
  else if n < 32 || n == 127 then
    "\\u{" ++ String.ofList (Nat.toDigits 16 n) ++ "}"
  else String.singleton (Char.ofNat n)

/-- `format!("{:?}", map)`: a debug map over every key/value pair, keys as
quoted strings, at most 100 entries. -/
def debugFmt (t : PathMap V) : String :=
  let es := (Map.iter t).take 100
  "{" ++ String.intercalate ", " (es.map fun (p, v) =>
    "\"" ++ String.join (p.map debugEscByte) ++ "\": " ++ toString v.toNat) ++ "}"

/-! ## Skip reasons

Same tokens in `differential/src/mapfuzz/{core_ops,lattice}.rs`.  Each stands
for a confirmed crate bug, written up in `lean/findings/map-core.md`, that
would otherwise end comparison on a large share of inputs.

* `skip:debug-root-val` — `Debug` of a map that has a root value: the crate
  leaves the root value out [map_debug_omits_root].
* `skip:map-ident` — the class of a `pjoin` / `psubtract` / `join_all` result
  that equals `self`: the crate reports `Element` for most of them
  [map_alg_ident_closures].  The dump is still compared, so only the
  `Identity`-vs-`Element` precision of that one case goes unchecked. -/

def skipDebugRootVal : String := "skip:debug-root-val"
def skipMapIdent : String := "skip:map-ident"

/-- A path operand for map `t`: `sel := u8`, then for `sel < 128` an index
`k := u8` into a list of `t`'s locations in depth-first order, modulo its
length: `sel < 48` its valued locations, `sel < 80` its dangling tips, else all
its locations (each falling back to all locations when empty).  `sel ≥ 128` is
a fresh path of `sel % 6` bytes.  Random paths alone almost never land on a
value or a dangling tip, which left `prune_path` and the value writers
untested. -/
def _root_.PathMapModel.Fuzz.Dec.mpath (d : Dec) (t : PathMap V) : Option (Path × Dec) := do
  let (sel, d) ← d.u8
  if sel.toNat < 128 then
    let ps :=
      if sel.toNat < 48 then t.vals.map (·.1)
      else if sel.toNat < 80 then t.paths.filter t.isDanglingTip
      else t.paths
    let ps := if ps.isEmpty then t.paths else ps
    let (k, d) ← d.u8
    some (ps.getD (k.toNat % ps.length) [], d)
  else d.pathN (sel.toNat % 6)

/-- Values only: the map rebuilt from its key/value pairs. -/
def valsOnly (t : PathMap V) : PathMap V := PathMap.mk' t.vals []

def stepCore (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 0 => do -- `get` / `get_val_at`
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      some (("get", showVal (Map.getValAt (s.get i) p), s), d)
  | 1 => do -- `insert` / `set_val_at`: returns the old value
      -- The map byte's spare bits: `/3 % 2` picks `insert` (an alias of
      -- `set_val_at`, so the same answer), `/6 % 2` appends `longTail`.
      let (raw, d) ← d.u8; let i := raw.toNat % 3
      let (p0, d) ← d.mpath (s.get i); let (v, d) ← d.val
      let p := if (raw.toNat / 6) % 2 == 1 then p0 ++ longTail else p0
      let (old, t) := Map.setValAt (s.get i) p v
      some (("insert", showVal old, s.set i t), d)
  | 2 => do -- `remove`: `remove_val_at(p, prune = true)`
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      let (old, t) := Map.removeValAt (s.get i) p true
      some (("remove", showVal old, s.set i t), d)
  | 3 => do -- `contains`: a *value* at `p`
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      some (("contains", showBool (Map.contains (s.get i) p), s), d)
  | 4 => do -- every read of one location
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      let t := s.get i
      let e := showBool (Map.pathExistsAt t p)
      let v := showVal (Map.getValAt t p)
      some (("exists", e ++ "|" ++ e ++ "|" ++ v ++ "|" ++ v ++ "|" ++ showVal (t.valAt []), s), d)
  | 5 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i); let (pr, d) ← d.bool
      let (old, t) := Map.removeValAt (s.get i) p pr
      some (("remove_val_at", showVal old, s.set i t), d)
  | 6 => do -- write through `get_val_mut_at`; never creates the path
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i); let (_k, d) ← d.bool; let (v, d) ← d.val
      let t := s.get i
      match t.valAt p with
      | some old => some (("get_val_mut_at", showVal (some old), s.set i (t.setVal p v).2), d)
      | none => some (("get_val_mut_at", "-", s), d)
  | 7 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i); let (dv, d) ← d.val
      let t := s.get i
      let r := (t.valAt p).getD dv
      some (("get_val_or_set_mut_at", showVal (some r), s.set i (t.setVal p (r + 1)).2), d)
  | 8 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i); let (dv, d) ← d.val
      let t := s.get i
      let ran := (t.valAt p).isNone
      let r := (t.valAt p).getD dv
      some (("get_val_or_set_mut_with_at", showVal (some r) ++ ":" ++ showBool ran,
        s.set i (t.setVal p (r + 1)).2), d)
  | 9 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i); let (pr, d) ← d.bool
      let (b, t) := Map.removeBranchesAt (s.get i) p pr
      some (("remove_branches_at", showBool b, s.set i t), d)
  | 10 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      let (n, t) := Map.prunePath (s.get i) p
      some (("prune_path", toString n, s.set i t), d)
  | 11 => do
      let (i, d) ← d.map; let (p, d) ← d.mpath (s.get i)
      let (b, t) := Map.createPath (s.get i) p
      some (("create_path", showBool b, s.set i t), d)
  | 12 => do -- `merkleize` (by a bool) preserves the contents
      let (i, d) ← d.map; let (_m, d) ← d.bool
      let t := s.get i
      let n := toString (Map.valCount t)
      some (("counts", n ++ "," ++ n ++ "," ++ showBool (Map.isEmpty t), s), d)
  | 13 => do
      let (i, d) ← d.map; let (k, d) ← d.bool
      let t := s.get i
      -- `skipDebugRootVal`: the crate's `Debug` omits the root value
      -- (`map_debug_omits_root`), on about a tenth of all inputs.
      if k then some (("debug-fmt", if (t.valAt []).isSome then skipDebugRootVal else debugFmt t, s), d)
      else some (("iter", showPairs ((Map.iter t).take 64), s), d)
  | 14 => do
      let (i, d) ← d.map; let (j, d) ← d.map; let (k, d) ← d.mod 3
      let src := s.get j
      if k == 2 then
        -- `PathMap<()>` from the keys: only its key set is observable.
        some (("from_iter", showPaths (((Map.iter src).map (·.1)).take 64), s), d)
      else
        let t := valsOnly src
        some (("from_iter", dumpAt t [], s.set i t), d)
  | 15 => do
      let (i, d) ← d.map; let (k, d) ← d.bool
      let t := s.get i
      let ret := showPairs ((Map.iter t).take 64)
      if k then some (("into_iter", ret, s.set i (valsOnly t)), d)
      else some (("into_iter", ret, s), d)
  | 16 => do
      let (i, d) ← d.map; let (j, d) ← d.map
      some (("clone", "1", s.set i (s.get j)), d)
  | 17 => do
      let (i, d) ← d.map; let (k, d) ← d.mod 5; let (p, d) ← d.path; let (v, d) ← d.val
      let t : PathMap V := if k < 3 then Map.single p v else Map.new
      some (("single", dumpAt t [], s.set i t), d)
  | 18 => do
      let (i, d) ← d.map; let (_k, d) ← d.mod 3; let (p, d) ← d.mpath (s.get i)
      some (("read_zipper_at", dumpAt (s.get i) p, s), d)
  | 19 => do
      let (i, d) ← d.map; let (p, d) ← d.path 4; let (q, d) ← d.path 4; let (v, d) ← d.val
      let (old, t) := (s.get i).setVal (p ++ q) v
      some (("into_write_zipper", showVal old ++ "|" ++ dumpAt t p, s.set i t), d)
  | _ => some (("nop", "-", s), d)

/-! ## Fixtures -/

#guard debugFmt (PathMap.mk' [([0, 1], (5 : UInt64)), ([], 7)] []) = "{\"\": 7, \"\\0\\u{1}\": 5}"
#guard debugFmt (PathMap.empty : PathMap V) = "{}"
#guard (valsOnly (PathMap.mk' [([0], (5 : UInt64))] [[1, 2]])).paths = [[], [0]]

end MapFuzz
end PathMapModel
