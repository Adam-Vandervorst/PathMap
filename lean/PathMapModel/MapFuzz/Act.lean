import PathMapModel.MapFuzz.Base
import PathMapModel.MapFuzz.Serial

/-!
# Map fuzzer, ops 40–49: ArenaCompactTree files, merge, stream

An `ArenaCompactTree` (`src/arena_compact.rs`) is a read-only image of a trie
with `u64` values.  Every way of producing one is a function of a trie, and the
model is that trie:

* `from_zipper`, `from_zipper_cached`, `dump_from_zipper` (straight to a file)
  and `open_mmap` of the bytes written: the subtrie under the zipper, **root
  value and dangling paths included** (the same view `Source.act` gives the
  read source), each value passed through the caller's `u64` mapping.
  `dump_from_zipper` documents (and its doc test asserts) that it writes the
  same bytes as `from_zipper`; `open_mmap` of `get_data()` reads back the same
  bytes.  `open_mmap` of a file that does not start with the magic is an
  `Err`.
* `merge_zipper_into_file`: a join where the zipper's value wins on a
  collision (the method's doc), so `paths = base ∪ src` (dangling included)
  and `val = src's, else base's`.  "If the zipper adds nothing, the file is
  left untouched": `root_history()` grows by one exactly when the merged trie
  differs from the base.
* `ACTOutputStream`: `push_val` paths in strictly increasing order; a path not
  greater than the last *accepted* one is rejected with `InvalidInput` and
  leaves the stream as it was; `push` is `push_val(_, 0)`.  The result holds
  exactly the accepted `(path, value)` pairs, no dangling paths.  The line
  cache limit (`with_cache_limit`, `0` disables it) never changes contents.
* `get_val_at` (and the deprecated `get`), `iter` (every value, root first,
  depth-first), `read_zipper_at_borrowed_path[_u64]`: the trie's values and
  subtries.  Op 48 also reads the unit-valued zipper over the whole tree
  (`read_zipper`, `Value = ()`): every location with whether it has a value
  (`val`, which `get_val` must agree with), `val_at(q)` / `get_val_at(q)` from
  the root, and `fork_read_zipper` at `q` (none where `q` is missing).

Value mappings: `0` identity, `1` `v * 0x0101010101010101` (eight-byte
varints), `2` `!v` (the nine-byte varint form).

The ACT's `val_count` is wrong below the root (known, `val_count_ignores_focus`)
and `descend_last_path` overshoots (known, `last_path_overshoots`); no op here
uses either.  `Counters` only count with the `act_counters` feature, so they
are not observable in this build.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool dumpAt)

namespace Act

open Serial (graftAt)

/-- The value mapping selected by the op's `mode` operand. -/
def fmap (mode : Nat) (v : V) : V :=
  match mode with
  | 0 => v
  | 1 => v * 0x0101010101010101
  | _ => ~~~v

/-- The ACT built from a zipper over `t`'s root: `t` itself with mapped values. -/
def actOf (mode : Nat) (t : PathMap V) : PathMap V :=
  PathMap.mk' (t.vals.map fun (k, v) => (k, fmap mode v)) t.paths

/-- `merge_zipper_into_file`: union, the zipper's (`src`'s) value winning. -/
def mergeR (base src : PathMap V) : PathMap V :=
  PathMap.mk' (src.vals ++ base.vals) (base.paths ++ src.paths)

def same (a b : PathMap V) : Bool := a.entries == b.entries

/-- Push a list of `(path, value)` into an `ACTOutputStream`: which were
accepted (`1`/`0`) and the pairs held.  A value `≡ 0 mod 4` is pushed with
`push` (value `0`). -/
def streamRaw (xs : List (Path × V)) : String × List (Path × V) :=
  let step := fun (acc : Option Path × List (Path × V) × String) (kv : Path × V) =>
    let (prev, held, bits) := acc
    let ok := match prev with
      | none => true
      | some pr => Path.lt pr kv.1
    if ok then
      let v : V := if kv.2.toNat % 4 == 0 then 0 else kv.2
      (some kv.1, held ++ [(kv.1, v)], bits ++ "1")
    else (prev, held, bits ++ "0")
  let (_, held, bits) := xs.foldl step (none, [], "")
  (if bits.isEmpty then "-" else bits, held)

/-- Every location of `t` at and below `q`, relative to `q`, capped like a dump. -/
def walkPaths (t : PathMap V) (q : Path) : List Path := ((t.subtrie q).paths).take 64

/-- Op 48's walk of a unit-valued `ACTZipper` rooted at `q` (`unit_walk` in
act.rs): each location `hexPath` + `v`/`-`; `get_val` must agree with `val`
(the crate marks a disagreement `!`, which the model never prints). -/
def unitWalk (t : PathMap V) (q : Path) : String :=
  let u := t.subtrie q
  String.intercalate "/" ((u.paths.take 64).map fun p => hexPath p ++ (if (u.valAt p).isSome then "v" else "-"))

def decPairs (d : Dec) : Nat → Option (List (Path × V) × Dec)
  | 0 => some ([], d)
  | n + 1 => do
      let (p, d) ← d.path; let (v, d) ← d.val
      let (rest, d) ← decPairs d n
      some ((p, v) :: rest, d)

def decPaths (d : Dec) (lim : Nat) : Nat → Option (List Path × Dec)
  | 0 => some ([], d)
  | n + 1 => do
      let (p, d) ← d.path lim
      let (rest, d) ← decPaths d lim n
      some (p :: rest, d)

end Act

open Act Serial in
def stepAct (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 40 => do -- `dump_from_zipper` to a file; same bytes as `from_zipper`
      let (i, d) ← d.map; let (p, d) ← d.path; let (mode, d) ← d.mod 3
      let t := actOf mode ((s.get i).subtrie p)
      some (("act_dump", dumpAt t [] ++ ";same=1", s), d)
  | 41 => do -- `from_zipper` → file → `open_mmap`; a truncated file
      let (i, d) ← d.map; let (p, d) ← d.path; let (mode, d) ← d.mod 3
      let (k, d) ← d.mod 20
      let t := actOf mode ((s.get i).subtrie p)
      -- A file shorter than the magic (empty included) should be an `Err`, but
      -- makes `open_mmap` panic (finding `act_open_short_panics`); it is skipped
      -- by name so the panic does not take the rest of the input with it.
      let trunc := if k < 8 then "skip:act_open_short" else "ok"
      some (("act_open", dumpAt t [] ++ ";same=1;trunc=" ++ trunc, s), d)
  | 42 => do -- `merge_zipper_into_file` once
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map; let (q, d) ← d.path
      let (mode, d) ← d.mod 3
      let base := actOf mode ((s.get i).subtrie p)
      let src := actOf mode ((s.get j).subtrie q)
      let m := mergeR base src
      let h := 1 + (if same m base then 0 else 1)
      some (("act_merge", dumpAt m [] ++ ";h=" ++ toString h, s), d)
  | 43 => do -- two merges into the same file: the root history chains
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map; let (q, d) ← d.path
      let (k, d) ← d.map; let (r, d) ← d.path; let (mode, d) ← d.mod 3
      let base := actOf mode ((s.get i).subtrie p)
      let m1 := mergeR base (actOf mode ((s.get j).subtrie q))
      let m2 := mergeR m1 (actOf mode ((s.get k).subtrie r))
      let h := 1 + (if same m1 base then 0 else 1) + (if same m2 m1 then 0 else 1)
      some (("act_merge2", dumpAt m2 [] ++ ";h=" ++ toString h, s), d)
  | 44 => do -- `ACTOutputStream` fed a map's values in order
      let (i, d) ← d.map; let (p, d) ← d.path; let (mode, d) ← d.mod 3
      let (_cache, d) ← d.mod 4
      let t := Serial.valsOnly (actOf mode ((s.get i).subtrie p))
      some (("act_stream", dumpAt t [], s), d)
  | 45 => do -- `ACTOutputStream` fed arbitrary paths: order check
      let (_cache, d) ← d.mod 4; let (n, d) ← d.mod 6
      let (xs, d) ← decPairs d n
      let (bits, held) := streamRaw xs
      some (("act_stream_raw", bits ++ ";" ++ dumpAt (PathMap.mk' held []) [], s), d)
  | 46 => do -- `from_zipper_cached` over a trie with map j grafted at 1–3 prefixes
      let (i, d) ← d.map; let (p, d) ← d.path; let (j, d) ← d.map
      let (n, d) ← d.mod 3; let (pres, d) ← decPaths d 4 (n + 1)
      let (mode, d) ← d.mod 3
      let tmp := pres.foldl (fun t a => graftAt t a (s.get j)) (s.get i)
      some (("act_cached", dumpAt (actOf mode (tmp.subtrie p)) [], s), d)
  | 47 => do -- `get_val_at` / `get` at a few paths; `iter`
      let (i, d) ← d.map; let (p, d) ← d.path; let (mode, d) ← d.mod 3
      let (n, d) ← d.mod 4; let (qs, d) ← decPaths d 6 n
      let t := actOf mode ((s.get i).subtrie p)
      let gets := qs.map (fun q => showVal (t.valAt q) ++ "/" ++ showVal (t.valAt q))
      let g := if gets.isEmpty then "-" else String.intercalate "," gets
      some (("act_get", g ++ ";" ++ showPairs t.vals, s), d)
  | 48 => do -- `read_zipper_at_borrowed_path_u64` / `read_zipper_at_borrowed_path` / `read_zipper`
      let (i, d) ← d.map; let (p, d) ← d.path; let (q, d) ← d.path; let (mode, d) ← d.mod 3
      let t := actOf mode ((s.get i).subtrie p)
      let fork := if t.pathExists q then unitWalk t q else "_"
      some (("act_zipper_at", dumpAt t q ++ ";" ++ showPaths (walkPaths t q) ++ ";U" ++ unitWalk t []
        ++ ";a" ++ showBool (t.valAt q).isSome ++ ";F" ++ fork, s), d)
  | _ => some (("nop", "-", s), d)

/-! ## Fixtures -/

namespace Act

private def fx : PathMap V := PathMap.mk' [([], 7), ([1, 2], 3)] [[2, 2]]

#guard (mergeR fx (PathMap.mk' [([1, 2], 9)] [[3]])).vals == [([], 7), ([1, 2], 9)]
#guard (mergeR fx (PathMap.mk' [([1, 2], 9)] [[3]])).paths.contains [2, 2]
#guard (mergeR fx (PathMap.mk' [([1, 2], 9)] [[3]])).paths.contains [3]
#guard same (mergeR fx (PathMap.mk' [([1, 2], 3)] [[2]])) fx
#guard streamRaw [([1], 5), ([1], 6), ([1, 0], 4), ([0], 1)] == ("1010", [([1], 5), ([1, 0], 0)])
#guard streamRaw [([], 5), ([], 6)] == ("10", [([], 5)])
#guard fmap 2 (0 : V) == 0xFFFFFFFFFFFFFFFF
#guard fmap 1 (2 : V) == 0x0202020202020202

end Act

end MapFuzz
end PathMapModel
