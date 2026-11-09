import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 0–19: the `PathMap` surface

`PathMap`'s own methods, against `Map.lean`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool)

def stepCore (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 0 => do -- `get` / `get_val_at`
      let (i, d) ← d.map; let (p, d) ← d.path
      some (("get", showVal (Map.getValAt (s.get i) p), s), d)
  | 1 => do -- `insert` / `set_val_at`: returns the old value
      let (i, d) ← d.map; let (p, d) ← d.path; let (v, d) ← d.val
      let (old, t) := Map.setValAt (s.get i) p v
      some (("insert", showVal old, s.set i t), d)
  | 2 => do -- `remove`: `remove_val_at(p, prune = true)`
      let (i, d) ← d.map; let (p, d) ← d.path
      let (old, t) := Map.removeValAt (s.get i) p true
      some (("remove", showVal old, s.set i t), d)
  | 3 => do -- `contains`: a *value* at `p`
      let (i, d) ← d.map; let (p, d) ← d.path
      some (("contains", showBool (Map.contains (s.get i) p), s), d)
  | _ => some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
