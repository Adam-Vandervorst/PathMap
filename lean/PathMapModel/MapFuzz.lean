import PathMapModel.MapFuzz.Core
import PathMapModel.MapFuzz.Lattice
import PathMapModel.MapFuzz.Serial
import PathMapModel.MapFuzz.Act
import PathMapModel.MapFuzz.Morph
import PathMapModel.MapFuzz.Head
import PathMapModel.MapFuzz.Exp

/-!
# The map-level fuzzer: dispatch and entry point

See `MapFuzz/Base.lean` for the format and the op ranges.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec dumpAt)

/-- Decode and run one operation; `none` once the input runs out. -/
def step (s : MSt) (d : Dec) : Option (MSt × Dec) := do
  let (opRaw, d) ← d.u8
  let op := opRaw.toNat % d.opCount
  let ((name, ret, s), d) ←
    if op < 20 then stepCore op s d
    else if op < 30 then stepLattice op s d
    else if op < 40 then stepSerial op s d
    else if op < 50 then stepAct op s d
    else if op < 60 then stepMorph op s d
    else if op < 70 then stepHead op s d
    else if op < 80 then stepExp op s d
    else some (("nop", "-", s), d)
  some (emit s name ret, d)

def loop : Nat → MSt → Dec → MSt
  | 0, s, _ => s
  | n + 1, s, d =>
      match step s d with
      | some (s', d') => loop n s' d'
      | none => s

def header (d : Dec) : Option (MSt × Dec) := do
  let (n0, d) ← d.mod 8
  let (m0, d) ← Fuzz.seed PathMap.empty d n0
  let (n1, d) ← d.mod 8
  let (m1, d) ← Fuzz.seed PathMap.empty d n1
  let (n2, d) ← d.mod 8
  let (m2, d) ← Fuzz.seed PathMap.empty d n2
  some ({ m0, m1, m2 }, d)

def run (bytes : ByteArray) (maxSteps : Nat := 256) : List String :=
  match Dec.init bytes >>= header with
  | none => ["EMPTY"]
  | some (s0, d) =>
      let s := loop maxSteps s0 d
      s.out.reverse ++
        [ "M0 " ++ dumpAt s.m0 [], "M1 " ++ dumpAt s.m1 [], "M2 " ++ dumpAt s.m2 [] ]

end MapFuzz
end PathMapModel
