import PathMapModel.UtilFuzz.Mask
import PathMapModel.UtilFuzz.Lattice
import PathMapModel.UtilFuzz.Ints
import PathMapModel.UtilFuzz.Misc

/-! # The util fuzzer: dispatch and entry point (see `UtilFuzz/Base.lean`) -/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

def step (d : Dec) : Option ((String × String) × Dec) := do
  let (opRaw, d) ← d.u8
  let op := opRaw.toNat % d.opCount
  if op < 30 then stepMask op d
  else if op < 60 then stepLattice op d
  else if op < 80 then stepInts op d
  else if op < 100 then stepMisc op d
  else some (("nop", "-"), d)

def loop : Nat → Nat → Dec → List String → List String
  | 0, _, _, out => out
  | n + 1, i, d, out =>
      match step d with
      | some ((name, ret), d') => loop n (i + 1) d' ((toString i ++ " " ++ name ++ " ret=" ++ ret) :: out)
      | none => out

def run (bytes : ByteArray) (maxSteps : Nat := 256) : List String :=
  match Dec.init bytes with
  | none => ["EMPTY"]
  | some d => (loop maxSteps 0 d []).reverse

end UtilFuzz
end PathMapModel
