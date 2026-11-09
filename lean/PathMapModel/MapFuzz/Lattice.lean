import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 20–29: whole-map lattice ops

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec)

def stepLattice (_op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
