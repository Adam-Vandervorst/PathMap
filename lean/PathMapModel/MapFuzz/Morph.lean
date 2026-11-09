import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 50–59: catamorphisms, anamorphisms

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec)

def stepMorph (_op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
