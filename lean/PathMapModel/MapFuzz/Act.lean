import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 40–49: ArenaCompactTree files, merge, stream

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec)

def stepAct (_op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
