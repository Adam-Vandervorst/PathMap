import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 0–29: ByteMask, BitMask for [u64; 4], other utils/mod.rs items

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

def stepMask (_op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  some (("nop", "-"), d)

end UtilFuzz
end PathMapModel
