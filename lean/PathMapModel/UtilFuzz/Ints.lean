import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 60–79: `utils/ints.rs`: PathInteger

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

def stepInts (_op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  some (("nop", "-"), d)

end UtilFuzz
end PathMapModel
