import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 80–99: path sorting (sort_paths, sort_paths_par) and the rest

Not written yet: every selector in the range is a `nop`.
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

def stepMisc (_op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  some (("nop", "-"), d)

end UtilFuzz
end PathMapModel
