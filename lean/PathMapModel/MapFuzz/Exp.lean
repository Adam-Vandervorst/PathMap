import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 70–79: experimental zippers

Every selector in the range is a `nop`, on purpose.  The group was meant for
`FullZipper` and `NullZipper` in `src/experimental.rs`, but both are private
(no `pub`, no public constructor), so the fuzzer cannot build them.  See
`lean/findings/overlay-exp.md`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec)

def stepExp (_op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
