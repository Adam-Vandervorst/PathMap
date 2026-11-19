import LawExport
import PrunedModel.Convex

/-! Regression checks for the logical boundary of theorem export. -/
open Lean Meta LawExport PrunedModel

namespace LawExport.Checks

private def config : Config := {
  ns := `PrunedModel.Convex, module := `PrunedModel.Convex
  generator := "PathSetLaws", output := "path_set_laws", pathSets := true
  ops := zippyOps ++ [
    (`PrunedModel.Convex.basis, "basis", [.space]),
    (`PrunedModel.Convex.hull, "hull", [.space]),
    (`PrunedModel.Convex.retain, "retain", [.space, .space])]
}

private theorem restricted (a b : PathSpace) (p : PathMapModel.Path)
    (ha : p ∉ a) (hb : p ∉ b) : p ∈ a ↔ p ∈ b := iff_of_false ha hb

private theorem dependent (p : PathMapModel.Path) :
    p ∈ Zippy.singleton p ↔ p ∈ Zippy.singleton p := Iff.rfl

run_meta do
  for n in [``restricted, ``dependent] do
    forallTelescope (← getConstInfo n).type fun xs body => do
      unless (← pointwiseEquation xs body).isNone do
        throwError "unsound extensional lifting of {n}"
  let .ok idem ← translate config (← getConstInfo ``Convex.basis_idempotent).type
    | throwError "basis idempotence was not exported"
  unless idem.paths == 0 && idem.pre.isEmpty &&
      idem.lhs == "basis(basis(s(0)))" && idem.rhs == "basis(s(0))" do
    throwError "incorrect lifting of basis idempotence"
  let .ok conditional ← translate config (← getConstInfo ``Convex.hull_of_antichain).type
    | throwError "conditional hull law was not exported"
  unless conditional.pre == #["eq_space(basis(s(0)), s(0))"] &&
      conditional.lhs == "hull(s(0))" && conditional.rhs == "s(0)" do
    throwError "antichain hypothesis was lost or mistranslated"
  let .ok included ← translate config (← getConstInfo ``Convex.hull_retain).type
    | throwError "inclusion hypothesis was not exported"
  unless included.pre == #["eq_space(inter(s(1), hull(s(0))), s(1))"] do
    throwError "inclusion hypothesis was lost or mistranslated"
  -- A non-equational conclusion must be rejected without probing absent args.
  let .error _ ← translate config (← getConstInfo ``Convex.mem_hull).type
    | throwError "unsupported quantified membership formula was exported"

end LawExport.Checks
