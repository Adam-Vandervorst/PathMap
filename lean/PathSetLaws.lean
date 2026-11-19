import LawExport

/-! Export the sorry-free path-set and convex laws from `PrunedModel.Convex`.
Run `lake env lean --run PathSetLaws.lean > ../differential/src/algebraic/path_set_laws.rs`.
Membership equivalences are lifted only at unrestricted universally quantified
paths. `Same`, inclusion, closure and antichain predicates use their finite-set
equations. Unsupported statements are listed in the generated file. -/

open LawExport

def main : IO Unit := LawExport.generate {
  ns := `PrunedModel.Convex
  module := `PrunedModel.Convex
  submodules := true
  generator := "PathSetLaws"
  output := "path_set_laws"
  namePrefix := "path_set/"
  pathSets := true
  ops := zippyOps ++ [
    (`PrunedModel.Convex.union, "union", [.space, .space]),
    (`PrunedModel.Convex.inter, "inter", [.space, .space]),
    (`PrunedModel.Convex.diff, "subtr", [.space, .space]),
    (`PrunedModel.Convex.product, "composition", [.space, .space]),
    (`PrunedModel.Convex.restrict, "restriction", [.space, .space]),
    (`PrunedModel.Convex.raffinate, "raffination", [.space, .space]),
    (`PrunedModel.Convex.retain, "retain", [.space, .space]),
    (`PrunedModel.Convex.divergence, "divergence", [.space, .space]),
    (`PrunedModel.Convex.branches, "branches", [.space]),
    (`PrunedModel.Convex.basis, "basis", [.space]),
    (`PrunedModel.Convex.hull, "hull", [.space]),
    (`PrunedModel.Convex.interior, "interior", [.space]),
    (`PrunedModel.Convex.completion, "completion", [.space]),
    (`PrunedModel.Convex.lcpProduct, "lcp_product", [.space, .space]),
    (`PrunedModel.Convex.convexMeet, "convex_meet", [.space, .space]),
    (`PrunedModel.Convex.convexSubtract, "convex_subtract", [.space, .space]),
    (`PrunedModel.Convex.convexLiteralSubtract, "convex_literal_subtract", [.space, .space]),
    (`PrunedModel.Convex.symDiff, "sym_diff", [.space, .space]),
    (`PrunedModel.Convex.head, "head", [.space]),
    (`PrunedModel.Convex.tails, "tails_union", [.space]),
    (`PrunedModel.Convex.wrap, "wrap", [.path, .space]),
    (`PrunedModel.Convex.unwrap, "unwrap", [.space, .path])]
}
