import LawExport

/-! Export the sorry-free equational laws of `PrunedModel.Zippy`.
Run `lake env lean --run ZippyLaws.lean > ../differential/src/algebraic/zippy_laws.rs`.
The shared exporter records every unsupported theorem and its reason. -/

def main : IO Unit := LawExport.generate {
  ns := `PrunedModel.Zippy
  module := `PrunedModel.Zippy
  generator := "ZippyLaws"
  output := "zippy_laws"
  ops := LawExport.zippyOps
}
