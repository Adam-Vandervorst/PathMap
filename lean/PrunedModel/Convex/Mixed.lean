import PrunedModel.Convex.Map
import PathMapModel.Map

/-! The mixed fuzzer can contain dangling paths. Convex operations observe its
valued projection in the pruned model, then graft the canonical result back.
All operation definitions and laws live in the pruned model. -/
namespace PathMapModel

private def pruned {V : Type} (a : PathMap V) : PrunedModel.PrunedMap V :=
  PrunedModel.PrunedMap.mk' a.vals
private def mixed {V : Type} (a : PrunedModel.PrunedMap V) : PathMap V :=
  PathMap.mk' a.entries []

namespace Zip

def convexMeet {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) : Zip V :=
  out.graftMap (mixed ((pruned a.makeMap).convexMeet (pruned b.makeMap)))
def convexSubtract {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) : Zip V :=
  out.graftMap (mixed ((pruned a.makeMap).convexSubtract (pruned b.makeMap)))

end Zip
end PathMapModel
