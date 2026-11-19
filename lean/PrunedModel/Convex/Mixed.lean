import PrunedModel.Convex.Map
import PathMapModel.Map

/-! The mixed fuzzer can contain dangling paths. Convex and path-set operations observe its
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

def basis {V : Type} (a out : Zip V) : Zip V :=
  out.graftMap (mixed (pruned a.makeMap).basis)
def hull {V : Type} (a out : Zip V) : Zip V :=
  out.graftMap (mixed (pruned a.makeMap).hull)
def retain {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) : Zip V :=
  out.graftMap (mixed ((pruned a.makeMap).retain (pruned b.makeMap)))

/-- Mark the pruned model's unit-valued branch points with a caller's payload. -/
private def marks {V : Type} (a : PrunedModel.PrunedMap Unit) (v : V) : PathMap V :=
  PathMap.mk' (a.entries.map fun (p, _) => (p, v)) []

def divergence {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) (v : V) : Zip V :=
  out.graftMap (marks ((pruned a.makeMap).divergence (pruned b.makeMap)) v)
def branches {V : Type} (a out : Zip V) (v : V) : Zip V :=
  out.graftMap (marks (pruned a.makeMap).branches v)

end Zip
end PathMapModel
