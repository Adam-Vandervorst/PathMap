import PrunedModel.Convex.PathSetLaws
import PrunedModel.Convex.Map

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace PrunedModel.Convex.PathSetChecks
open PathMapModel
open PrunedModel.Convex

def small : List PathSpace := [(ofPaths []), (ofPaths [[]]), (ofPaths [[0]]), (ofPaths [[1]]), (ofPaths [[],[0]]), (ofPaths [[],[1]]), (ofPaths [[0],[1]]), (ofPaths [[],[0],[1]])]
def fixtures : List PathSpace := small ++
  [(ofPaths [[0],[0,0],[0,1]]), (ofPaths [[0,0],[0,1]]), (ofPaths [[0],[1,0],[1,1,0],[1,1,1]]),
   (ofPaths [[255,0],[255,255]]), (ofPaths [[0,0,0],[1],[0,1],[0,0,1]])]

#guard (small.flatMap fun a => small.flatMap fun b => small.flatMap fun c =>
  small.map fun f => (PathSetLaws.failures (PathSetLaws.all a b c f)).isEmpty).all id
#guard (fixtures.flatMap fun a => fixtures.map fun b =>
  (PathSetLaws.failures (PathSetLaws.unary a ++ PathSetLaws.binary a b)).isEmpty).all id
#guard (fixtures.flatMap fun a => (List.range 4).flatMap fun m => (List.range 4).map fun n =>
  (PathSetLaws.failures (PathSetLaws.powers a m n)).isEmpty).all id

-- Counterexamples are positively checked: these are NOT proposed rewrite rules.
#guard !equiv (divergence (divergence (ofPaths [[0,0]]) (ofPaths [[0,1]])) (ofPaths [[1]]))
  (divergence (ofPaths [[0,0]]) (divergence (ofPaths [[0,1]]) (ofPaths [[1]])))
#guard !equiv (divergence (inter (ofPaths [[0,0]]) (ofPaths [[0,1]])) (ofPaths [[1]]))
  (inter (divergence (ofPaths [[0,0]]) (ofPaths [[1]])) (divergence (ofPaths [[0,1]]) (ofPaths [[1]])))
#guard !equiv (divergence (diff (ofPaths [[0,0],[0,1]]) (ofPaths [[0,0]])) (ofPaths [[1]]))
  (diff (divergence (ofPaths [[0,0],[0,1]]) (ofPaths [[1]])) (divergence (ofPaths [[0,0]]) (ofPaths [[1]])))
#guard !equiv (restrict (divergence (ofPaths [[0,0]]) (ofPaths [[0,1]])) (ofPaths [[0,0],[0,1]]))
  (divergence (restrict (ofPaths [[0,0]]) (ofPaths [[0,0],[0,1]])) (restrict (ofPaths [[0,1]]) (ofPaths [[0,0],[0,1]])))
#guard !equiv (divergence (product (ofPaths [[0]]) (ofPaths [[2]])) (product (ofPaths [[0,1]]) (ofPaths [[2]]))) (divergence (ofPaths [[0]]) (ofPaths [[0,1]]))
#guard !equiv (divergence (ofPaths [[0],[1,0],[1,1,0],[1,1,1]]) (branches (ofPaths [[0],[1,0],[1,1,0],[1,1,1]])))
  (branches (branches (ofPaths [[0],[1,0],[1,1,0],[1,1,1]])))
#guard !equiv (divergence (ofPaths [[0,0],[0,1]]) (ofPaths [[0]])) (divergence (ofPaths [[0,0],[0,1]]) (ofPaths [[0,0]]))
#guard !equiv (branches (ofPaths [[0],[0,0],[0,1]])) (branches (basis (ofPaths [[0],[0,0],[0,1]])))
#guard equiv (branches (ofPaths [[102,111,111],[102,111,111,100]])) (ofPaths []) -- foo / food
#guard equiv (divergence (ofPaths [[102,111,111,100]]) (ofPaths [[102,111,117,114]])) (ofPaths [[102,111]]) -- food / four
#guard count (divergence (ofPaths [[0,0,0]]) (ofPaths [[1],[0,1],[0,0,1]])) == 3

-- Payload operators preserve the original values at selected paths.
def valued : PrunedMap Nat := PrunedMap.mk' [([0],10),([0,1],20),([2],30)]
#guard valued.basis.valAt [0] == some 10
#guard valued.basis.valAt [0,1] == none
#guard valued.hull.valAt [0,1] == some 20
#guard valued.hull.valAt [0] == none
#guard equiv valued.branches (ofPaths [[]])
#guard equiv (valued.divergence (PrunedMap.empty : PrunedMap Nat)) (ofPaths [])
end PrunedModel.Convex.PathSetChecks
