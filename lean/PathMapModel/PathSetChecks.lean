import PathMapModel.PathSetLaws
import PathMapModel.PathSetProofs

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace PathMapModel.PathSetChecks
open PathSpace

def small : List PathSpace := [[], [[]], [[0]], [[1]], [[],[0]], [[],[1]], [[0],[1]], [[],[0],[1]]]
def fixtures : List PathSpace := small ++
  [[[0],[0,0],[0,1]], [[0,0],[0,1]], [[0],[1,0],[1,1,0],[1,1,1]],
   [[255,0],[255,255]], [[0,0,0],[1],[0,1],[0,0,1]]]

#guard (small.flatMap fun a => small.flatMap fun b => small.flatMap fun c =>
  small.map fun f => (PathSetLaws.failures (PathSetLaws.all a b c f)).isEmpty).all id
#guard (fixtures.flatMap fun a => fixtures.map fun b =>
  (PathSetLaws.failures (PathSetLaws.unary a ++ PathSetLaws.binary a b)).isEmpty).all id
#guard (fixtures.flatMap fun a => (List.range 4).flatMap fun m => (List.range 4).map fun n =>
  (PathSetLaws.failures (PathSetLaws.powers a m n)).isEmpty).all id

-- Counterexamples are positively checked: these are NOT proposed rewrite rules.
#guard !equiv (divergence (divergence [[0,0]] [[0,1]]) [[1]])
  (divergence [[0,0]] (divergence [[0,1]] [[1]]))
#guard !equiv (divergence (inter [[0,0]] [[0,1]]) [[1]])
  (inter (divergence [[0,0]] [[1]]) (divergence [[0,1]] [[1]]))
#guard !equiv (divergence (diff [[0,0],[0,1]] [[0,0]]) [[1]])
  (diff (divergence [[0,0],[0,1]] [[1]]) (divergence [[0,0]] [[1]]))
#guard !equiv (restrict (divergence [[0,0]] [[0,1]]) [[0,0],[0,1]])
  (divergence (restrict [[0,0]] [[0,0],[0,1]]) (restrict [[0,1]] [[0,0],[0,1]]))
#guard !equiv (divergence (product [[0]] [[2]]) (product [[0,1]] [[2]])) (divergence [[0]] [[0,1]])
#guard !equiv (divergence [[0],[1,0],[1,1,0],[1,1,1]] (branches [[0],[1,0],[1,1,0],[1,1,1]]))
  (branches (branches [[0],[1,0],[1,1,0],[1,1,1]]))
#guard !equiv (divergence [[0,0],[0,1]] [[0]]) (divergence [[0,0],[0,1]] [[0,0]])
#guard !equiv (branches [[0],[0,0],[0,1]]) (branches (basis [[0],[0,0],[0,1]]))
#guard equiv (branches [[102,111,111],[102,111,111,100]]) [] -- foo / food
#guard equiv (divergence [[102,111,111,100]] [[102,111,117,114]]) [[102,111]] -- food / four
#guard count (divergence [[0,0,0]] [[1],[0,1],[0,0,1]]) == 3

-- The map adapter retains values; bare paths do not supply witnesses.
def valued : PathMap Nat := PathMap.mk' [([0],10),([0,1],20),([2],30)] [[0,1,255],[3,4]]
#guard (Map.basis valued).valAt [0] == some 10
#guard (Map.basis valued).valAt [0,1] == none
#guard (Map.hull valued).valAt [0,1] == some 20
#guard (Map.hull valued).valAt [0] == none
#guard equiv (ofMap (Map.branches valued)) [[]]
#guard equiv (ofMap (Map.divergence valued (PathMap.mk' ([] : List (Path × Nat)) [[4,5]]))) []
end PathMapModel.PathSetChecks
