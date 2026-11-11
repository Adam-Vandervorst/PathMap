import PathMapModel.Spec
import PathMapModel.Fuzz
import PathMapModel.Hash
import PathMapModel.GraftNoop

/-!
# Build-time checks

Two kinds of `#guard`, both evaluated by the Lean compiler on every build:

* **Regression fixtures** transcribed from `pathmap`'s own unit tests
  (`src/write_zipper.rs`).  These pin the model to observed crate behaviour for
  the operations whose semantics are hardest to read off the source — pruning
  and `drop_head`.
* **Law checks**: the metamorphic properties from `Spec.Laws`, evaluated over a
  battery of tries chosen to cover branch points, single-child runs, values at
  interior nodes, dangling paths, and the empty trie.
-/

namespace PathMapModel
namespace Check

open Laws

abbrev T := PathMap UInt64
def ops : ValOps UInt64 := u64Ops

/-! Build a trie from a list of path/value pairs. -/
def mk (entries : List (Path × Nat)) : T :=
  entries.foldl (fun t kv => (t.setVal kv.1 (UInt64.ofNat kv.2)).2) PathMap.empty

def zipAt (t : T) (root path : Path) : Zip UInt64 := { trie := t, root, path }

/-! ## Fixtures -/

/-- Branching at the root and at depth 1, with a value at an interior node. -/
def fBranch : T := mk [([], 0), ([0], 1), ([0,0], 2), ([0,1], 3), ([1], 4)]
/-- A single-child run: the shape `descend_until` / `ascend_until` care about. -/
def fRun : T := mk [([0,0,0,0], 7)]
/-- Overlapping prefixes without a root value. -/
def fSide : T := mk [([0,0], 9), ([0,2], 8), ([2], 7)]
/-- The empty trie. -/
def fEmpty : T := PathMap.empty
/-- A dangling path: `[0,1,2]` exists but carries no value. -/
def fDangle : T := (mk [([0], 5)]).addPath [0,1,2]
/-- Two values under a shared 2-byte prefix, plus a deeper third. -/
def fDeep : T := mk [([1,1,0], 1), ([1,1,1], 2), ([1,1,1,3], 3)]

def fixtures : List T := [fBranch, fRun, fSide, fEmpty, fDangle, fDeep]

/-- Focus positions worth probing in each fixture. -/
def probes : List Path := [[], [0], [1], [0,0], [0,1], [1,1], [0,1,2], [3]]

def allZips : List (Zip UInt64) :=
  fixtures.flatMap (fun t => probes.map (fun p => zipAt t [] p))

/-! The selector count belongs to each input, independent of the current operation table. -/

def inputWithCount (lo hi : UInt8) : ByteArray :=
  ByteArray.mk (Fuzz.wireMagic ++ [lo, hi]).toArray

#guard ((Fuzz.Dec.init (ByteArray.mk #[])).map (·.opCount)) == some 56
#guard ((Fuzz.Dec.init (inputWithCount 56 0)).map (·.opCount)) == some 56
#guard ((Fuzz.Dec.init (inputWithCount 58 0)).map (·.opCount)) == some 58
#guard ((Fuzz.Dec.init (inputWithCount 0 1)).map (·.opCount)) == some 256
#guard (Fuzz.Dec.init (inputWithCount 0 0)).isNone
#guard (Fuzz.Dec.init (inputWithCount 1 1)).isNone
#guard (Fuzz.Dec.init (ByteArray.mk Fuzz.wireMagic.toArray)).isNone
#guard (Fuzz.Dec.init (ByteArray.mk (Fuzz.wireMagic ++ [57]).toArray)).isNone

/-- Preserve inputs recorded on both sides of the master/Merkle opcode collision. -/
def programWithCount (count : UInt8) (program : List UInt8) : ByteArray :=
  ByteArray.mk (Fuzz.wireMagic ++ [count, 0] ++ program).toArray

#guard [false, true].all (fun act =>
  Fuzz.run (programWithCount 61 [0, 0, 0, 0, 60, 1, 2, 7, 27, 9]) 256 act ==
  Fuzz.run (programWithCount 65 [0, 0, 0, 0, 64, 1, 2, 7, 27, 9]) 256 act)
#guard [false, true].all (fun act =>
  Fuzz.run (programWithCount 64 [0, 0, 0, 0, 60, 0, 61, 62, 63, 27, 9]) 256 act ==
  Fuzz.run (programWithCount 65 [0, 0, 0, 0, 60, 0, 61, 62, 63, 27, 9]) 256 act)

/-! ## Regression fixtures from `src/write_zipper.rs` -/

/-- `write_zipper_prune_path_test2`, first phase: removing the value at
`[0,0,1,0,0]` and pruning removes exactly 3 bytes, back to the branch at `[0,0]`. -/
def pruneT2 : T := mk [([0], 0), ([0,0,0], 0), ([0,0,1,0,0], 0)]

#guard (((zipAt pruneT2 [] [0,0,1,0,0]).removeVal false).2.prunePath).1 == 3
#guard !(((zipAt pruneT2 [] [0,0,1,0,0]).removeVal false).2.prunePath).2.pathExists
#guard (((zipAt pruneT2 [] [0,0,1,0,0]).removeVal false).2.pathExists)
#guard ((zipAt pruneT2 [] [0,0]).childCount) == 2

/-- Same test, later phase: a chain with every value removed prunes all the way
to the zipper root (7 bytes), and the root itself survives. -/
def pruneT2b : T := ((mk [([0,0,0,1,2,3,4], 0)]).removeVal [0,0,0,1,2,3,4]).2

#guard ((zipAt pruneT2b [] [0,0,0,1,2,3,4]).prunePath).1 == 7
#guard ((zipAt pruneT2b [] [0,0,0,1,2,3,4]).prunePath).2.reset.pathExists

/-! Pruning is a no-op above the dangling tip (the location still has a child)
and below it (the location does not exist). -/

#guard ((zipAt pruneT2b [] [0,0,0,1,2,3]).prunePath).1 == 0
#guard ((zipAt pruneT2b [] [0,0,0,1,2,3,4,5]).prunePath).1 == 0

/-! The zipper root bounds pruning, even for a dangling chain continuing above it. -/

#guard ((zipAt pruneT2b [0,0] [0,1,2,3,4]).prunePath).1 == 5
#guard ((zipAt pruneT2b [0,0] [0,1,2,3,4]).prunePath).2.trie.pathExists [0,0]
#guard !((zipAt pruneT2b [0,0] [0,1,2,3,4]).prunePath).2.trie.pathExists [0,0,0]

/-! The flag is an explicit prune after the operation, including a no-op.
`false` preserves a dangling path. -/

#guard (((zipAt pruneT2 [] [0,0,1,0,0]).removeVal true).2.trie.pathExists [0,0,1]) == false
#guard (((zipAt pruneT2 [] [0,0,1,0,0]).removeVal false).2.trie.pathExists [0,0,1,0,0])
#guard !(((zipAt pruneT2b [] [0,0,0,1,2,3,4]).removeVal true).2.trie.pathExists [0,0,0,1,2,3,4])
#guard !(((zipAt pruneT2b [] []).removeBranches true).2.trie.pathExists [0])
#guard (((zipAt pruneT2b [] []).removeBranches false).2.trie.pathExists [])
#guard (((zipAt pruneT2b [] [0,0,0,1,2,3,4]).removeUnmaskedBranches
  (ByteMask.ofList []) true).trie.pathExists [0,0,0,1,2,3,4]) == false
#guard !(((zipAt pruneT2b [] [0,0,0,1,2,3,4]).takeMap true).2.trie.pathExists
  [0,0,0,1,2,3,4])
#guard !(((zipAt pruneT2b [] [0,0,0,1,2,3,4]).joinKPathInto ops 1 true).2.trie.pathExists
  [0,0,0,1,2,3,4])
#guard (((zipAt pruneT2b [0,0] [0,1,2,3,4]).removeVal true).2.trie.pathExists [0,0])
#guard !(((zipAt pruneT2b [0,0] [0,1,2,3,4]).removeVal true).2.trie.pathExists
  [0,0,0])

/-! `write_zipper_drop_head_test3`: `[[0,0],[0,1],[1,0],[1,1]]` with
`join_k_path_into(1)` collapses to 2 values. -/
def dropT3 : T := mk [([0,0], 0), ([0,1], 1), ([1,0], 2), ([1,1], 3)]

#guard (((zipAt dropT3 [] []).joinKPathInto ops 1 true).2).valCount == 2

/-- `write_zipper_drop_head_test6`: dropping 4 bytes from paths that are at most
4 long annihilates everything, because values at depth exactly `k` are lost. -/
def dropT6 : T := mk [([193,191,193,193,191], 0), ([193,191,193,194,12,28], 1),
                      ([193,191,193,194,18,9], 2), ([193,191,194,193,191], 3),
                      ([193,191,194,194,12,28], 4), ([193,191,194,194,15,47], 5),
                      ([193,191,194,194,18,9], 6)]

#guard !((zipAt dropT6 [] [193,191]).joinKPathInto ops 4 true).1
#guard (((zipAt dropT6 [] [193,191]).joinKPathInto ops 4 true).2).valCount == 0

/-- `write_zipper_drop_head_test1`: under the root `123:`, dropping 4 bytes
rewrites `abc:Bob` to `Bob` and `dog:Bob:Fido` to `Bob:Fido`. -/
def dropT1 : T := mk [
  ([0x31,0x32,0x33,0x3a,0x61,0x62,0x63,0x3a,0x42,0x6f,0x62], 0),
  ([0x31,0x32,0x33,0x3a,0x64,0x6f,0x67,0x3a,0x42,0x6f,0x62,0x3a,0x46,0x69,0x64,0x6f], 1)]

def dropT1Result : T := ((zipAt dropT1 [0x31,0x32,0x33,0x3a] []).joinKPathInto ops 4 true).2.trie

#guard dropT1Result.valAt [0x31,0x32,0x33,0x3a,0x42,0x6f,0x62] == some 0
#guard dropT1Result.valAt [0x31,0x32,0x33,0x3a,0x42,0x6f,0x62,0x3a,0x46,0x69,0x64,0x6f] == some 1
#guard dropT1Result.valCount [] == 2

/-! ## Subtrie removal -/

/-! `remove_subtrie` clears the focus and descendants, preserves other content,
and prunes only up to the zipper root. Dangling descendants count as branches;
pruning an already dangling focus does not count as removing content. -/

#guard ((zipAt fBranch [] [0]).removeSubtrie false).1
#guard ((zipAt fBranch [] [0]).removeSubtrie false).2.pathExists
#guard !((zipAt fBranch [] [0]).removeSubtrie false).2.isVal
#guard ((zipAt fBranch [] [0]).removeSubtrie false).2.childCount == 0
#guard ((zipAt fBranch [] [0]).removeSubtrie true).2.trie.valAt [] == some 0
#guard ((zipAt fBranch [] [0]).removeSubtrie true).2.trie.valAt [1] == some 4
#guard !((zipAt fBranch [] [0]).removeSubtrie true).2.pathExists
#guard ((zipAt fBranch [] []).removeSubtrie true).2.trie.isEmptyMap
#guard !(((zipAt fBranch [] []).removeSubtrie true).2.removeSubtrie true).1
#guard ((zipAt fDangle [] [0,1]).removeSubtrie false).1
#guard !((zipAt fDangle [] [0,1,2]).removeSubtrie true).1
#guard !((zipAt fDangle [] [0,1,2]).removeSubtrie true).2.pathExists
#guard !((zipAt fEmpty [] [3]).removeSubtrie true).1
#guard !((zipAt fEmpty [] [3]).removeSubtrie true).2.pathExists
#guard ((zipAt fRun [0,0] [0]).removeSubtrie true).2.trie.pathExists [0,0]
#guard !((zipAt fRun [0,0] [0]).removeSubtrie true).2.trie.pathExists [0,0,0]
#guard ((zipAt fRun [0,0] []).removeSubtrie true).2.pathExists

#guard allZips.all (fun z => [false, true].all (fun pr =>
  let (removed, after) := z.removeSubtrie pr
  let (branches, z1) := z.removeBranches pr
  let (value, composed) := z1.removeVal pr
  removed == (branches || value.isSome) &&
    after.trie.vals == composed.trie.vals && after.trie.paths == composed.trie.paths &&
    after.path == z.path && after.root == z.root &&
    !after.isVal && after.childCount == 0))

/-! ## Structural invariants over every fixture -/

#guard fixtures.all valsExist
#guard fixtures.all prefixClosed
#guard fixtures.all valCountAgrees
#guard fixtures.all (fun t => probes.all (childMaskAgrees t))

/-! ## Zipper law checks -/

#guard allZips.all removeValLeavesPath
#guard allZips.all createPathIdempotent
#guard allZips.all (createThenPrune ops)
#guard allZips.all descendIndexedLands
#guard allZips.all siblingRoundTrip
#guard allZips.all toNextValMonotone
#guard allZips.all toPrevStepMonotone
#guard allZips.all toPrevValMonotone
#guard allZips.all stepRoundTrip
#guard allZips.all valRoundTrip

/-! Reverse traversal skips missing ancestors, stops at existing parents,
wraps from the root, and stays within a zipper rooted below the map root. -/
#guard ((zipAt fSide [] [3,3,3]).toPrevStep).2.path == [2]
#guard ((zipAt fSide [] [0,0,3,3]).toPrevStep).2.path == [0,0]
#guard ((zipAt fSide [] [0,1,3]).toPrevStep).2.path == [0,0]
#guard ((zipAt fSide [] []).toPrevStep).2.path == [2]
#guard !((zipAt fSide [] [0]).toPrevStep).1
#guard !((zipAt fSide [0,0] [3,3]).toPrevStep).1
#guard ((zipAt fSide [0] []).toPrevVal).2.path == [2]
#guard ((zipAt fBranch [] [0,1]).toPrevVal).2.path == [0,0]
#guard ((zipAt fBranch [] [0,0]).toPrevVal).2.path == [0]
#guard !((zipAt fBranch [] [0]).toPrevVal).1
#guard !((zipAt (mk [([], 9)]) [] []).toPrevVal).1
#guard !((zipAt fEmpty [] []).toPrevStep).1
#guard !((zipAt fEmpty [] [3,3]).toPrevVal).1
#guard ((zipAt fDangle [] []).toPrevVal).2.path == [0]

#guard allZips.all descendLastValLands

/-! Last-value descent includes the focus and skips dangling suffixes. -/
#guard ((zipAt fDangle [] []).descendLastVal).2.path == [0]
#guard ((zipAt fDangle [] [0]).descendLastVal).1
#guard ((zipAt fDangle [] [0]).descendLastVal).2.path == [0]
#guard !((zipAt fDangle [] [0,1]).descendLastVal).1
#guard ((zipAt fDangle [] [0,1]).descendLastVal).2.path == [0,1]
#guard !((zipAt fEmpty [] []).descendLastVal).1
#guard ((zipAt (mk [([], 9)]) [] []).descendLastVal).1
#guard ((zipAt (mk [([], 9)]) [] []).descendLastVal).2.path == []
#guard ((zipAt fBranch [0] []).descendLastVal).2.path == [1]
#guard !((zipAt fSide [] [3,3]).descendLastVal).1
#guard ((zipAt fSide [] [3,3]).descendLastVal).2.path == [3,3]
#guard allZips.all (fun z => probes.all (descendToExistingLands z))
#guard allZips.all (fun z => setValThenVal ops z 42)
#guard allZips.all (fun z => probes.all (fun p => setValAtAgrees ops z p 42))
#guard allZips.all (takeThenGraft ops)
#guard allZips.all (joinEmptyIdentity ops)
#guard allZips.all (joinSelfIdentity ops)
#guard allZips.all (removeBranchesKeepsVal ops)
#guard allZips.all (removeUnmaskedFullMask ops)
#guard allZips.all (removeUnmaskedEmptyMask ops)
#guard allZips.all (fun z => [[0], [0,1], [2,2]].all (dropHeadUndoesInsertPrefix ops z))
#guard allZips.all (fun z => allZips.all (fun w => graftThenMakeMap ops z w))
#guard fixtures.all (fun s =>
  [([0], [9]), ([1], [2]), ([0, 0], [1, 1])].all (fun ab =>
    graftedCopiesIndependent ops s ab.1 ab.2 [3, 7] 999))

/-! ## Algebraic law checks -/

#guard fixtures.all (fun a => fixtures.all (joinCommOnPaths ops a))
#guard fixtures.all (joinIdem ops)
#guard fixtures.all (fun a => fixtures.all (fun b => fixtures.all (joinAssoc ops a b)))
#guard fixtures.all (meetIdemOnVals ops)
#guard fixtures.all (subSelfEmptyVals ops)
#guard fixtures.all (restrictSelf ops)

/-! ## Naive oracles

`PathMap.join` / `meet` / `sub` are defined in terms of `ValOps`, which was
transcribed from `src/ring.rs` -- so a defect in the crate's `Option<V>` lattice
impls could have been copied into the model, after which the differential would
agree and report nothing.

These oracles are written from set theory instead: they say which *keys* survive
without consulting `ValOps`, `PathMap`, or anything else the model shares with the
crate.  They are deliberately naive and quadratic.  Where they and the real
definitions agree, the shared-derivation risk is excluded for that operation.

`u64Ops.psub` annihilates exactly when the two values are equal, which is the one
fact about the value type these need. -/

/-- Keys of `a` and `b` together: what `join` must produce. -/
def joinKeysOracle (a b : T) : List Path :=
  Path.sortDedup (a.vals.map (·.1) ++ b.vals.map (·.1))

/-- Keys in both: what `meet` must produce. -/
def meetKeysOracle (a b : T) : List Path :=
  Path.sortDedup ((a.vals.map (·.1)).filter (fun k => (b.valAt k).isSome))

/-- Keys of `a` whose value `b` does not annihilate: what `sub` must produce.
For `u64`, `psubtract` annihilates exactly on equal values. -/
def subKeysOracle (a b : T) : List Path :=
  Path.sortDedup <| a.vals.filterMap fun kv =>
    match b.valAt kv.1 with
    | some bv => if bv == kv.2 then none else some kv.1
    | none => some kv.1

#guard fixtures.all (fun a => fixtures.all (fun b =>
  (PathMap.join ops a b).vals.map (·.1) == joinKeysOracle a b))
#guard fixtures.all (fun a => fixtures.all (fun b =>
  (PathMap.meet ops a b).vals.map (·.1) == meetKeysOracle a b))
#guard fixtures.all (fun a => fixtures.all (fun b =>
  (PathMap.sub ops a b).vals.map (·.1) == subKeysOracle a b))

/-- `restrict` against the `BTreeSet` oracle from
`tests/pathmap_algebra_differential.rs`: a path of `a` survives when some prefix
of it — the empty prefix and the path itself both count — carries a value in `b`. -/
def restrictOracle (a b : T) : List Path :=
  a.vals.map (·.1) |>.filter fun p =>
    (List.range (p.length + 1)).any fun i => (b.valAt (p.take i)).isSome

#guard fixtures.all (fun a => fixtures.all (fun b =>
  (Map.restrict a b).vals.map (·.1) == restrictOracle a b))

/-! The minimal shapes from `restrict_matches_btreeset_oracle`, which caught a
real `prestrict` bug: a location that both carries a value and branches. -/

#guard [ [([0,1], 0), ([0,1,2], 1)],
         [([0,1], 0), ([0,1,2], 1), ([0,1,3], 2)],
         [([0], 0), ([0,1], 1), ([0,1,2], 2)],
         [([0], 0), ([0,1,2], 1), ([0,1,3], 2)],
         [([0], 0), ([0,1], 1), ([0,1,2], 2), ([0,1,3], 3), ([9,9], 4)] ].all
  (fun es => restrictSelf ops (mk es))

/-! ## The logical hash

`Hash.hashU64` is the model of the crate's `Fnv1a64Scheme` trie hash.  These pin the definition
to the algebra the crate implements in `CatamorphismCached::hash_with_scheme`: a run steps one
byte at a time, a leaf value sits on the empty node, a value with children is layered on the
hash of the node below it, and the hash at a position sees nothing above it. -/

-- The empty trie is the empty node.
#guard Hash.hashU64 fEmpty [] == Hash.leaf

-- A dangling position hashes as the empty node, exactly like the empty trie.
#guard Hash.hashU64 (PathMap.empty.addPath [0,1]) [0,1] == Hash.leaf

-- A single run: one `step` per byte above a leaf value.
#guard Hash.hashU64 fRun [] ==
  Hash.step 0 (Hash.step 0 (Hash.step 0 (Hash.step 0 (Hash.withValue (Hash.value 7) Hash.leaf))))

-- The hash at a position is the hash of the subtrie below it, independent of what is above.
#guard Hash.hashU64 fRun [0,0] == Hash.step 0 (Hash.step 0 (Hash.withValue (Hash.value 7) Hash.leaf))

-- A value with children: layered on the node below, whose children fold in ascending order.
#guard Hash.hashU64 fBranch [0] ==
  Hash.withValue (Hash.value 1)
    (Hash.node [0, 1] [Hash.withValue (Hash.value 2) Hash.leaf, Hash.withValue (Hash.value 3) Hash.leaf])

-- The root value is layered on like any other.
#guard Hash.hashU64 fBranch [] ==
  Hash.withValue (Hash.value 0) (Hash.node [0, 1] [Hash.hashU64 fBranch [0], Hash.withValue (Hash.value 4) Hash.leaf])

-- Different values, and a value present or absent at an interior position, change the hash.
#guard Hash.hashU64 (mk [([0,0], 1)]) [] != Hash.hashU64 (mk [([0,0], 2)]) []
#guard Hash.hashU64 (mk [([0,0], 1)]) [] != Hash.hashU64 (mk [([0], 1), ([0,0], 1)]) []
#guard Hash.hashU64 (mk [([0,0], 1)]) [] != Hash.hashU64 (PathMap.empty.addPath [0,0]) []

-- The mask bitmap: byte `b` sets bit `b % 8` of byte `b / 8`.
#guard Hash.maskBytes [0, 9, 255] == [1, 2] ++ List.replicate 29 0 ++ [128]
#guard Hash.maskBytes [] == List.replicate 32 0

-- `GraftNoop.lean`, executed: grafting a hash-equal subtrie (here, the same contents built in a
-- different order, at a focus inside the trie) leaves every entry as it was.
def fBranchAgain : T := mk [([1], 4), ([0,1], 3), ([0,0], 2), ([0], 1), ([], 0)]
#guard Hash.hashU64 fBranch [0] == Hash.hashU64 fBranchAgain [0]
#guard ((zipAt fBranch [] [0]).graft (zipAt fBranchAgain [] [0])).trie.entries == fBranch.entries
#guard ((zipAt fBranch [] []).graft (zipAt fBranchAgain [] [])).trie.entries == fBranch.entries
-- and a graft that is not hash-equal does change it
#guard ((zipAt fBranch [] [0]).graft (zipAt fRun [] [])).trie.entries != fBranch.entries

-- Rendering matches `format!("{:016x}")`.
#guard Hash.hex64 0 == "0000000000000000"
#guard Hash.hex64 0xcbf29ce484222325 == "cbf29ce484222325"

end Check
end PathMapModel
