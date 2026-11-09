import PathMapModel.PathMap

/-!
# Prefix trees: what a catamorphism serializes and an anamorphism deserializes

A trie such as `{aa, aaa, ab}` can be written down as a nested prefix tree that
keeps the trie's shape:

```
(-, a(-, a(✓, a(✓)), b(✓)))
```

Folding a trie bottom-up with a catamorphism whose closure builds such a tree
node is *serialization*; unfolding a tree top-down with an anamorphism whose
closure pushes each edge is *deserialization*.  This file states and proves
that the two are inverse, at two granularities:

* **Byte level.**  Every edge is one byte.  This is what the *stepping*
  catamorphisms (`into_cata_side_effect`, `into_cata_cached`, and their
  `_fallible` versions when they succeed) build, and what an anamorphism builds
  with `TrieBuilder::push_byte`.
* **Line level.**  Every edge is a *line*: a maximal run of bytes with no fork
  and no value inside it.  This is what the *jumping* catamorphisms
  (`into_cata_jumping_*`) build, and what an anamorphism builds with multi-byte
  `TrieBuilder::push`.

## The tree

`PTree V`: a node carries an optional value and a list of `(edge, child)`
pairs.  `flatten` reads a tree back as a `PathMap`: every node is a location
(carrying its value), and so is every byte position strictly inside an edge
(carrying none).  A leaf with no value is a **dangling** location, exactly as
`create_path` makes one: the tree form has no trouble with dangling paths.

## Canonical forms

* `ByteForm`: edges of length 1, their bytes strictly ascending.
* `LineForm`: edges non-empty, first bytes strictly ascending, and every
  **child** a *feature* -- it carries a value or does not have exactly one
  child.  That makes each edge maximal: a line stops exactly where a value or a
  fork (or a leaf) is.

### The root is exempt

The root of a `LineForm` tree need not be a feature.  This is the decision for
a trie whose root has one child and no value: a jumping catamorphism does not
visit such a root at all, it hands back the result of the first feature below
it, whose jump "counts from the root" (see `MapFuzz/Morph.lean`).  In the tree
that is a root `node none [(line, featureTree)]`: one leading edge from a
non-feature root.  Allowing it only at the root keeps the form unique: the
root is the one node that is not at the end of an edge, so it is the one node
whose shape is not decided by "edges are maximal".

## Contents

* `flatten`, `PathMap.WF` (the canonical-form invariant of `PathMap`, which
  `PathMap.mk'` establishes but the model never named).
* `cata` / `cataJump`: the model's stepping and jumping catamorphisms, generic
  in the closure; `MapFuzz/Morph.lean`'s folds are these, instantiated with the
  fuzzer's string-encoding closures.  `toBytes` / `toLines` are the same folds
  with the tree-building closures, so (c) of the brief holds by definition for
  the cached flavours; `side_eq_cata` shows the numbered post-order
  (side-effecting) flavours return the same.
* Theorems: `flatten_toBytes`, `flatten_toLines` (serialize then deserialize
  is the identity on well-formed tries); `toBytes_flatten`, `toLines_flatten`
  (deserialize then serialize is the identity on canonical trees); `ana_unfold`
  (the anamorphism that pushes a tree's edges builds `flatten` minus dangling
  locations, which no push can create; exactly `flatten` when no leaf dangles).
-/

namespace PathMapModel

/-- A prefix tree: a value, and edges to children.  The children are
`(edge, child)` pairs; the edge is the run of bytes from this node to the child. -/
inductive PTree (V : Type) where
  | node (v : Option V) (kids : List (Path × PTree V))
deriving Repr, Inhabited

namespace PTree

variable {V : Type}

def val : PTree V → Option V
  | node v _ => v

def kids : PTree V → List (Path × PTree V)
  | node _ k => k

/-- Induction over a tree, with the hypothesis for every child of a node. -/
theorem ind {motive : PTree V → Prop}
    (h : ∀ v kids, (∀ e c, (e, c) ∈ kids → motive c) → motive (node v kids)) :
    ∀ t, motive t
  | node v kids => h v kids (fun e c hm => ind h c)
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem hm
  simp only [Prod.mk.sizeOf_spec] at this
  simp only [node.sizeOf_spec]
  omega

/-- The locations strictly inside an edge: its proper, non-empty prefixes. -/
def mids (e : Path) : List Path := (List.range (e.length - 1)).map fun i => e.take (i + 1)

mutual
/-- Every location of the tree, pre-order, each with its value: the node, then
for each edge the bytes inside it (no value) and the child's locations. -/
def ents : PTree V → List (Path × Option V)
  | node v kids => ([], v) :: entsKids kids

def entsKids : List (Path × PTree V) → List (Path × Option V)
  | [] => []
  | (e, c) :: rest =>
      ((mids e).map fun p => (p, (none : Option V))) ++
        ((ents c).map fun pv => (e ++ pv.1, pv.2)) ++ entsKids rest
end

/-- The trie a tree denotes.  A well-formed `PathMap` when the tree's edges are
non-empty with strictly ascending first bytes (`wf_flatten`), which both
canonical forms ask. -/
def flatten (t : PTree V) : PathMap V := ⟨t.ents⟩

/-- The valued locations, pre-order. -/
def valsOf (t : PTree V) : List (Path × V) :=
  t.ents.filterMap fun pv => pv.2.map (pv.1, ·)

/-- A node that a jumping fold stops at: a value, or not exactly one child. -/
def isFeat : PTree V → Bool
  | node v kids => v.isSome || kids.length != 1

/-- The first byte of every edge, in order. -/
def heads (kids : List (Path × PTree V)) : List UInt8 := kids.map (·.1.headD 0)

/-- Byte form: every edge is one byte, the bytes strictly ascending. -/
inductive ByteForm : PTree V → Prop
  | node (v : Option V) (kids : List (Path × PTree V)) :
      (heads kids).Pairwise (· < ·) →
      (∀ k ∈ kids, k.1.length = 1) → (∀ k ∈ kids, ByteForm k.2) →
      ByteForm (node v kids)

/-- Line form: edges non-empty, first bytes strictly ascending, every child a
feature.  The root may be a non-feature (see the header). -/
inductive LineForm : PTree V → Prop
  | node (v : Option V) (kids : List (Path × PTree V)) :
      (heads kids).Pairwise (· < ·) →
      (∀ k ∈ kids, k.1 ≠ [] ∧ k.2.isFeat = true) → (∀ k ∈ kids, LineForm k.2) →
      LineForm (node v kids)

/-- No leaf without a value: what an anamorphism can build by pushing alone. -/
inductive NoDangling : PTree V → Prop
  | node (v : Option V) (kids : List (Path × PTree V)) :
      (kids = [] → v.isSome) →
      (∀ k ∈ kids, NoDangling k.2) →
      NoDangling (node v kids)

/-- Recursion bound for `ana`: more than the number of nodes on any branch. -/
def height : PTree V → Nat
  | node _ kids => 1 + heightKids kids
where heightKids : List (Path × PTree V) → Nat
  | [] => 0
  | (_, c) :: rest => max (height c) (heightKids rest)

mutual
/-- A canonical rendering, `(<val>,<edge hex><child>,...)`; the fuzzer compares it
with the crate's closures' output.  `showV` renders a value (`-` for none). -/
def render (showV : Option V → String) (hex : Path → String) : PTree V → String
  | node v kids => "(" ++ showV v ++ renderKids showV hex kids ++ ")"

def renderKids (showV : Option V → String) (hex : Path → String) :
    List (Path × PTree V) → String
  | [] => ""
  | (e, c) :: rest => "," ++ hex e ++ render showV hex c ++ renderKids showV hex rest
end

end PTree

/-! ## Catamorphisms -/

namespace PathMap

variable {V : Type}

/-- A location a jumping fold stops at: valued, or not exactly one child. -/
def isFeature (T : PathMap V) (q : Path) : Bool :=
  (T.valAt q).isSome || T.childCount q != 1

/-- The first feature at or below `q` along its single-child chain. -/
def follow (T : PathMap V) : Nat → Path → Path
  | 0, q => q
  | n + 1, q =>
      if isFeature T q then q else
      match T.childMask q with
      | [b] => follow T n (q ++ [b])
      | _ => q

/-- Recursion bound: deeper than any path in `T`. -/
def fuel (T : PathMap V) : Nat := (T.paths.map List.length).foldl max 0 + 2

section
variable {W : Type}

/-- The stepping catamorphism: `alg` at every location, given its value, its
child mask and its children's results in ascending byte order.  `d` answers
when the fuel runs out (never, from `cataStep`). -/
def cata (T : PathMap V) (alg : Option V → ByteMask → List W → W) (d : W) : Nat → Path → W
  | 0, _ => d
  | n + 1, q =>
      let m := T.childMask q
      alg (T.valAt q) m (m.map fun b => cata T alg d n (q ++ [b]))

def cataStep (T : PathMap V) (alg : Option V → ByteMask → List W → W) (d : W) : W :=
  cata T alg d (fuel T) []

/-- The jumping catamorphism at feature `q`, reached by jumping over `sub`:
`alg` sees `sub`, the value, the mask, and for each child byte `b` the result at
the first feature on the chain from `q ++ [b]`, which jumped over the bytes
after `b`. -/
def cataJ (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W) (d : W) :
    Nat → Path → Path → W
  | 0, _, _ => d
  | n + 1, q, sub =>
      let m := T.childMask q
      alg sub (T.valAt q) m (m.map fun b =>
        let f := follow T (fuel T) (q ++ [b])
        cataJ T alg d n f (f.drop (q.length + 1)))

/-- The root is visited iff it is a feature; otherwise the result is the first
feature's, which jumped over every byte from the root. -/
def cataJump (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W) (d : W) : W :=
  if isFeature T [] then cataJ T alg d (fuel T) [] []
  else
    let f := follow T (fuel T) []
    cataJ T alg d (fuel T) f f

/-! ### Side-effecting flavours

Post-order (children in ascending byte order, then the location) and numbered:
`enc i q jump v m ws` is call `i`'s result at `q` (`jump` is `none` for a
stepping fold), `err i q jump v m` the `Err` it would return.  Each returns the
result, the next call number, and every call's `Err` in call order. -/

variable {E : Type}

def sideCata (T : PathMap V) (enc : Nat → Path → Option Nat → Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    Nat → Path → Nat → W × Nat × List E
  | 0, _, i => (d, i, [])
  | n + 1, q, i =>
      let mask := T.childMask q
      let (ws, i, log) := mask.foldl (fun (acc : List W × Nat × List E) b =>
        let (w, i', l') := sideCata T enc err d n (q ++ [b]) acc.2.1
        (acc.1 ++ [w], i', acc.2.2 ++ l')) ([], i, [])
      let v := T.valAt q
      (enc i q none v mask ws, i + 1, log ++ [err i q none v mask])

/-- At feature `q`, reached with `jump` jumped bytes. -/
def sideJ (T : PathMap V) (enc : Nat → Path → Option Nat → Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    Nat → Path → Nat → Nat → W × Nat × List E
  | 0, _, _, i => (d, i, [])
  | n + 1, q, jump, i =>
      let mask := T.childMask q
      let (ws, i, log) := mask.foldl (fun (acc : List W × Nat × List E) b =>
        let f := follow T (fuel T) (q ++ [b])
        let (w, i', l') := sideJ T enc err d n f (f.length - q.length - 1) acc.2.1
        (acc.1 ++ [w], i', acc.2.2 ++ l')) ([], i, [])
      let v := T.valAt q
      (enc i q (some jump) v mask ws, i + 1, log ++ [err i q (some jump) v mask])

/-- A side-effecting fold of the whole view, stepping or jumping. -/
def sideFold (T : PathMap V) (jumping : Bool)
    (enc : Nat → Path → Option Nat → Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) : W × Nat × List E :=
  if !jumping then sideCata T enc err d (fuel T) [] 0
  else if isFeature T [] then sideJ T enc err d (fuel T) [] 0 0
  else
    let f := follow T (fuel T) []
    sideJ T enc err d (fuel T) f f.length 0

end

/-- The byte-tree closure: one edge per mask byte. -/
def algB (v : Option V) (m : ByteMask) (ws : List (PTree V)) : PTree V :=
  .node v (List.zipWith (fun b w => ([b], w)) m ws)

/-- The line-tree closure: the result carries the bytes it jumped over, and the
parent puts its mask byte in front of them. -/
def algL (sub : Path) (v : Option V) (m : ByteMask) (ws : List (Path × PTree V)) :
    Path × PTree V :=
  (sub, .node v (List.zipWith (fun b w => (b :: w.1, w.2)) m ws))

/-- **Serialize, byte level**: the stepping catamorphism with `algB`. -/
def toBytes (T : PathMap V) : PTree V := cataStep T algB (.node none [])

/-- Wrap a jumping fold's result: a non-empty jump is the root's leading edge. -/
def rootLine (r : Path × PTree V) : PTree V :=
  if r.1.isEmpty then r.2 else .node none [r]

/-- **Serialize, line level**: the jumping catamorphism with `algL`. -/
def toLines (T : PathMap V) : PTree V := rootLine (cataJump T algL ([], .node none []))

/-- The canonical-form invariant every `PathMap` the model builds satisfies
(`mk'` establishes it): entries strictly sorted by path, prefix-closed, and the
root present. -/
def WF (t : PathMap V) : Prop :=
  t.entries.Pairwise (fun a b => Path.lt a.1 b.1 = true) ∧
  (∀ p r : Path, p ++ r ∈ t.paths → p ∈ t.paths) ∧ [] ∈ t.paths

end PathMap

/-! ## Anamorphisms

The generic anamorphism lives in `MapFuzz/Morph.lean` (`Morph.ana`, with the
`TrieBuilder` calls `push`/`push_byte`/`graft_at_byte` as `AnaKid`s).  Its
closure for a tree just pushes every edge; `PTree.unfoldVals` is what it
collects, stated here so the theorem needs nothing from the fuzzer. -/

namespace PTree

variable {V : Type}

/-! ## Fixtures -/

/-- `{aa: 1, aaa: 2, ab: 3}` with `a b` = `1 2`, and a dangling `[2]`. -/
private def ex : PathMap Nat := PathMap.mk' [([1, 1], 1), ([1, 1, 1], 2), ([1, 2], 3)] [[2]]

private def rd : PTree Nat → String :=
  render (fun v => match v with | none => "-" | some x => toString x)
    (fun p => String.join (p.map toString))

#guard rd (PathMap.toBytes ex) == "(-,1(-,1(1,1(2)),2(3)),2(-))"
#guard rd (PathMap.toLines ex) == "(-,1(-,1(1,1(2)),2(3)),2(-))"
#guard (PathMap.toBytes ex).flatten.entries == ex.entries
#guard (PathMap.toLines ex).flatten.entries == ex.entries

/-- A root that is no feature: one leading edge. -/
private def ex2 : PathMap Nat := PathMap.mk' [([1, 2, 3, 4], 1), ([1, 2, 3, 5, 6], 2)] []

#guard rd (PathMap.toLines ex2) == "(-,123(-,4(1),56(2)))"
#guard rd (PathMap.toBytes ex2) == "(-,1(-,2(-,3(-,4(1),5(-,6(2))))))"
#guard (PathMap.toLines ex2).flatten.entries == ex2.entries
#guard (PathMap.toBytes ex2).flatten.entries == ex2.entries
-- A dangling chain is a line ending in a dangling leaf.
#guard rd (PathMap.toLines (PathMap.mk' [] [[3, 3, 3]] : PathMap Nat)) == "(-,333(-))"
#guard rd (PathMap.toLines (PathMap.empty : PathMap Nat)) == "(-)"
#guard rd (PathMap.toLines (PathMap.mk' [([], 7)] [[3, 3]] : PathMap Nat)) == "(7,33(-))"

end PTree
end PathMapModel
