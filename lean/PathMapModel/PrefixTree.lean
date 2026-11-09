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
  | node v kids => h v kids (fun e c _hm => ind h c)
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem _hm
  simp only [Prod.mk.sizeOf_spec] at this
  simp only [node.sizeOf_spec]
  omega

/-- Put byte `b` in front of an entry's path. -/
def pre (b : UInt8) (pv : Path × Option V) : Path × Option V := (b :: pv.1, pv.2)

/-- The locations an edge contributes, below its parent: one valueless location
for every byte strictly inside the edge, then the child's own locations `L`
under the whole edge. -/
def blockEnts : Path → List (Path × Option V) → List (Path × Option V)
  | [], L => L
  | [b], L => L.map (pre b)
  | b :: c :: x, L => ([b], none) :: (blockEnts (c :: x) L).map (pre b)

mutual
/-- Every location of the tree, pre-order, each with its value: the node, then
for each edge the bytes inside it (no value) and the child's locations. -/
def ents : PTree V → List (Path × Option V)
  | node v kids => ([], v) :: entsKids kids

def entsKids : List (Path × PTree V) → List (Path × Option V)
  | [] => []
  | (e, c) :: rest => blockEnts e (ents c) ++ entsKids rest
end

/-- The trie a tree denotes.  A well-formed `PathMap` when the tree's edges are
non-empty with strictly ascending first bytes (`wf_flatten`), which both
canonical forms ask. -/
def flatten (t : PTree V) : PathMap V := ⟨t.ents⟩

/-- An entry's value, with its path. -/
def valued (pv : Path × Option V) : Option (Path × V) := pv.2.map (pv.1, ·)

/-- The valued locations, pre-order. -/
def valsOf (t : PTree V) : List (Path × V) := t.ents.filterMap valued

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

/-- What both canonical forms ask of every node: non-empty edges with strictly
ascending first bytes.  Enough for `flatten` to be sorted (`sorted_ents`). -/
inductive Ordered : PTree V → Prop
  | node (v : Option V) (kids : List (Path × PTree V)) :
      (heads kids).Pairwise (· < ·) →
      (∀ k ∈ kids, k.1 ≠ []) → (∀ k ∈ kids, Ordered k.2) →
      Ordered (node v kids)

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

`PathMap::new_from_ana(w, alg)` runs `alg(w, &mut val, builder, path)` at the
root, then, depth-first in push order, at `path ++ sub` for every child
`(sub, w')` pushed into the builder (`push_byte`, `push`, `set_child_mask`).
`graft_at_byte(b, rz)` instead places the subtrie strictly *below* `rz`'s focus
at `path ++ [b]` and does not recurse.  The result holds exactly the values
set, the grafted content (dangling paths included), and their prefixes: a
location that got neither a value nor anything below it does not exist.  (The
fuzzer's closures are in `MapFuzz/Morph.lean`.) -/

/-- What the closure put in the `TrieBuilder`. -/
inductive AnaKid (V W : Type) where
  /-- `push(sub, w)` / `push_byte` / `set_child_mask`: recurse at `path ++ sub`. -/
  | w (sub : Path) (w : W)
  /-- `graft_at_byte(b, rz)`: `node` is the subtrie at `rz`'s focus; only what is
  strictly below its root is placed, at `path ++ [b]`. -/
  | graft (b : UInt8) (node : PathMap V)

/-- The first byte of the branch a kid starts (its `TrieBuilder` child-mask bit). -/
def AnaKid.byte {V W : Type} : AnaKid V W → UInt8
  | .w sub _ => sub.headD 0
  | .graft b _ => b

/-- Values, grafted locations and calls (pre-order) of an anamorphism.  A call
is its path and the first bytes of what it pushed: after the closure,
`TrieBuilder::len` is their number and `child_mask` their set. -/
def anaGo {V W : Type} (alg : W → Path → Option V × List (AnaKid V W)) :
    Nat → W → Path → List (Path × V) × List Path × List (Path × List UInt8)
  | 0, _, _ => ([], [], [])
  | n + 1, w, path =>
      let (v, kids) := alg w path
      let vals0 : List (Path × V) := match v with | some x => [(path, x)] | none => []
      kids.foldl (fun (acc : List (Path × V) × List Path × List (Path × List UInt8)) k =>
        match k with
        | .w sub w' =>
            let (vs, ps, cs) := anaGo alg n w' (path ++ sub)
            (acc.1 ++ vs, acc.2.1 ++ ps, acc.2.2 ++ cs)
        | .graft b node =>
            (acc.1 ++ node.vals.filterMap (fun (q, x) =>
                if q.isEmpty then none else some (path ++ [b] ++ q, x)),
             acc.2.1 ++ node.paths.filterMap (fun q =>
                if q.isEmpty then none else some (path ++ [b] ++ q)),
             acc.2.2)) (vals0, [], [(path, kids.map AnaKid.byte)])

/-- `PathMap::new_from_ana(w, alg)`: the map and the calls of `alg` (see `anaGo`). -/
def ana {V W : Type} (alg : W → Path → Option V × List (AnaKid V W)) (w : W) (fuel : Nat) :
    PathMap V × List (Path × List UInt8) :=
  let (vs, ps, cs) := anaGo alg fuel w []
  (PathMap.mk' vs ps, cs)

/-- The closure that deserializes a tree: set the node's value, push every edge. -/
def PTree.unfold {V : Type} (t : PTree V) (_path : Path) : Option V × List (AnaKid V (PTree V)) :=
  (t.val, t.kids.map fun k => .w k.1 k.2)

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

/-! # Proofs

Everything is stated through lookups: a `PathMap` is determined by
`entries.lookup` once its entries are sorted (`eq_of_sorted_of_lookup`), and
`ents` of a tree is looked up edge by edge (`lookup_entsKids`, `edgeLook`). -/

namespace PathMapModel

/-! ## Paths, masks, and what a  answers -/

theorem Path.stripPrefix_eq_some : ∀ (p q s : Path), Path.stripPrefix p q = some s ↔ q = p ++ s
  | [], q, s => by simp [Path.stripPrefix]
  | a :: as, [], s => by simp [Path.stripPrefix]
  | a :: as, b :: bs, s => by
      by_cases h : a = b
      · subst h; simp [Path.stripPrefix, Path.stripPrefix_eq_some as bs s]
      · simp [Path.stripPrefix, h, Ne.symm h]

theorem ByteMask.mem_ofList (bs : List UInt8) (b : UInt8) : b ∈ ByteMask.ofList bs ↔ b ∈ bs := by
  unfold ByteMask.ofList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    simp only at hi
    split at hi
    · rename_i hc; cases hi; simpa using hc
    · cases hi
  · intro hb
    refine ⟨b.toNat, List.mem_range.mpr (by have := UInt8.toNat_lt b; omega), ?_⟩
    simp [UInt8.ofNat_toNat, hb]

theorem ByteMask.sorted_ofList (bs : List UInt8) : (ByteMask.ofList bs).Pairwise (· < ·) := by
  unfold ByteMask.ofList
  rw [List.pairwise_filterMap]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro i j hi hj hij x hx y hy
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  simp only at hx hy
  split at hx <;> split at hy <;> cases hx <;> cases hy
  rw [UInt8.lt_iff_toNat_lt]
  simp
  omega

/-- Two strictly ascending byte lists with the same members are equal. -/
theorem eq_of_sorted_of_mem :
    ∀ {l₁ l₂ : List UInt8}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ b, b ∈ l₁ ↔ b ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | b :: _, [], _, _, h => absurd ((h b).mp (List.mem_cons_self ..)) (by simp)
  | a :: as, b :: bs, h₁, h₂, h => by
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        rcases (h a).mp (List.mem_cons_self ..) with _ | ⟨_, ha⟩
        · rfl
        · rcases (h b).mpr (List.mem_cons_self ..) with _ | ⟨_, hb⟩
          · rfl
          · have := h₂.1 a ha; have := h₁.1 b hb
            rw [UInt8.lt_iff_toNat_lt] at *; omega
      subst hab
      congr 1
      refine eq_of_sorted_of_mem h₁.2 h₂.2 (fun x => ?_)
      constructor
      · intro hx
        rcases (h x).mp (List.mem_cons_of_mem _ hx) with _ | ⟨_, hx'⟩
        · exact absurd (h₁.1 a hx) (by rw [UInt8.lt_iff_toNat_lt]; omega)
        · exact hx'
      · intro hx
        rcases (h x).mpr (List.mem_cons_of_mem _ hx) with _ | ⟨_, hx'⟩
        · exact absurd (h₂.1 a hx) (by rw [UInt8.lt_iff_toNat_lt]; omega)
        · exact hx'

namespace PathMap
variable {V : Type}

theorem mem_paths (T : PathMap V) (p : Path) : p ∈ T.paths ↔ (T.entries.lookup p).isSome := by
  rw [List.lookup_isSome_iff, paths, List.mem_map]
  constructor
  · rintro ⟨kv, hm, rfl⟩; exact ⟨kv, hm, by simp⟩
  · rintro ⟨kv, hm, h⟩; exact ⟨kv, hm, (eq_of_beq h).symm⟩

theorem valAt_eq (T : PathMap V) (p : Path) : T.valAt p = (T.entries.lookup p).bind id := by
  simp only [valAt, entryAt]
  cases T.entries.lookup p with
  | none => rfl
  | some o => cases o <;> rfl

theorem mem_childMask (T : PathMap V) (q : Path) (b : UInt8) :
    b ∈ T.childMask q ↔ (T.entries.lookup (q ++ [b])).isSome := by
  rw [childMask, ByteMask.mem_ofList, List.mem_filterMap, ← mem_paths]
  constructor
  · rintro ⟨r, hr, hs⟩
    split at hs
    · rename_i s h
      have := (Path.stripPrefix_eq_some q r [s]).mp h
      cases hs; subst this; exact hr
    · cases hs
  · intro h
    refine ⟨q ++ [b], h, ?_⟩
    rw [(Path.stripPrefix_eq_some q (q ++ [b]) [b]).mpr rfl]

theorem sorted_childMask (T : PathMap V) (q : Path) : (T.childMask q).Pairwise (· < ·) :=
  ByteMask.sorted_ofList _

/-- An existing location's entry is its value. -/
theorem lookup_eq_valAt {T : PathMap V} {p : Path} (h : (T.entries.lookup p).isSome) :
    T.entries.lookup p = some (T.valAt p) := by
  rw [valAt_eq]; cases hl : T.entries.lookup p with
  | none => simp [hl] at h
  | some o => rfl

theorem WF.prefix {T : PathMap V} (hT : T.WF) {p : Path} (r : Path)
    (h : (T.entries.lookup (p ++ r)).isSome) : (T.entries.lookup p).isSome := by
  rw [← mem_paths] at h ⊢; exact hT.2.1 p r h

theorem WF.root {T : PathMap V} (hT : T.WF) : (T.entries.lookup []).isSome := by
  rw [← mem_paths]; exact hT.2.2

end PathMap

/-! ## Looking up a tree -/

namespace PTree
variable {V : Type}

/-! ### Lookups -/

theorem lookup_nil_key (L : List (Path × Option V)) (b : UInt8) :
    (L.map (pre b)).lookup [] = none := by
  induction L with
  | nil => rfl
  | cons hd tl ih => simp [pre, List.lookup_cons, ih]

theorem lookup_map_pre (L : List (Path × Option V)) (b b' : UInt8) (p : Path) :
    (L.map (pre b)).lookup (b' :: p) = if b' = b then L.lookup p else none := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [List.map_cons, pre, List.lookup_cons] at ih ⊢
    by_cases hb : b' = b
    · subst hb
      by_cases hpk : p = k
      · subst hpk; simp
      · have h1 : (b' :: p == b' :: k) = false := by simp [hpk]
        have h2 : (p == k) = false := by simp [hpk]
        simp only [h1, h2, ite_true] at ih ⊢
        exact ih
    · have : (b' :: p == b :: k) = false := by simp [hb]
      simp [this, ih, hb]

/-- Looking up a path through the rest `x` of an edge, given `g`, the lookup
below the edge's end.  `[]` is the location the rest starts at. -/
def edgeLook (g : Path → Option (Option V)) : Path → Path → Option (Option V)
  | [], p => g p
  | _ :: _, [] => some none
  | c :: x, c' :: p => if c' = c then edgeLook g x p else none

theorem lookup_blockEnts (L : List (Path × Option V)) (b : UInt8) :
    ∀ (x : Path) (b' : UInt8) (p : Path),
      (blockEnts (b :: x) L).lookup (b' :: p) = if b' = b then edgeLook (fun q => L.lookup q) x p else none
  | [], b', p => by simp [blockEnts, lookup_map_pre, edgeLook]
  | c :: x, b', p => by
      rw [blockEnts, List.lookup_cons]
      by_cases hb : b' = b
      · subst hb
        cases p with
        | nil => simp [edgeLook]
        | cons c' p =>
          have : (b' :: c' :: p == [b']) = false := by simp
          simp only [this, lookup_map_pre, lookup_blockEnts L c x c' p, edgeLook]
      · have : (b' :: p == [b]) = false := by simp [hb]
        simp [this, lookup_map_pre, hb]

theorem edgeLook_append (g : Path → Option (Option V)) :
    ∀ (x r : Path), edgeLook g x (x ++ r) = g r
  | [], r => rfl
  | c :: x, r => by simp [edgeLook, edgeLook_append g x r]

/-- `edgeLook` asks `g` only about suffixes no longer than the path. -/
theorem edgeLook_congr {g g' : Path → Option (Option V)} :
    ∀ (x p : Path), (∀ s : Path, s.length ≤ p.length → g s = g' s) →
      edgeLook g x p = edgeLook g' x p
  | [], p, h => h p (Nat.le_refl _)
  | _ :: _, [], _ => rfl
  | c :: x, c' :: p, h => by
      simp only [edgeLook]
      rw [edgeLook_congr x p (fun s hs => h s (by simp; omega))]

theorem edgeLook_nil_isSome (g : Path → Option (Option V)) (hg : (g []).isSome) :
    ∀ x : Path, (edgeLook g x []).isSome
  | [] => hg
  | _ :: _ => rfl


theorem lookup_ents_nil (v : Option V) (kids : List (Path × PTree V)) :
    (ents (node v kids)).lookup [] = some v := by
  simp [ents]

theorem lookup_ents_cons (v : Option V) (kids : List (Path × PTree V)) (b : UInt8) (p : Path) :
    (ents (node v kids)).lookup (b :: p) = (entsKids kids).lookup (b :: p) := by
  simp [ents, List.lookup_cons]

/-- The child whose edge starts with `b`. -/
def kidAt (kids : List (Path × PTree V)) (b : UInt8) : Option (Path × PTree V) :=
  kids.find? (fun k => k.1.headD 0 == b)

theorem kidAt_eq_none {kids : List (Path × PTree V)} {b : UInt8} (h : b ∉ heads kids) :
    kidAt kids b = none := by
  unfold kidAt
  rw [List.find?_eq_none]
  intro k hk hb
  exact h (List.mem_map.mpr ⟨k, hk, by simpa using hb⟩)

/-- Looking up below a node: through the edge that starts with the first byte. -/
theorem lookup_entsKids :
    ∀ (kids : List (Path × PTree V)), (∀ k ∈ kids, k.1 ≠ []) → (heads kids).Nodup →
      ∀ (b : UInt8) (p : Path),
        (entsKids kids).lookup (b :: p) =
          (kidAt kids b).bind (fun k => edgeLook (fun q => (ents k.2).lookup q) k.1.tail p)
  | [], _, _, b, p => by simp [entsKids, kidAt]
  | (e, c) :: rest, hne, hnd, b, p => by
      obtain ⟨b0, x, rfl⟩ : ∃ b0 x, e = b0 :: x := by
        cases e with
        | nil => exact absurd rfl (hne _ (List.mem_cons_self ..))
        | cons b0 x => exact ⟨b0, x, rfl⟩
      have hnd' : b0 ∉ heads rest ∧ (heads rest).Nodup := by
        simpa [heads] using hnd
      rw [entsKids, List.lookup_append, lookup_blockEnts,
        lookup_entsKids rest (fun k hk => hne k (List.mem_cons_of_mem _ hk)) hnd'.2]
      by_cases hb : b = b0
      · subst hb
        rw [kidAt_eq_none hnd'.1]
        simp [kidAt]
      · have : (b0 == b) = false := by simp [Ne.symm hb]
        simp [hb, kidAt, this]

end PTree
/-! ## Sortedness, and extensionality -/

theorem Path.lt_cons_same (b : UInt8) (x y : Path) : Path.lt (b :: x) (b :: y) = Path.lt x y := by
  rw [Path.lt_cons]; have : ¬ (b < b) := by rw [UInt8.lt_iff_toNat_lt]; omega
  simp [this]

theorem Path.lt_of_head_lt {a b : UInt8} (h : a < b) (x y : Path) : Path.lt (a :: x) (b :: y) = true := by
  rw [Path.lt_cons]; simp [h]

namespace PTree
variable {V : Type}

/-- Sorted strictly by path. -/
def Sorted (l : List (Path × Option V)) : Prop := l.Pairwise (fun a b => Path.lt a.1 b.1 = true)

theorem mem_blockEnts (L : List (Path × Option V)) (b : UInt8) :
    ∀ (x : Path), ∀ kv ∈ blockEnts (b :: x) L, ∃ r, kv.1 = b :: r
  | [], kv, h => by
      simp only [blockEnts, List.mem_map] at h
      obtain ⟨u, _, rfl⟩ := h; exact ⟨u.1, rfl⟩
  | c :: x, kv, h => by
      simp only [blockEnts, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨u, _, rfl⟩
      · exact ⟨[], rfl⟩
      · exact ⟨u.1, rfl⟩

theorem sorted_map_pre {L : List (Path × Option V)} (h : Sorted L) (b : UInt8) :
    Sorted (L.map (pre b)) := by
  unfold Sorted at *
  rw [List.pairwise_map]
  exact h.imp (fun hab => by simp only [pre, Path.lt_cons_same]; exact hab)

theorem sorted_blockEnts {L : List (Path × Option V)} (h : Sorted L) (b : UInt8) :
    ∀ x : Path, Sorted (blockEnts (b :: x) L)
  | [] => sorted_map_pre h b
  | c :: x => by
      rw [blockEnts]
      unfold Sorted
      rw [List.pairwise_cons]
      refine ⟨?_, sorted_map_pre (sorted_blockEnts h c x) b⟩
      intro kv hkv
      simp only [List.mem_map] at hkv
      obtain ⟨u, hu, rfl⟩ := hkv
      obtain ⟨r, hr⟩ := mem_blockEnts L c x u hu
      simp only [pre, hr, Path.lt_cons_same]; rfl

theorem mem_entsKids :
    ∀ (kids : List (Path × PTree V)), (∀ k ∈ kids, k.1 ≠ []) →
      ∀ kv ∈ entsKids kids, ∃ k ∈ kids, ∃ r, kv.1 = k.1.headD 0 :: r
  | [], _, kv, h => by simp [entsKids] at h
  | (e, c) :: rest, hne, kv, h => by
      rw [entsKids, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨b, x, rfl⟩ : ∃ b x, e = b :: x := by
          cases e with
          | nil => exact absurd rfl (hne _ (List.mem_cons_self ..))
          | cons b x => exact ⟨b, x, rfl⟩
        obtain ⟨r, hr⟩ := mem_blockEnts _ b x kv h
        exact ⟨(b :: x, c), List.mem_cons_self .., r, hr⟩
      · obtain ⟨k, hk, r, hr⟩ := mem_entsKids rest (fun k hk => hne k (List.mem_cons_of_mem _ hk)) kv h
        exact ⟨k, List.mem_cons_of_mem _ hk, r, hr⟩

theorem sorted_entsKids :
    ∀ (kids : List (Path × PTree V)), (heads kids).Pairwise (· < ·) → (∀ k ∈ kids, k.1 ≠ []) →
      (∀ k ∈ kids, Sorted (ents k.2)) → Sorted (entsKids kids)
  | [], _, _, _ => List.Pairwise.nil
  | (e, c) :: rest, hp, hne, hs => by
      obtain ⟨b, x, rfl⟩ : ∃ b x, e = b :: x := by
        cases e with
        | nil => exact absurd rfl (hne _ (List.mem_cons_self ..))
        | cons b x => exact ⟨b, x, rfl⟩
      simp only [heads, List.map_cons, List.pairwise_cons] at hp
      rw [entsKids]
      unfold Sorted
      rw [List.pairwise_append]
      refine ⟨sorted_blockEnts (hs _ (List.mem_cons_self ..)) b x,
        sorted_entsKids rest hp.2 (fun k hk => hne k (List.mem_cons_of_mem _ hk))
          (fun k hk => hs k (List.mem_cons_of_mem _ hk)), ?_⟩
      intro u hu w hw
      obtain ⟨r, hr⟩ := mem_blockEnts _ b x u hu
      obtain ⟨k, hk, r', hr'⟩ :=
        mem_entsKids rest (fun k hk => hne k (List.mem_cons_of_mem _ hk)) w hw
      rw [hr, hr']
      exact Path.lt_of_head_lt (hp.1 _ (List.mem_map.mpr ⟨k, hk, rfl⟩)) r r'

theorem sorted_ents : ∀ t : PTree V, Ordered t → Sorted (ents t) := by
  refine PTree.ind (fun v kids ih ho => ?_)
  cases ho with
  | node _ _ hp hne hk =>
    rw [ents]
    unfold Sorted
    rw [List.pairwise_cons]
    refine ⟨fun kv hkv => ?_, sorted_entsKids kids hp hne (fun k hk' => ih k.1 k.2 hk' (hk k hk'))⟩
    obtain ⟨_, _, r, hr⟩ := mem_entsKids kids hne kv hkv
    rw [hr]; rfl

end PTree
namespace PTree
variable {V : Type}

theorem lookup_eq_none_of_all_lt {l : List (Path × Option V)} {k : Path}
    (h : ∀ kv ∈ l, Path.lt k kv.1 = true) : l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons kv l ih =>
    obtain ⟨k', x⟩ := kv
    have h1 := h _ (List.mem_cons_self ..)
    have : (k == k') = false := by
      cases hk : k == k'
      · rfl
      · have : k = k' := eq_of_beq hk
        subst this; simp at h1
    rw [List.lookup_cons, this]
    exact ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv))

/-- **A sorted entry list is determined by its lookups.** (`Canon.lean`'s
`eq_of_sortedKeys_of_lookup`, for `Pairwise`.) -/
theorem eq_of_sorted_of_lookup :
    ∀ {l₁ l₂ : List (Path × Option V)}, Sorted l₁ → Sorted l₂ →
      (∀ k, l₁.lookup k = l₂.lookup k) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], (k, _) :: _, _, _, h => by have := h k; simp at this
  | (k, _) :: _, [], _, _, h => by have := h k; simp at this
  | (k₁, v₁) :: r₁, (k₂, v₂) :: r₂, h₁, h₂, h => by
      unfold Sorted at h₁ h₂
      rw [List.pairwise_cons] at h₁ h₂
      have below : ∀ {k k' : Path} {r : List (Path × Option V)},
          (∀ kv ∈ r, Path.lt k' kv.1 = true) → Path.lt k k' = true → ∀ kv ∈ r, Path.lt k kv.1 = true :=
        fun hr hlt kv hkv => Path.lt_trans hlt (hr kv hkv)
      have hkey : k₁ = k₂ := by
        rcases Path.lt_total k₁ k₂ with hlt | heq | hgt
        · have := h k₁
          rw [List.lookup_cons, List.lookup_cons] at this
          simp only [beq_self_eq_true] at this
          have hne : (k₁ == k₂) = false := by
            cases hb : k₁ == k₂
            · rfl
            · have := eq_of_beq hb; subst this; simp at hlt
          rw [hne, lookup_eq_none_of_all_lt (below h₂.1 hlt)] at this
          cases this
        · exact heq
        · have := h k₂
          rw [List.lookup_cons, List.lookup_cons] at this
          simp only [beq_self_eq_true] at this
          have hne : (k₂ == k₁) = false := by
            cases hb : k₂ == k₁
            · rfl
            · have := eq_of_beq hb; subst this; simp at hgt
          rw [hne, lookup_eq_none_of_all_lt (below h₁.1 hgt)] at this
          cases this
      subst hkey
      have hv : v₁ = v₂ := by have := h k₁; simpa [List.lookup_cons] using this
      subst hv
      congr 1
      refine eq_of_sorted_of_lookup h₁.2 h₂.2 (fun k => ?_)
      by_cases hk : k = k₁
      · subst hk
        have e1 : ∀ kv ∈ r₁, Path.lt k kv.1 = true := h₁.1
        have e2 : ∀ kv ∈ r₂, Path.lt k kv.1 = true := h₂.1
        rw [lookup_eq_none_of_all_lt e1, lookup_eq_none_of_all_lt e2]
      · have := h k
        have hb : (k == k₁) = false := by simp [hk]
        simpa [List.lookup_cons, hb] using this

end PTree

namespace PathMap
variable {V : Type}

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], _ => Nat.le_refl _
  | x :: l, a => Nat.le_trans (Nat.le_max_left a x) (le_foldl_max l (max a x))

theorem mem_le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | y :: l, a, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right a x) (le_foldl_max l _)
      · exact mem_le_foldl_max l _ x h

/-- Every location is shallower than the fuel, by two. -/
theorem lt_fuel {T : PathMap V} {r : Path} (h : r ∈ T.paths) : r.length + 2 ≤ T.fuel := by
  unfold fuel
  have := mem_le_foldl_max (T.paths.map List.length) 0 r.length (List.mem_map.mpr ⟨r, h, rfl⟩)
  omega

end PathMap
/-! ## (a), byte level: serialize, then flatten -/
namespace PTree
variable {V : Type}

theorem zipWith_map_self {α β γ : Type} (g : α → β → γ) (f : α → β) :
    ∀ l : List α, List.zipWith g l (l.map f) = l.map (fun a => g a (f a))
  | [] => rfl
  | a :: l => by simp [zipWith_map_self g f l]

theorem find?_beq (b : UInt8) :
    ∀ m : List UInt8, m.find? (fun a => a == b) = if b ∈ m then some b else none
  | [] => by simp
  | a :: m => by
      by_cases h : a = b
      · subst h; simp
      · have : (a == b) = false := by simp [h]
        simp [this, find?_beq b m, Ne.symm h]

/-- The kids a fold builds: one per mask byte, the edge starting with it. -/
theorem kidAt_map {f : UInt8 → Path × PTree V} (hf : ∀ a, (f a).1.headD 0 = a) (b : UInt8)
    (m : List UInt8) : kidAt (m.map f) b = if b ∈ m then some (f b) else none := by
  unfold kidAt
  rw [List.find?_map]
  have : ((fun k : Path × PTree V => k.1.headD 0 == b) ∘ f) = fun a => a == b := by
    funext a; simp only [Function.comp, hf a]
  rw [this, find?_beq]
  split <;> rfl

theorem heads_map {f : UInt8 → Path × PTree V} (hf : ∀ a, (f a).1.headD 0 = a) (m : List UInt8) :
    heads (m.map f) = m := by
  induction m with
  | nil => rfl
  | cons a m ih => simp only [heads, List.map_cons] at ih ⊢; rw [hf a, ih]

theorem nodup_of_sorted {l : List UInt8} (h : l.Pairwise (· < ·)) : l.Nodup :=
  h.imp (fun hab heq => by subst heq; rw [UInt8.lt_iff_toNat_lt] at hab; omega)

end PTree

namespace PathMap
open PTree
variable {V : Type}

theorem cata_succ {W : Type} (T : PathMap V) (alg : Option V → ByteMask → List W → W) (d : W)
    (n : Nat) (q : Path) :
    T.cata alg d (n + 1) q =
      alg (T.valAt q) (T.childMask q) ((T.childMask q).map fun b => T.cata alg d n (q ++ [b])) := rfl

/-- The byte tree of `T` at `q` holds exactly what `T` holds below `q`. -/
theorem lookup_cata_bytes {T : PathMap V} (hT : T.WF) (d : PTree V) :
    ∀ (p q : Path) (n : Nat), (T.entries.lookup q).isSome →
      (∀ r, (T.entries.lookup r).isSome → r.length < q.length + n) →
      (ents (T.cata algB d n q)).lookup p = T.entries.lookup (q ++ p) := by
  intro p
  induction p with
  | nil =>
    intro q n hq hb
    cases n with
    | zero => exact absurd (hb q hq) (by omega)
    | succ n =>
      rw [cata_succ, algB, lookup_ents_nil, List.append_nil, lookup_eq_valAt hq]
  | cons b p ih =>
    intro q n hq hb
    cases n with
    | zero => exact absurd (hb q hq) (by omega)
    | succ n =>
      have hm := T.sorted_childMask q
      rw [cata_succ, algB, zipWith_map_self, lookup_ents_cons,
        lookup_entsKids _ (by simp) (by rw [heads_map (by simp)]; exact nodup_of_sorted hm),
        kidAt_map (by simp)]
      by_cases hbm : b ∈ T.childMask q
      · have hq' := (T.mem_childMask q b).mp hbm
        simp only [hbm, if_true, Option.bind_some, List.tail_cons, edgeLook]
        rw [ih (q ++ [b]) n hq' (fun r hr => by have := hb r hr; simp; omega)]
        simp
      · simp only [hbm, if_false, Option.bind_none]
        symm
        cases h : T.entries.lookup (q ++ b :: p) with
        | none => rfl
        | some _ =>
          have : (T.entries.lookup (q ++ [b] ++ p)).isSome := by simp [h]
          exact absurd ((T.mem_childMask q b).mpr (hT.prefix p this)) hbm

end PathMap
namespace PTree
variable {V : Type}

theorem ByteForm.ordered : ∀ {t : PTree V}, ByteForm t → Ordered t := by
  intro t
  induction t using PTree.ind with
  | h v kids ih =>
    intro hb
    cases hb with
    | node _ _ hp hl hk =>
      exact .node v kids hp (fun k hk' => by
          intro h; have := hl k hk'; rw [h] at this; cases this)
        (fun k hk' => ih k.1 k.2 hk' (hk k hk'))

end PTree

namespace PathMap
open PTree
variable {V : Type}

theorem byteForm_cata (T : PathMap V) {d : PTree V} (hd : ByteForm d) :
    ∀ (n : Nat) (q : Path), ByteForm (T.cata algB d n q)
  | 0, _ => hd
  | n + 1, q => by
      rw [cata_succ, algB, zipWith_map_self]
      refine .node _ _ (by rw [heads_map (by simp)]; exact T.sorted_childMask q) (by simp) ?_
      intro k hk
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hk
      exact byteForm_cata T hd n (q ++ [b])

/-- `toBytes` builds a byte-form tree. -/
theorem byteForm_toBytes (T : PathMap V) : ByteForm (toBytes T) :=
  byteForm_cata T (.node none [] (by simp [heads]) (by simp) (by simp)) _ _

theorem bound_fuel (T : PathMap V) :
    ∀ r, (T.entries.lookup r).isSome → r.length < ([] : Path).length + T.fuel := by
  intro r hr
  have := lt_fuel ((T.mem_paths r).mpr hr)
  simp; omega

/-- **(a), byte level.**  Serializing a well-formed trie into its byte tree
and flattening the tree gives the trie back. -/
theorem flatten_toBytes {T : PathMap V} (hT : T.WF) : (toBytes T).flatten = T := by
  have h := eq_of_sorted_of_lookup (sorted_ents _ (byteForm_toBytes T).ordered) hT.1
    (fun k => by
      rw [toBytes, cataStep, lookup_cata_bytes hT _ k [] _ hT.root (bound_fuel T)]
      rfl)
  cases T; simp only [flatten] at h ⊢; rw [h]

end PathMap
/-! ## (a), line level -/
namespace PathMap
open PTree
variable {V : Type}

theorem follow_succ (T : PathMap V) (n : Nat) (q : Path) :
    T.follow (n + 1) q =
      if isFeature T q then q else
      match T.childMask q with
      | [b] => follow T n (q ++ [b])
      | _ => q := rfl

/-- `follow` extends its start. -/
theorem follow_shape (T : PathMap V) : ∀ (n : Nat) (r : Path), ∃ x, T.follow n r = r ++ x
  | 0, r => ⟨[], by simp [follow]⟩
  | n + 1, r => by
      rw [follow_succ]
      split
      · exact ⟨[], by simp⟩
      · split
        · rename_i c _
          obtain ⟨x, hx⟩ := follow_shape T n (r ++ [c])
          exact ⟨c :: x, by simp [hx]⟩
        · exact ⟨[], by simp⟩

theorem valAt_none_of_not_feature {T : PathMap V} {q : Path} (h : ¬ isFeature T q = true) :
    T.valAt q = none := by
  unfold isFeature at h
  cases hv : T.valAt q with
  | none => rfl
  | some _ => simp [hv] at h

/-- `follow` reaches an existing location. -/
theorem follow_exists (T : PathMap V) :
    ∀ (n : Nat) (r : Path), (T.entries.lookup r).isSome → (T.entries.lookup (T.follow n r)).isSome
  | 0, r, h => h
  | n + 1, r, h => by
      rw [follow_succ]
      split
      · exact h
      · split
        · rename_i c hm
          exact follow_exists T n _ ((T.mem_childMask r c).mp (by rw [hm]; simp))
        · exact h

/-- **Lookups along a line.**  Below `r`, the trie is the chain `follow` walks
over (valueless, one child each) and then whatever is below its end. -/
theorem lookup_follow {T : PathMap V} (hT : T.WF) :
    ∀ (n : Nat) (r x : Path), (T.entries.lookup r).isSome → T.follow n r = r ++ x →
      ∀ p, T.entries.lookup (r ++ p) = edgeLook (fun s => T.entries.lookup (r ++ x ++ s)) x p
  | 0, r, x, _, hx, p => by
      simp only [follow] at hx
      have : x = [] := by simpa using hx
      subst this; simp [edgeLook]
  | n + 1, r, x, hr, hx, p => by
      rw [follow_succ] at hx
      split at hx
      · have : x = [] := by simpa using hx
        subst this; simp [edgeLook]
      · rename_i hnf
        split at hx
        · rename_i c hm
          obtain ⟨x', hx'⟩ := follow_shape T n (r ++ [c])
          have hxe : x = c :: x' := by rw [hx'] at hx; simpa using hx.symm
          subst hxe
          have hrc : (T.entries.lookup (r ++ [c])).isSome :=
            (T.mem_childMask r c).mp (by rw [hm]; simp)
          cases p with
          | nil =>
            rw [List.append_nil, lookup_eq_valAt hr, valAt_none_of_not_feature hnf]; rfl
          | cons c' p =>
            simp only [edgeLook]
            by_cases hc : c' = c
            · subst hc
              have := lookup_follow hT n (r ++ [c']) x' hrc hx' p
              simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
              rw [if_pos trivial, this]
            · rw [if_neg hc]
              cases hl : T.entries.lookup (r ++ c' :: p) with
              | none => rfl
              | some _ =>
                have : (T.entries.lookup (r ++ [c'] ++ p)).isSome := by simp [hl]
                have hm' := (T.mem_childMask r c').mpr (hT.prefix p this)
                rw [hm] at hm'; simp at hm'; exact absurd hm' hc
        · have : x = [] := by simpa using hx
          subst this; simp [edgeLook]

end PathMap
namespace PathMap
open PTree
variable {V : Type}

theorem cataJ_succ {W : Type} (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W)
    (d : W) (n : Nat) (q sub : Path) :
    T.cataJ alg d (n + 1) q sub =
      alg sub (T.valAt q) (T.childMask q) ((T.childMask q).map fun b =>
        T.cataJ alg d n (T.follow T.fuel (q ++ [b])) ((T.follow T.fuel (q ++ [b])).drop (q.length + 1))) := rfl

theorem cataJ_fst (T : PathMap V) (d : Path × PTree V) (n : Nat) (q sub : Path) :
    (T.cataJ algL d (n + 1) q sub).1 = sub := rfl

/-- The kids `algL` builds. -/
theorem cataJ_lines (T : PathMap V) (d : Path × PTree V) (n : Nat) (q sub : Path) :
    T.cataJ algL d (n + 1) q sub =
      (sub, .node (T.valAt q) ((T.childMask q).map fun b =>
        let w := T.cataJ algL d n (T.follow T.fuel (q ++ [b]))
          ((T.follow T.fuel (q ++ [b])).drop (q.length + 1))
        (b :: w.1, w.2))) := by
  rw [cataJ_succ, algL, zipWith_map_self]

/-- The line tree of `T` at `q` holds exactly what `T` holds below `q`. -/
theorem lookup_cataJ_lines {T : PathMap V} (hT : T.WF) (d : Path × PTree V) :
    ∀ (N : Nat) (p : Path), p.length ≤ N → ∀ (q sub : Path) (n : Nat), (T.entries.lookup q).isSome →
      (∀ r, (T.entries.lookup r).isSome → r.length < q.length + n) →
      (ents (T.cataJ algL d n q sub).2).lookup p = T.entries.lookup (q ++ p) := by
  intro N
  induction N with
  | zero =>
    intro p hp q sub n hq hb
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    cases n with
    | zero => exact absurd (hb q hq) (by omega)
    | succ n => rw [cataJ_lines, lookup_ents_nil, List.append_nil, lookup_eq_valAt hq]
  | succ N ih =>
    intro p hp q sub n hq hb
    cases n with
    | zero => exact absurd (hb q hq) (by omega)
    | succ n =>
    cases p with
    | nil => rw [cataJ_lines, lookup_ents_nil, List.append_nil, lookup_eq_valAt hq]
    | cons b p =>
      have hm := T.sorted_childMask q
      rw [cataJ_lines, lookup_ents_cons,
        lookup_entsKids _ (by simp) (by rw [heads_map (by simp)]; exact nodup_of_sorted hm),
        kidAt_map (by simp)]
      by_cases hbm : b ∈ T.childMask q
      · have hq' := (T.mem_childMask q b).mp hbm
        obtain ⟨x, hx⟩ := follow_shape T T.fuel (q ++ [b])
        have hf := follow_exists T T.fuel _ hq'
        rw [hx] at hf
        have hlen : (q ++ [b] ++ x).length = q.length + 1 + x.length := by simp; omega
        cases n with
        | zero => exact absurd (hb _ hf) (by omega)
        | succ n =>
        simp only [hbm, if_true, Option.bind_some, List.tail_cons, hx, cataJ_fst]
        have hdrop : (q ++ [b] ++ x).drop (q.length + 1) = x := by
          have : q ++ [b] ++ x = (q ++ [b]) ++ x := rfl
          rw [this, List.drop_append_of_le_length (by simp)]; simp
        rw [hdrop]
        have hfol := lookup_follow hT T.fuel (q ++ [b]) x hq' hx p
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hfol ⊢
        rw [hfol]
        apply edgeLook_congr
        intro s hs
        have := ih s (by simp at hp; omega) (q ++ [b] ++ x) x (n + 1) hf
          (fun r hr => by have := hb r hr; omega)
        simpa using this
      · simp only [hbm, if_false, Option.bind_none]
        symm
        cases h : T.entries.lookup (q ++ b :: p) with
        | none => rfl
        | some _ =>
          have : (T.entries.lookup (q ++ [b] ++ p)).isSome := by simp [h]
          exact absurd ((T.mem_childMask q b).mpr (hT.prefix p this)) hbm

end PathMap
namespace PathMap
open PTree
variable {V : Type}

theorem fuel_succ (T : PathMap V) : ∃ k, T.fuel = k + 2 := ⟨_, rfl⟩

/-- The jumping fold starts at the first feature from the root, whichever case. -/
theorem cataJump_eq {W : Type} (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W) (d : W) :
    T.cataJump alg d = T.cataJ alg d T.fuel (T.follow T.fuel []) (T.follow T.fuel []) := by
  unfold cataJump
  split
  · rename_i h
    obtain ⟨k, hk⟩ := fuel_succ T
    have : T.follow T.fuel [] = [] := by rw [hk, follow_succ, if_pos h]
    rw [this]
  · rfl

theorem toLines_eq (T : PathMap V) :
    T.toLines = rootLine (T.follow T.fuel [],
      (T.cataJ algL ([], .node none []) T.fuel (T.follow T.fuel []) (T.follow T.fuel [])).2) := by
  unfold toLines
  rw [cataJump_eq]
  congr 1

theorem lookup_rootLine (t : PTree V) (p : Path) :
    ∀ f : Path, (ents (rootLine (f, t))).lookup p = edgeLook (fun s => (ents t).lookup s) f p
  | [] => rfl
  | c :: x => by
      simp only [rootLine, List.isEmpty_cons, Bool.false_eq_true, if_false]
      cases p with
      | nil => rfl
      | cons b p =>
        rw [lookup_ents_cons, lookup_entsKids _ (by simp) (by simp [heads])]
        simp only [kidAt, List.find?_cons, List.find?_nil, edgeLook, List.headD_cons]
        by_cases h : b = c
        · subst h; simp
        · have : (c == b) = false := by simp [Ne.symm h]
          simp [this, h]

theorem ordered_rootLine {t : PTree V} (h : Ordered t) : ∀ f : Path, Ordered (rootLine (f, t))
  | [] => h
  | c :: x => by
      simp only [rootLine, List.isEmpty_cons, Bool.false_eq_true, if_false]
      exact .node _ _ (by simp [heads]) (by simp) (by simp [h])

theorem ordered_cataJ (T : PathMap V) {d : Path × PTree V} (hd : Ordered d.2) :
    ∀ (n : Nat) (q sub : Path), Ordered (T.cataJ algL d n q sub).2
  | 0, _, _ => hd
  | n + 1, q, sub => by
      rw [cataJ_lines]
      refine .node _ _ (by rw [heads_map (by simp)]; exact T.sorted_childMask q) (by simp) ?_
      intro k hk
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hk
      exact ordered_cataJ T hd n _ _

/-- **(a), line level.**  Serializing a well-formed trie into its line tree and
flattening the tree gives the trie back. -/
theorem flatten_toLines {T : PathMap V} (hT : T.WF) : (toLines T).flatten = T := by
  obtain ⟨f, hf⟩ := follow_shape T T.fuel []
  simp only [List.nil_append] at hf
  have hfe := follow_exists T T.fuel [] hT.root
  rw [hf] at hfe
  have hord : Ordered T.toLines := by
    rw [toLines_eq]
    exact ordered_rootLine (ordered_cataJ T (.node none [] (by simp [heads]) (by simp) (by simp)) _ _ _) _
  have h := eq_of_sorted_of_lookup (sorted_ents _ hord) hT.1 (fun k => by
    rw [toLines_eq, hf, lookup_rootLine]
    have := lookup_follow hT T.fuel [] f hT.root (by simpa using hf) k
    simp only [List.nil_append] at this
    rw [this]
    apply edgeLook_congr
    intro s _
    exact lookup_cataJ_lines hT _ s.length s (Nat.le_refl _) f f T.fuel hfe
      (fun r hr => by have := lt_fuel ((T.mem_paths r).mpr hr); omega))
  cases T; simp only [flatten] at h ⊢; rw [h]

end PathMap
/-! ## (b): flatten, then serialize -/
namespace PTree
variable {V : Type}

theorem kidAt_isSome (kids : List (Path × PTree V)) (b : UInt8) :
    (kidAt kids b).isSome ↔ b ∈ heads kids := by
  unfold kidAt heads
  rw [List.find?_isSome]
  constructor
  · rintro ⟨k, hk, h⟩; exact List.mem_map.mpr ⟨k, hk, by simpa using h⟩
  · intro h; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h; exact ⟨k, hk, by simp⟩

theorem kidAt_of_mem {kids : List (Path × PTree V)} (hnd : (heads kids).Nodup) {k : Path × PTree V}
    (hk : k ∈ kids) : kidAt kids (k.1.headD 0) = some k := by
  induction kids with
  | nil => cases hk
  | cons k' rest ih =>
    simp only [heads, List.map_cons, List.nodup_cons] at hnd
    unfold kidAt at ih ⊢
    rcases List.mem_cons.mp hk with rfl | hk
    · simp
    · have hne : (k'.1.headD 0 == k.1.headD 0) = false := by
        have : k'.1.headD 0 ≠ k.1.headD 0 := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨k, hk, rfl⟩)
        exact beq_eq_false_iff_ne.mpr this
      rw [List.find?_cons, hne]
      exact ih hnd.2 hk

theorem lookup_ents_isSome_nil (c : PTree V) : ((ents c).lookup []).isSome := by
  cases c; rw [lookup_ents_nil]; rfl

/-- The child below edge `e` of a node is what the node holds below `e`. -/
theorem lookup_kid {v : Option V} {kids : List (Path × PTree V)} (hne : ∀ k ∈ kids, k.1 ≠ [])
    (hnd : (heads kids).Nodup) {e : Path} {c : PTree V} (hk : (e, c) ∈ kids) (r : Path) :
    (ents (node v kids)).lookup (e ++ r) = (ents c).lookup r := by
  obtain ⟨b, x, rfl⟩ : ∃ b x, e = b :: x := by
    cases e with
    | nil => exact absurd rfl (hne _ hk)
    | cons b x => exact ⟨b, x, rfl⟩
  have := kidAt_of_mem hnd hk
  simp only [List.headD_cons] at this
  rw [List.cons_append, lookup_ents_cons, lookup_entsKids _ hne hnd, this]
  simp [edgeLook_append]

theorem edgeLook_append_left (g : Path → Option (Option V)) :
    ∀ (y w p : Path), edgeLook g (y ++ w) (y ++ p) = edgeLook g w p
  | [], _, _ => rfl
  | c :: y, w, p => by simp [edgeLook, edgeLook_append_left g y w p]

theorem mem_blockEnts_append (L : List (Path × Option V)) (kv : Path × Option V) (h : kv ∈ L) :
    ∀ e : Path, (e ++ kv.1, kv.2) ∈ blockEnts e L
  | [] => h
  | [b] => List.mem_map.mpr ⟨kv, h, rfl⟩
  | b :: c :: x => by
      rw [blockEnts]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, mem_blockEnts_append L kv h (c :: x), rfl⟩)

theorem mem_entsKids_of_mem {kids : List (Path × PTree V)} {k : Path × PTree V} (hk : k ∈ kids)
    {kv : Path × Option V} (h : kv ∈ ents k.2) : (k.1 ++ kv.1, kv.2) ∈ entsKids kids := by
  induction kids with
  | nil => cases hk
  | cons k' rest ih =>
    rw [entsKids, List.mem_append]
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl (mem_blockEnts_append _ kv h _)
    · exact Or.inr (ih hk)

theorem height_kid {v : Option V} {kids : List (Path × PTree V)} {k : Path × PTree V}
    (hk : k ∈ kids) : height k.2 + 1 ≤ height (node v kids) := by
  have : ∀ ks : List (Path × PTree V), k ∈ ks → height k.2 ≤ height.heightKids ks := by
    intro ks hks
    induction ks with
    | nil => cases hks
    | cons k' rest ih =>
      rw [height.heightKids]
      rcases List.mem_cons.mp hks with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
  have := this kids hk
  rw [height]; omega

theorem heightKids_cases : ∀ kids : List (Path × PTree V),
    height.heightKids kids = 0 ∨ ∃ k ∈ kids, height.heightKids kids = height k.2
  | [] => Or.inl rfl
  | (e, c) :: rest => by
      rw [height.heightKids]
      rcases heightKids_cases rest with h | ⟨k, hk, h⟩
      · right; refine ⟨(e, c), List.mem_cons_self .., ?_⟩; rw [h]; simp
      · right
        by_cases hm : height c ≤ height.heightKids rest
        · exact ⟨k, List.mem_cons_of_mem _ hk, by rw [Nat.max_eq_right hm, h]⟩
        · exact ⟨(e, c), List.mem_cons_self .., by rw [Nat.max_eq_left (by omega)]⟩

/-- Some location is as deep as the tree is high (edges non-empty). -/
theorem deep_key : ∀ t : PTree V, Ordered t → ∃ kv ∈ ents t, height t ≤ kv.1.length + 1 := by
  refine PTree.ind (fun v kids ih ho => ?_)
  cases ho with
  | node _ _ _ hne hk =>
    rcases heightKids_cases kids with h | ⟨k, hkm, h⟩
    · exact ⟨([], v), by simp [ents], by rw [height, h]; simp⟩
    · obtain ⟨kv, hkv, hd⟩ := ih k.1 k.2 hkm (hk k hkm)
      refine ⟨(k.1 ++ kv.1, kv.2), ?_, ?_⟩
      · rw [ents]; exact List.mem_cons_of_mem _ (mem_entsKids_of_mem hkm hkv)
      · have : k.1.length ≥ 1 := by
          cases h' : k.1 with
          | nil => exact absurd h' (hne k hkm)
          | cons _ _ => simp
        rw [height, h]; simp; omega

end PTree
namespace PathMap
open PTree
variable {V : Type}

/-- `T` holds below `q` exactly what `P` holds. -/
def Looks (T : PathMap V) (q : Path) (P : PTree V) : Prop :=
  ∀ r, T.entries.lookup (q ++ r) = (ents P).lookup r

theorem valAt_of_looks {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) : T.valAt q = v := by
  rw [valAt_eq]; have := h []; rw [List.append_nil, lookup_ents_nil] at this; rw [this]; rfl

theorem childMask_of_looks {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) (hne : ∀ k ∈ kids, k.1 ≠ []) (hp : (heads kids).Pairwise (· < ·)) :
    T.childMask q = heads kids := by
  apply eq_of_sorted_of_mem (T.sorted_childMask q) hp
  intro b
  rw [T.mem_childMask, h [b], lookup_ents_cons, lookup_entsKids _ hne (nodup_of_sorted hp),
    ← kidAt_isSome]
  cases hk : kidAt kids b with
  | none => simp
  | some k => simpa using edgeLook_nil_isSome _ (lookup_ents_isSome_nil k.2) _

theorem isFeature_of_looks {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) (hne : ∀ k ∈ kids, k.1 ≠ []) (hp : (heads kids).Pairwise (· < ·)) :
    T.isFeature q = (node v kids).isFeat := by
  simp only [isFeature, childCount, valAt_of_looks h, childMask_of_looks h hne hp, isFeat, heads,
    List.length_map]

theorem looks_kid {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) (hne : ∀ k ∈ kids, k.1 ≠ []) (hnd : (heads kids).Nodup)
    {e : Path} {c : PTree V} (hk : (e, c) ∈ kids) : Looks T (q ++ e) c := by
  intro r; rw [List.append_assoc, h, lookup_kid hne hnd hk]

theorem height_pos (t : PTree V) : 1 ≤ t.height := by cases t; simp [height]

theorem cata_of_looks (T : PathMap V) (d : PTree V) :
    ∀ P : PTree V, ByteForm P → ∀ (q : Path) (n : Nat), P.height ≤ n → Looks T q P →
      T.cata algB d n q = P := by
  refine PTree.ind (fun v kids ih => ?_)
  intro hb q n hn hl
  cases hb with
  | node _ _ hp hl1 hk =>
  have hne : ∀ k ∈ kids, k.1 ≠ [] := fun k hk' h => by have := hl1 k hk'; rw [h] at this; cases this
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := height_pos (node v kids); omega⟩
  rw [cata_succ, algB, zipWith_map_self, valAt_of_looks hl, childMask_of_looks hl hne hp]
  congr 1
  rw [heads, List.map_map]
  conv => rhs; rw [← List.map_id kids]
  apply List.map_congr_left
  rintro ⟨e, c⟩ hkm
  obtain ⟨b, rfl⟩ : ∃ b, e = [b] := by
    have := hl1 _ hkm
    match e, this with
    | [b], _ => exact ⟨b, rfl⟩
  simp only [Function.comp, List.headD_cons, id]
  rw [ih [b] c hkm (hk _ hkm) (q ++ [b]) n (by have := height_kid (v := v) hkm; simp at this; omega)
    (looks_kid hl hne (nodup_of_sorted hp) hkm)]

theorem height_le_fuel {P : PTree V} (h : Ordered P) : P.height ≤ P.flatten.fuel := by
  obtain ⟨kv, hkv, hd⟩ := deep_key P h
  have := lt_fuel (T := P.flatten) (r := kv.1) (List.mem_map.mpr ⟨kv, hkv, rfl⟩)
  omega

/-- **(b), byte level.**  Flattening a byte-form tree and serializing the trie
gives the tree back.  With (a): byte-form trees and well-formed tries are in
bijection. -/
theorem toBytes_flatten {P : PTree V} (h : ByteForm P) : toBytes P.flatten = P :=
  cata_of_looks _ _ P h [] _ (height_le_fuel h.ordered) (fun _ => rfl)

end PathMap
namespace PTree
variable {V : Type}

theorem LineForm.ordered : ∀ {t : PTree V}, LineForm t → Ordered t := by
  intro t
  induction t using PTree.ind with
  | h v kids ih =>
    intro hl
    cases hl with
    | node _ _ hp hf hk =>
      exact .node v kids hp (fun k hk' => (hf k hk').1) (fun k hk' => ih k.1 k.2 hk' (hk k hk'))

end PTree

namespace PathMap
open PTree
variable {V : Type}

/-- `follow` walks a line: valueless one-child locations up to a feature. -/
theorem follow_line (T : PathMap V) : ∀ (x r : Path) (N : Nat), x.length ≤ N →
    (∀ y c z, x = y ++ c :: z → T.isFeature (r ++ y) = false ∧ T.childMask (r ++ y) = [c]) →
    T.isFeature (r ++ x) = true → T.follow N r = r ++ x
  | [], r, N, _, _, hf => by
      simp only [List.append_nil] at hf ⊢
      cases N with
      | zero => rfl
      | succ N => rw [follow_succ, if_pos hf]
  | c :: z, r, N, hN, hch, hf => by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at hN; omega⟩
      obtain ⟨h1, h2⟩ := hch [] c z rfl
      simp only [List.append_nil] at h1 h2
      rw [follow_succ, if_neg (by simp [h1]), h2]
      simp only
      have := follow_line T z (r ++ [c]) M (by simp at hN; omega)
        (fun y c' z' hy => by
          have := hch (c :: y) c' z' (by simp [hy])
          simpa using this)
        (by simpa using hf)
      rw [this]; simp

/-- Below the first byte of a kid's edge, a node holds the edge's rest and then the kid. -/
theorem lookup_looks_edge {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) (hne : ∀ k ∈ kids, k.1 ≠ []) (hnd : (heads kids).Nodup)
    {b : UInt8} {x : Path} {c : PTree V} (hk : (b :: x, c) ∈ kids) (p : Path) :
    T.entries.lookup (q ++ b :: p) = edgeLook (fun s => (ents c).lookup s) x p := by
  have := kidAt_of_mem hnd hk
  simp only [List.headD_cons] at this
  rw [h, lookup_ents_cons, lookup_entsKids _ hne hnd, this]; rfl

theorem single_of_mem {l : List UInt8} {c : UInt8} (hp : l.Pairwise (· < ·)) (h : ∀ b, b ∈ l ↔ b = c) :
    l = [c] :=
  eq_of_sorted_of_mem hp (List.pairwise_singleton _ _) (fun b => by rw [h]; simp)

/-- A kid's edge is the line `follow` walks from its first byte. -/
theorem follow_kid {T : PathMap V} {q : Path} {v : Option V} {kids : List (Path × PTree V)}
    (h : Looks T q (node v kids)) (hl : LineForm (node v kids))
    {b : UInt8} {x : Path} {c : PTree V} (hk : (b :: x, c) ∈ kids) (N : Nat) (hN : x.length ≤ N) :
    T.follow N (q ++ [b]) = q ++ b :: x := by
  cases hl with
  | node _ _ hp hf hks =>
  have hne : ∀ k ∈ kids, k.1 ≠ [] := fun k hk' => (hf k hk').1
  have hnd := nodup_of_sorted hp
  have hedge := lookup_looks_edge h hne hnd hk
  rw [follow_line T x (q ++ [b]) N hN]
  · simp
  · intro y c' z hx
    subst hx
    have hloc : ∀ s, T.entries.lookup (q ++ [b] ++ y ++ s) =
        edgeLook (fun s => (ents c).lookup s) (c' :: z) s := by
      intro s
      have := hedge (y ++ s)
      rw [edgeLook_append_left] at this
      simpa using this
    have hv : T.valAt (q ++ [b] ++ y) = none := by
      rw [valAt_eq]; have := hloc []; rw [List.append_nil] at this; rw [this]; rfl
    have hm : T.childMask (q ++ [b] ++ y) = [c'] := by
      apply single_of_mem (T.sorted_childMask _)
      intro b''
      rw [T.mem_childMask, hloc [b'']]
      simp only [edgeLook]
      by_cases hb : b'' = c'
      · subst hb
        simpa using edgeLook_nil_isSome _ (lookup_ents_isSome_nil c) z
      · simp [hb]
    have e : q ++ [b] ++ y = q ++ b :: y := by simp
    rw [e] at hv hm ⊢
    refine ⟨?_, hm⟩
    simp [isFeature, hv, childCount, hm]
  · obtain ⟨v', kids'⟩ := c
    cases hks _ hk with
    | node _ _ hp' hf' _ =>
    have hlc : Looks T (q ++ (b :: x)) (node v' kids') := looks_kid h hne hnd hk
    have := isFeature_of_looks hlc (fun k hk' => (hf' k hk').1) hp'
    simp only [List.append_assoc, List.singleton_append] at this ⊢
    rw [this]; exact (hf _ hk).2

theorem cataJ_of_looks (T : PathMap V) (d : Path × PTree V) :
    ∀ P : PTree V, LineForm P → ∀ (q sub : Path) (n : Nat), P.height ≤ n → Looks T q P →
      T.cataJ algL d n q sub = (sub, P) := by
  refine PTree.ind (fun v kids ih => ?_)
  intro hlf q sub n hn hl
  have hlf' := hlf
  cases hlf with
  | node _ _ hp hf hk =>
  have hne : ∀ k ∈ kids, k.1 ≠ [] := fun k hk' => (hf k hk').1
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := height_pos (node v kids); omega⟩
  rw [cataJ_lines, valAt_of_looks hl, childMask_of_looks hl hne hp]
  congr 2
  rw [heads, List.map_map]
  conv => rhs; rw [← List.map_id kids]
  apply List.map_congr_left
  rintro ⟨e, c⟩ hkm
  obtain ⟨b, x, rfl⟩ : ∃ b x, e = b :: x := by
    cases e with
    | nil => exact absurd rfl (hne _ hkm)
    | cons b x => exact ⟨b, x, rfl⟩
  simp only [Function.comp, List.headD_cons, id]
  have hlc := looks_kid hl hne (nodup_of_sorted hp) hkm
  have hex : (T.entries.lookup (q ++ (b :: x))).isSome := by
    have := hlc []; rw [List.append_nil] at this; rw [this]; exact lookup_ents_isSome_nil c
  have hfuel := lt_fuel ((T.mem_paths _).mpr hex)
  rw [follow_kid hl hlf' hkm T.fuel (by simp at hfuel; omega)]
  have hdrop : (q ++ b :: x).drop (q.length + 1) = x := by
    rw [show q ++ b :: x = (q ++ [b]) ++ x by simp, List.drop_append_of_le_length (by simp)]; simp
  rw [hdrop, ih (b :: x) c hkm (hk _ hkm) (q ++ b :: x) x n
    (by have := height_kid (v := v) hkm; simp at this; omega) hlc]

/-- **(b), line level.**  Flattening a line-form tree and serializing the trie
gives the tree back.  With (a): line-form trees and well-formed tries are in
bijection. -/
theorem toLines_flatten {P : PTree V} (h : LineForm P) : toLines P.flatten = P := by
  have hl : Looks P.flatten [] P := fun _ => rfl
  have hh := height_le_fuel h.ordered
  rw [toLines_eq]
  obtain ⟨v, kids⟩ := P
  have h' := h
  cases h' with
  | node _ _ hp hf hk =>
  have hne : ∀ k ∈ kids, k.1 ≠ [] := fun k hk' => (hf k hk').1
  have hfeat := isFeature_of_looks hl hne hp
  obtain ⟨k, hk2⟩ := fuel_succ (node v kids).flatten
  by_cases hft : (node v kids).isFeat = true
  · have hf0 : (node v kids).flatten.follow (node v kids).flatten.fuel [] = [] := by
      rw [hk2, follow_succ, if_pos (by rw [hfeat]; exact hft)]
    rw [hf0, cataJ_of_looks _ _ _ h [] [] _ hh hl]; rfl
  · simp only [isFeat, Bool.or_eq_true, Option.isSome_iff_ne_none, bne_iff_ne, ne_eq,
      Decidable.not_not, not_or] at hft
    obtain ⟨hv, hlen⟩ := hft
    subst hv
    obtain ⟨⟨e, c⟩, rfl⟩ : ∃ kc, kids = [kc] := by
      match kids, hlen with
      | [kc], _ => exact ⟨kc, rfl⟩
    obtain ⟨b, x, rfl⟩ : ∃ b x, e = b :: x := by
      cases e with
      | nil => exact absurd rfl (hne _ (List.mem_singleton_self _))
      | cons b x => exact ⟨b, x, rfl⟩
    have hm : (node none [(b :: x, c)]).flatten.childMask [] = [b] := by
      rw [childMask_of_looks hl hne hp]; rfl
    have hlc := looks_kid hl hne (nodup_of_sorted hp) (List.mem_singleton_self _)
    have hex : ((node none [(b :: x, c)]).flatten.entries.lookup (b :: x)).isSome := by
      have := hlc []; rw [List.append_nil, List.nil_append] at this; rw [this]; exact lookup_ents_isSome_nil c
    have hfuel := lt_fuel (((node none [(b :: x, c)]).flatten.mem_paths _).mpr hex)
    have hf0 : (node none [(b :: x, c)]).flatten.follow (node none [(b :: x, c)]).flatten.fuel [] = b :: x := by
      rw [hk2, follow_succ, if_neg (by rw [hfeat]; simp [isFeat]), hm]
      simp only
      have := follow_kid hl h (List.mem_singleton_self _) (k + 1) (by simp at hfuel; omega)
      simpa using this
    rw [hf0, cataJ_of_looks _ _ c (hk _ (List.mem_singleton_self _)) (b :: x) (b :: x) _
      (by have := height_kid (v := (none : Option V)) (List.mem_singleton_self (b :: x, c)); simp only at this; omega)
      (by simpa using hlc)]
    rfl

end PathMap
/-! ## (d): deserialize with an anamorphism -/
namespace PTree
variable {V : Type}

/-- Put `e` in front of a valued location. -/
def preV (e : Path) (pv : Path × V) : Path × V := (e ++ pv.1, pv.2)

theorem filterMap_pre (b : UInt8) : ∀ L : List (Path × Option V),
    (L.map (pre b)).filterMap valued = (L.filterMap valued).map (preV [b])
  | [] => rfl
  | (p, o) :: L => by
      cases o <;> simp [valued, pre, preV, List.filterMap_cons, filterMap_pre b L]

theorem filterMap_blockEnts (L : List (Path × Option V)) :
    ∀ e : Path, (blockEnts e L).filterMap valued = (L.filterMap valued).map (preV e)
  | [] => by
      simp only [blockEnts]
      conv => lhs; rw [← List.map_id (L.filterMap valued)]
      congr 1
  | [b] => filterMap_pre b L
  | b :: c :: x => by
      rw [blockEnts, List.filterMap_cons, show valued ([b], (none : Option V)) = none from rfl]
      simp only
      rw [filterMap_pre, filterMap_blockEnts L (c :: x), List.map_map]
      congr 1

theorem valsOf_node (v : Option V) (kids : List (Path × PTree V)) :
    valsOf (node v kids) =
      (match v with | some x => [([], x)] | none => []) ++
        kids.flatMap (fun k => (valsOf k.2).map (preV k.1)) := by
  have hk : ∀ ks : List (Path × PTree V), (entsKids ks).filterMap valued =
      ks.flatMap (fun k => (valsOf k.2).map (preV k.1)) := by
    intro ks
    induction ks with
    | nil => simp [entsKids]
    | cons k ks ih =>
      obtain ⟨e, c⟩ := k
      rw [entsKids, List.filterMap_append, filterMap_blockEnts, ih]
      simp [valsOf]
  unfold valsOf
  rw [ents, List.filterMap_cons, hk kids]
  cases v <;> simp [valued, valsOf]



theorem foldl_acc {α β γ δ : Type} (f : List α × List β × γ → δ → List α × List β × γ) (g : δ → List α) :
    ∀ (ks : List δ), (∀ k ∈ ks, ∀ acc, (f acc k).1 = acc.1 ++ g k ∧ (f acc k).2.1 = acc.2.1) →
      ∀ acc, (ks.foldl f acc).1 = acc.1 ++ ks.flatMap g ∧ (ks.foldl f acc).2.1 = acc.2.1
  | [], _, acc => by simp
  | k :: ks, h, acc => by
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := foldl_acc f g ks (fun k hk => h k (List.mem_cons_of_mem _ hk)) (f acc k)
      obtain ⟨h3, h4⟩ := h k (List.mem_cons_self ..) acc
      rw [h1, h2, h3, h4]; simp

theorem anaGo_unfold : ∀ (t : PTree V) (n : Nat) (path : Path), t.height ≤ n →
    (anaGo PTree.unfold n t path).1 = t.valsOf.map (preV path) ∧
      (anaGo PTree.unfold n t path).2.1 = [] := by
  refine PTree.ind (fun v kids ih => ?_)
  intro n path hn
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := PathMap.height_pos (node v kids); omega⟩
  rw [anaGo]
  simp only [PTree.unfold, val, PTree.kids]
  rw [List.foldl_map]
  have key := foldl_acc (β := Path) (γ := List (Path × List UInt8)) (g := fun k : Path × PTree V => (valsOf k.2).map (preV (path ++ k.1)))
  have hyp : ∀ k ∈ kids, ∀ (acc : List (Path × V) × List Path × List (Path × List UInt8)),
      (acc.1 ++ (anaGo PTree.unfold n k.2 (path ++ k.1)).1 = acc.1 ++ (valsOf k.2).map (preV (path ++ k.1))) ∧
      (acc.2.1 ++ (anaGo PTree.unfold n k.2 (path ++ k.1)).2.1 = acc.2.1) := by
    intro k hk acc
    obtain ⟨h1, h2⟩ := ih k.1 k.2 hk n (path ++ k.1)
      (by have := height_kid (v := v) hk; omega)
    rw [h1, h2]; simp
  constructor
  · rw [(key _ kids (fun k hk acc => hyp k hk acc) _).1, valsOf_node]
    have hp : ∀ e : Path, (preV e : Path × V → Path × V) = fun pv => (e ++ pv.1, pv.2) := fun _ => rfl
    cases v <;> simp [hp, List.map_flatMap, List.map_map, Function.comp_def]
  · rw [(key _ kids (fun k hk acc => hyp k hk acc) _).2]

/-- **(d).**  The anamorphism that pushes every edge of a tree (`push_byte` for a
one-byte edge, `push` for a longer one: the model does not tell them apart)
builds exactly the tree's values and their prefixes.  So it is `flatten t`
minus the dangling locations, which no push can create (see `NoDangling`). -/
theorem ana_unfold (t : PTree V) (n : Nat) (h : t.height ≤ n) :
    (ana PTree.unfold t n).1 = PathMap.mk' t.valsOf [] := by
  unfold ana
  obtain ⟨h1, h2⟩ := anaGo_unfold t n [] h
  rcases hg : anaGo PTree.unfold n t [] with ⟨vs, ps, cs⟩
  rw [hg] at h1 h2
  simp only at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  conv => rhs; rw [← List.map_id t.valsOf]
  congr 1

end PTree
/-! ## (c): every catamorphism flavour builds the same tree -/
namespace PathMap
open PTree
variable {V : Type}

theorem foldl_fst {α β γ δ : Type} (F : List α × β × γ → δ → List α × β × γ) (g : δ → α) :
    ∀ (bs : List δ), (∀ b ∈ bs, ∀ acc, (F acc b).1 = acc.1 ++ [g b]) →
      ∀ acc, (bs.foldl F acc).1 = acc.1 ++ bs.map g
  | [], _, acc => by simp
  | b :: bs, h, acc => by
      rw [List.foldl_cons, foldl_fst F g bs (fun b hb => h b (List.mem_cons_of_mem _ hb)),
        h b (List.mem_cons_self ..)]
      simp

section
variable {W E : Type}

/-- The side-effecting stepping fold, whose closure ignores the call number,
the path and the `Err`, returns the cached fold's result. -/
theorem sideCata_fst (T : PathMap V) (alg : Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    ∀ (n : Nat) (q : Path) (i : Nat),
      (T.sideCata (fun _ _ _ v m ws => alg v m ws) err d n q i).1 = T.cata alg d n q
  | 0, _, _ => rfl
  | n + 1, q, i => by
      rw [sideCata, cata_succ]
      simp only
      rw [foldl_fst _ (fun b => T.cata alg d n (q ++ [b])) _ (fun b _ acc => by
        simp only
        rw [← sideCata_fst T alg err d n (q ++ [b]) acc.2.1])]
      simp

/-- The same for jumping folds: the closure reads its jumped bytes off the end
of its path, as op 58's does (`path[path.len() - jump..]`). -/
theorem sideJ_fst (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    ∀ (n : Nat) (q : Path) (jump i : Nat),
      (T.sideJ (fun _ q j v m ws => alg (q.drop (q.length - j.getD 0)) v m ws) err d n q jump i).1 =
        T.cataJ alg d n q (q.drop (q.length - jump))
  | 0, _, _, _ => rfl
  | n + 1, q, jump, i => by
      rw [sideJ, cataJ_succ]
      simp only [Option.getD_some]
      rw [foldl_fst _ (fun b => T.cataJ alg d n (T.follow T.fuel (q ++ [b]))
          ((T.follow T.fuel (q ++ [b])).drop (q.length + 1))) _ (fun b _ acc => by
        simp only
        rw [sideJ_fst T alg err d n]
        obtain ⟨x, hx⟩ := follow_shape T T.fuel (q ++ [b])
        rw [hx]
        have : (q ++ [b] ++ x).length - ((q ++ [b] ++ x).length - q.length - 1) = q.length + 1 := by
          simp; omega
        rw [this])]
      simp

/-- **(c), side-effecting flavours.**  With a closure that ignores the call
number, `into_cata_side_effect` (and a `_fallible` run that succeeds) returns
what `into_cata_cached` does: `cataStep`. -/
theorem sideFold_step (T : PathMap V) (alg : Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    (T.sideFold false (fun _ _ _ v m ws => alg v m ws) err d).1 = T.cataStep alg d :=
  sideCata_fst T alg err d _ _ _

/-- …and `into_cata_jumping_side_effect` what `into_cata_jumping_cached` does. -/
theorem sideFold_jump (T : PathMap V) (alg : Path → Option V → ByteMask → List W → W)
    (err : Nat → Path → Option Nat → Option V → ByteMask → E) (d : W) :
    (T.sideFold true (fun _ q j v m ws => alg (q.drop (q.length - j.getD 0)) v m ws) err d).1 =
      T.cataJump alg d := by
  unfold sideFold cataJump
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  split
  · rw [sideJ_fst]; rfl
  · rw [sideJ_fst]; simp

end

/-- **(c)** for the trees: every flavour serializes to `toBytes` / `toLines`.
(The cached flavours are `cataStep` / `cataJump` by definition.) -/
theorem side_toBytes (T : PathMap V) {E : Type} (err : Nat → Path → Option Nat → Option V → ByteMask → E) :
    (T.sideFold false (fun _ _ _ v m ws => algB v m ws) err (.node none [])).1 = T.toBytes :=
  sideFold_step T algB err _

theorem side_toLines (T : PathMap V) {E : Type} (err : Nat → Path → Option Nat → Option V → ByteMask → E) :
    rootLine (T.sideFold true (fun _ q j v m ws => algL (q.drop (q.length - j.getD 0)) v m ws) err
      ([], .node none [])).1 = T.toLines := by
  rw [sideFold_jump]; rfl

end PathMap
end PathMapModel
