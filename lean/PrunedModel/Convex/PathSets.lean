import PrunedModel.Convex.Space
import PrunedModel.Convex.Path

/-! Additional finite-space geometry on `PrunedMap Unit`. Ordinary set
operations are imported from Zippy, so all laws concern the same canonical
model as the existing zipper algebra. -/
namespace PrunedModel.Convex
open PathMapModel

def retain (p a : PathSpace) : PathSpace :=
  ofPaths (p.keys.filter fun x => a.keys.any (x ≼ ·))
def divergence (a b : PathSpace) : PathSpace :=
  ofPaths (a.keys.flatMap fun p => b.keys.filterMap (Path.divergence p))
/-- Fold pairs whose second prefix properly extends the first. -/
def properOverlap (a b : PathSpace) (f : Path → Path → PathSpace) : PathSpace :=
  ofPaths (a.keys.flatMap fun u => b.keys.flatMap fun v => match Path.stripPrefix u v with
    | some r@(_ :: _) => (f u r).keys
    | _ => [])
def branches (a : PathSpace) : PathSpace := divergence a a
/-- Prefix-minimal members. -/
def basis (a : PathSpace) : PathSpace :=
  ofPaths (a.keys.filter fun p => !(a.keys.any fun q => q != p && q ≼ p))
/-- Prefix-maximal members. -/
def hull (a : PathSpace) : PathSpace :=
  ofPaths (a.keys.filter fun p => !(a.keys.any fun q => q != p && p ≼ q))
def interior (a : PathSpace) : PathSpace := diff a (hull a)
def completion (a : PathSpace) : PathSpace := union a (branches a)
def lcpProduct (a b : PathSpace) : PathSpace :=
  ofPaths (a.keys.flatMap fun p => b.keys.map (Path.lcp p))
def power (a : PathSpace) : Nat → PathSpace
  | 0 => ofPaths [[]]
  | n + 1 => product a (power a n)
def branchIter (a : PathSpace) : Nat → PathSpace
  | 0 => a
  | n + 1 => branches (branchIter a n)
/-- The canonical model already has distinct keys. -/
def count (a : PathSpace) : Nat := a.keys.length
def height (a : PathSpace) : Nat := (a.keys.map List.length).foldl max 0
def commonPrefix (a : PathSpace) : Path := match a.keys with
  | [] => []
  | p :: ps => ps.foldl Path.lcp p
def prefixFree (a : PathSpace) : Bool := equiv a (basis a)
def covers (a b : PathSpace) : Bool := a.keys.all fun p => b.keys.any (p ≼ ·)

/-- Union a family, using the existing finite key enumeration. -/
def bind (a : PathSpace) (f : Path → PathSpace) : PathSpace :=
  ofPaths (a.keys.flatMap fun p => (f p).keys)
@[simp] theorem mem_bind (a : PathSpace) (f : Path → PathSpace) (p : Path) :
    p ∈ bind a f ↔ ∃ q ∈ a, p ∈ f q := by simp [bind, List.mem_flatMap]

/-- Independent head-recursive definitions, fueled by maximum length + 1. -/
def divergenceRec : Nat → PathSpace → PathSpace → PathSpace
  | 0, _, _ => ofPaths []
  | n + 1, a, b =>
    let ha := head a
    let hb := head b
    let root := if ha.keys.any (fun x => hb.keys.any (· != x)) then ofPaths [[]] else ofPaths []
    union root (bind (inter ha hb) fun p => wrap p (divergenceRec n (unwrap a p) (unwrap b p)))
def basisRec : Nat → PathSpace → PathSpace
  | 0, _ => ofPaths []
  | n + 1, a => if ([] : Path) ∈ a then ofPaths [[]] else
    bind (head a) fun p => wrap p (basisRec n (unwrap a p))
def hullRec : Nat → PathSpace → PathSpace
  | 0, _ => ofPaths []
  | n + 1, a =>
    let root := if ([] : Path) ∈ a ∧ head a = ofPaths [] then ofPaths [[]] else ofPaths []
    union root (bind (head a) fun p => wrap p (hullRec n (unwrap a p)))
def retainRec : Nat → PathSpace → PathSpace → PathSpace
  | 0, _, _ => ofPaths []
  | n + 1, p, a =>
    let root := if ([] : Path) ∈ p ∧ a ≠ ofPaths [] then ofPaths [[]] else ofPaths []
    union root (bind (inter (head p) (head a)) fun q =>
      wrap q (retainRec n (unwrap p q) (unwrap a q)))

def ofMap {V : Type} (t : PrunedMap V) : PathSpace := ofPaths t.keys

/-- General witness theorem, not a bounded check. -/
theorem mem_divergence (a b : PathSpace) (p : Path) :
    p ∈ divergence a b ↔ ∃ x ∈ a, ∃ y ∈ b, Path.divergence x y = some p := by
  simp [divergence, List.mem_flatMap, List.mem_filterMap]

theorem divergence_comm (a b : PathSpace) (p : Path) :
    p ∈ divergence a b ↔ p ∈ divergence b a := by
  simp only [mem_divergence]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, (Path.divergence_comm y x).trans h⟩
  · rintro ⟨y, hy, x, hx, h⟩
    exact ⟨x, hx, y, hy, (Path.divergence_comm x y).trans h⟩

@[simp] theorem divergence_empty_left (a : PathSpace) : divergence (ofPaths []) a = ofPaths [] := by
  apply Zippy.ext; intro p; simp [mem_divergence]
@[simp] theorem divergence_empty_right (a : PathSpace) : divergence a (ofPaths []) = ofPaths [] := by
  apply Zippy.ext; intro p; simp [mem_divergence]
@[simp] theorem divergence_epsilon_left (a : PathSpace) : divergence (ofPaths [[]]) a = ofPaths [] := by
  apply Zippy.ext; intro p; simp [mem_divergence]
@[simp] theorem divergence_epsilon_right (a : PathSpace) : divergence a (ofPaths [[]]) = ofPaths [] := by
  apply Zippy.ext; intro p; simp [mem_divergence]

theorem divergence_union_left (a b c : PathSpace) :
    divergence (union a b) c = union (divergence a c) (divergence b c) := by
  apply Zippy.ext; intro p; simp only [mem_divergence, mem_union]; grind

theorem divergence_union_right (a b c : PathSpace) (p : Path) :
    p ∈ divergence a (union b c) ↔ p ∈ union (divergence a b) (divergence a c) := by
  simp only [mem_union, mem_divergence]; grind

theorem divergence_diagonal (a : PathSpace) : divergence a a = branches a := rfl

theorem divergence_mono {a b c d : PathSpace}
    (ha : ∀ p, p ∈ a → p ∈ c) (hb : ∀ p, p ∈ b → p ∈ d) :
    ∀ p, p ∈ divergence a b → p ∈ divergence c d := by
  intro p hp
  obtain ⟨x, hx, y, hy, h⟩ := (mem_divergence a b p).mp hp
  exact (mem_divergence c d p).mpr ⟨x, ha x hx, y, hb y hy, h⟩

theorem mem_basis (a : PathSpace) (p : Path) :
    p ∈ basis a ↔ p ∈ a ∧ ∀ q ∈ a, q ≠ p → (q ≼ p) = false := by
  simp [basis, List.mem_filter, Bool.not_eq_true, List.any_eq_false]

theorem mem_hull (a : PathSpace) (p : Path) :
    p ∈ hull a ↔ p ∈ a ∧ ∀ q ∈ a, q ≠ p → (p ≼ q) = false := by
  simp [hull, List.mem_filter, Bool.not_eq_true, List.any_eq_false]
end PrunedModel.Convex
