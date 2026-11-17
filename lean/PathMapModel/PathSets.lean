import PathMapModel.Map

/-! Valued finite path sets. This independent list model deliberately differs
from the Rust zipper traversal. Lists denote sets: order/duplicates are ignored
by `equiv`. Bare structure is not membership. Basis/hull preserve payloads. -/
namespace PathMapModel
namespace Path

def lcp : Path → Path → Path
  | a :: as, b :: bs => if a == b then a :: lcp as bs else []
  | _, _ => []

/-- Termination is not a next byte. -/
def divergence : Path → Path → Option Path
  | a :: as, b :: bs => if a == b then (divergence as bs).map (a :: ·) else some []
  | _, _ => none

@[simp] theorem divergence_self (p : Path) : divergence p p = none := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [divergence, ih]

theorem divergence_comm (p q : Path) : divergence p q = divergence q p := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b; simp [divergence, ih]
      · simp [divergence, h, Ne.symm h]

@[simp] theorem divergence_nil_left (p : Path) : divergence [] p = none := by cases p <;> rfl
@[simp] theorem divergence_nil_right (p : Path) : divergence p [] = none := by cases p <;> rfl

theorem divergence_wrap (p a b : Path) :
    divergence (p ++ a) (p ++ b) = (divergence a b).map (p ++ ·) := by
  induction p with
  | nil => simp
  | cons c cs ih => simp [divergence, ih, Option.map_map, Function.comp_def]
end Path

abbrev PathSpace := List Path
namespace PathSpace

def normalize (a : PathSpace) : PathSpace := Path.sortDedup a
def subset (a b : PathSpace) : Bool := a.all b.contains
/-- Set equality is independent of enumeration and serialization order. -/
def equiv (a b : PathSpace) : Bool := subset a b && subset b a
def union (a b : PathSpace) : PathSpace := a ++ b
def inter (a b : PathSpace) : PathSpace := a.filter b.contains
def diff (a b : PathSpace) : PathSpace := a.filter (!b.contains ·)
def symDiff (a b : PathSpace) : PathSpace := union (diff a b) (diff b a)
def product (a b : PathSpace) : PathSpace := a.flatMap fun p => b.map (p ++ ·)
def wrap (p : Path) (a : PathSpace) : PathSpace := a.map (p ++ ·)
def unwrap (a : PathSpace) (p : Path) : PathSpace := a.filterMap (Path.stripPrefix p)
def restrict (a p : PathSpace) : PathSpace := a.filter fun x => p.any (· ≼ x)
def raffinate (a p : PathSpace) : PathSpace := diff a (restrict a p)
def live (p a : PathSpace) : PathSpace := p.filter fun x => a.any (x ≼ ·)
def head (a : PathSpace) : PathSpace := a.filterMap fun p => p.head?.map (fun b => [b])
def tails (a : PathSpace) : PathSpace := a.filterMap fun p => match p with
  | [] => none
  | _ :: ps => some ps

def divergence (a b : PathSpace) : PathSpace := a.flatMap fun p => b.filterMap (Path.divergence p)
/-- Fold pairs whose second prefix properly extends the first. -/
def properOverlap (a b : PathSpace) (f : Path → Path → PathSpace) : PathSpace :=
  a.flatMap fun u => b.flatMap fun v => match Path.stripPrefix u v with
    | some r@(_ :: _) => f u r
    | _ => []

def branches (a : PathSpace) : PathSpace := divergence a a
/-- Prefix-minimal members. -/
def basis (a : PathSpace) : PathSpace := a.filter fun p => !(a.any fun q => q != p && q ≼ p)
/-- Prefix-maximal members. -/
def hull (a : PathSpace) : PathSpace := a.filter fun p => !(a.any fun q => q != p && p ≼ q)
def interior (a : PathSpace) : PathSpace := diff a (hull a)
def completion (a : PathSpace) : PathSpace := union a (branches a)
def lcpProduct (a b : PathSpace) : PathSpace := a.flatMap fun p => b.map (Path.lcp p)
def power (a : PathSpace) : Nat → PathSpace
  | 0 => [[]]
  | n + 1 => product a (power a n)
def branchIter (a : PathSpace) : Nat → PathSpace
  | 0 => a
  | n + 1 => branches (branchIter a n)
/-- Cardinality counts distinct members, independently of their lexical order. -/
def count (a : PathSpace) : Nat := a.eraseDups.length
def height (a : PathSpace) : Nat := (a.map List.length).foldl max 0
def commonPrefix (a : PathSpace) : Path := match a with
  | [] => []
  | p :: ps => ps.foldl Path.lcp p
def prefixFree (a : PathSpace) : Bool := equiv a (basis a)
def covers (a b : PathSpace) : Bool := a.all fun p => b.any (p ≼ ·)

/-- Independent head-recursive definitions, fueled by maximum length + 1. -/
def divergenceRec : Nat → PathSpace → PathSpace → PathSpace
  | 0, _, _ => []
  | n + 1, a, b =>
    let ha := normalize (head a)
    let hb := normalize (head b)
    let root := if ha.any (fun x => hb.any (· != x)) then [[]] else []
    root ++ (inter ha hb).flatMap fun p => wrap p (divergenceRec n (unwrap a p) (unwrap b p))
def basisRec : Nat → PathSpace → PathSpace
  | 0, _ => []
  | n + 1, a => if a.contains [] then [[]] else
    (normalize (head a)).flatMap fun p => wrap p (basisRec n (unwrap a p))
def hullRec : Nat → PathSpace → PathSpace
  | 0, _ => []
  | n + 1, a =>
    let root := if a.contains [] && (head a).isEmpty then [[]] else []
    root ++ (normalize (head a)).flatMap fun p => wrap p (hullRec n (unwrap a p))
def liveRec : Nat → PathSpace → PathSpace → PathSpace
  | 0, _, _ => []
  | n + 1, p, a =>
    let root := if p.contains [] && !a.isEmpty then [[]] else []
    root ++ (normalize (inter (head p) (head a))).flatMap fun q =>
      wrap q (liveRec n (unwrap p q) (unwrap a q))

def ofMap {V : Type} (t : PathMap V) : PathSpace := t.vals.map (·.1)

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

@[simp] theorem divergence_empty_left (a : PathSpace) : divergence [] a = [] := rfl
@[simp] theorem divergence_empty_right (a : PathSpace) : divergence a [] = [] := by simp [divergence]
@[simp] theorem divergence_epsilon_left (a : PathSpace) : divergence [[]] a = [] := by simp [divergence]
@[simp] theorem divergence_epsilon_right (a : PathSpace) : divergence a [[]] = [] := by simp [divergence]

theorem divergence_union_left (a b c : PathSpace) :
    divergence (union a b) c = union (divergence a c) (divergence b c) := by
  simp [divergence, union]

theorem divergence_union_right (a b c : PathSpace) (p : Path) :
    p ∈ divergence a (union b c) ↔ p ∈ union (divergence a b) (divergence a c) := by
  simp only [union, List.mem_append, mem_divergence]
  constructor
  · rintro ⟨x, hx, y, hy | hy, h⟩
    · exact Or.inl ⟨x, hx, y, hy, h⟩
    · exact Or.inr ⟨x, hx, y, hy, h⟩
  · rintro (⟨x, hx, y, hy, h⟩ | ⟨x, hx, y, hy, h⟩)
    · exact ⟨x, hx, y, Or.inl hy, h⟩
    · exact ⟨x, hx, y, Or.inr hy, h⟩

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
end PathSpace

namespace Map

def basis {V : Type} (t : PathMap V) : PathMap V :=
  let support := PathSpace.basis (PathSpace.ofMap t)
  PathMap.mk' (t.vals.filter (fun kv => support.contains kv.1)) []
def hull {V : Type} (t : PathMap V) : PathMap V :=
  let support := PathSpace.hull (PathSpace.ofMap t)
  PathMap.mk' (t.vals.filter (fun kv => support.contains kv.1)) []
def divergence {V W : Type} (a : PathMap V) (b : PathMap W) : PathMap Unit :=
  PathMap.mk' ((PathSpace.divergence (PathSpace.ofMap a) (PathSpace.ofMap b)).map (·, ())) []
def branches {V : Type} (a : PathMap V) : PathMap Unit := divergence a a
end Map

namespace Zip
/-- Relative focus semantics; input and output cursor positions are unchanged. -/
def basis {V : Type} (src out : Zip V) : Zip V := out.graftMap (Map.basis src.makeMap)
def hull {V : Type} (src out : Zip V) : Zip V := out.graftMap (Map.hull src.makeMap)
def divergence {V W : Type} (a : Zip V) (b : Zip W) (out : Zip Unit) : Zip Unit :=
  out.graftMap (Map.divergence a.makeMap b.makeMap)
def branches {V : Type} (src : Zip V) (out : Zip Unit) : Zip Unit :=
  out.graftMap (Map.branches src.makeMap)
end Zip
end PathMapModel
