import PrunedModel.Zippy

/-! Convex algebra extends the existing canonical pruned model. Ordinary set
operations are Zippy's zipper programs; only the additional geometry is new. -/
namespace PrunedModel
open PathMapModel

abbrev PathSpace := Zippy.Space

namespace Convex
attribute [simp] Zippy.not_mem_empty

/-- Finite set literals use the pruned model's canonical constructor. -/
def ofPaths (ps : List Path) : PathSpace := PrunedMap.mk' (ps.map (·, ()))
instance : Coe (List Path) PathSpace := ⟨ofPaths⟩
instance : Append PathSpace := ⟨Zippy.union⟩

@[simp] theorem mem_ofPaths (ps : List Path) (p : Path) : p ∈ ofPaths ps ↔ p ∈ ps := by
  change ((PrunedMap.mk' _).valAt p).isSome = true ↔ _
  rw [PrunedMap.valAt, PrunedMap.mk', lookup_normVals]
  constructor
  · intro h
    have := mem_keys_of_lookup_isSome h
    simpa using this
  · intro h
    apply lookup_isSome_of_mem_keys
    simpa using h

@[simp] theorem mem_keys (a : PathSpace) (p : Path) : p ∈ a.keys ↔ p ∈ a := Zippy.mem_keys

@[simp] theorem ofPaths_keys (a : PathSpace) : ofPaths a.keys = a := by
  apply Zippy.ext; intro p; simp

abbrev union := Zippy.union
abbrev inter := Zippy.inter
abbrev diff := Zippy.subtr
abbrev product := Zippy.composition
abbrev wrap := Zippy.wrap
abbrev unwrap := Zippy.unwrap
abbrev restrict := Zippy.restriction
abbrev raffinate := Zippy.raffination
abbrev head := Zippy.head
abbrev tails := Zippy.tailsUnion

def subset (a b : PathSpace) : Bool := a.keys.all (fun p => decide (p ∈ b))
def equiv (a b : PathSpace) : Bool := decide (a = b)
def symDiff (a b : PathSpace) : PathSpace := union (diff a b) (diff b a)

@[simp] theorem mem_union (a b : PathSpace) (p : Path) :
    p ∈ union a b ↔ p ∈ a ∨ p ∈ b := Zippy.mem_union
theorem mem_union_left (b : PathSpace) {a : PathSpace} {p : Path} (h : p ∈ a) : p ∈ union a b :=
  (mem_union a b p).mpr (Or.inl h)
theorem mem_union_right (a : PathSpace) {b : PathSpace} {p : Path} (h : p ∈ b) : p ∈ union a b :=
  (mem_union a b p).mpr (Or.inr h)

@[simp] theorem mem_inter (a b : PathSpace) (p : Path) :
    p ∈ inter a b ↔ p ∈ a ∧ p ∈ b := Zippy.mem_inter
@[simp] theorem mem_diff (a b : PathSpace) (p : Path) :
    p ∈ diff a b ↔ p ∈ a ∧ p ∉ b := Zippy.mem_subtr
@[simp] theorem mem_append (a b : PathSpace) (p : Path) :
    p ∈ a ++ b ↔ p ∈ a ∨ p ∈ b := Zippy.mem_union

theorem eq_empty_iff (a : PathSpace) : a = ofPaths [] ↔ ∀ p, p ∉ a := by
  constructor
  · rintro rfl; simp
  · intro h; apply Zippy.ext; intro p; simp [h p]

theorem ne_empty_iff (a : PathSpace) : a ≠ ofPaths [] ↔ ∃ p, p ∈ a := by
  classical
  rw [ne_eq, eq_empty_iff]
  grind

theorem ofPaths_nil : ofPaths [] = Zippy.empty := by
  apply Zippy.ext; intro p; simp [Zippy.not_mem_empty]

@[simp] theorem append_eq_union (a b : PathSpace) : a ++ b = union a b := rfl

theorem ofPaths_cons (p : Path) (ps : List Path) :
    ofPaths (p :: ps) = union [p] (ofPaths ps) := by
  apply Zippy.ext; intro q; simp

@[simp] theorem keys_eq_nil_iff (a : PathSpace) : a.keys = [] ↔ a = ofPaths [] := by
  rw [List.eq_nil_iff_forall_not_mem, eq_empty_iff]
  simp

theorem keys_nodup (a : PathSpace) : a.keys.Nodup := by
  have go : ∀ xs : List (Path × Unit), DistinctKeys xs → (xs.map Prod.fst).Nodup := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rintro ⟨hx, hxs⟩
      exact List.nodup_cons.mpr ⟨hx, ih hxs⟩
  exact go a.entries (distinctKeys_of_sortedKeys a.sorted)

/-- Induction through the canonical map's finite key enumeration. -/
@[elab_as_elim] theorem space_induction {motive : PathSpace → Prop} (a : PathSpace)
    (nil : motive (ofPaths [])) (cons : ∀ (p : Path) a, motive a → motive (union [p] a)) : motive a := by
  rw [← ofPaths_keys a]
  generalize a.keys = ps
  induction ps with
  | nil => exact nil
  | cons p ps ih => rw [ofPaths_cons]; exact cons p _ ih

end Convex
end PrunedModel
