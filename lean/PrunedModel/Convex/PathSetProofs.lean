import PrunedModel.Convex.PathSets

/-! Universally quantified proofs, separate from the executable law battery. -/
namespace PrunedModel.Convex
open PathMapModel

theorem basis_subset (a : PathSpace) {p : Path} (h : p ∈ basis a) : p ∈ a :=
  ((mem_basis a p).mp h).1

theorem hull_subset (a : PathSpace) {p : Path} (h : p ∈ hull a) : p ∈ a :=
  ((mem_hull a p).mp h).1

theorem basis_idempotent (a : PathSpace) (p : Path) :
    p ∈ basis (basis a) ↔ p ∈ basis a := by
  constructor
  · exact basis_subset (basis a)
  · intro hp
    apply (mem_basis (basis a) p).mpr
    exact ⟨hp, fun q hq hne => ((mem_basis a p).mp hp).2 q (basis_subset a hq) hne⟩

theorem hull_idempotent (a : PathSpace) (p : Path) :
    p ∈ hull (hull a) ↔ p ∈ hull a := by
  constructor
  · exact hull_subset (hull a)
  · intro hp
    apply (mem_hull (hull a) p).mpr
    exact ⟨hp, fun q hq hne => ((mem_hull a p).mp hp).2 q (hull_subset a hq) hne⟩

theorem basis_antichain {a : PathSpace} {p q : Path}
    (hp : p ∈ basis a) (hq : q ∈ basis a) (hne : p ≠ q) : (p ≼ q) = false :=
  ((mem_basis a q).mp hq).2 p (basis_subset a hp) hne

theorem hull_antichain {a : PathSpace} {p q : Path}
    (hp : p ∈ hull a) (hq : q ∈ hull a) (hne : p ≠ q) : (p ≼ q) = false :=
  ((mem_hull a p).mp hp).2 q (hull_subset a hq) (Ne.symm hne)

theorem divergence_intersection_bound {a b c : PathSpace} {p : Path}
    (h : p ∈ divergence (inter a b) c) :
    p ∈ divergence a c ∧ p ∈ divergence b c := by
  obtain ⟨x, hx, y, hy, hd⟩ := (mem_divergence _ _ _).mp h
  obtain ⟨ha, hb⟩ := (mem_inter _ _ _).mp hx
  exact ⟨(mem_divergence _ _ _).mpr ⟨x, ha, y, hy, hd⟩,
    (mem_divergence _ _ _).mpr ⟨x, hb, y, hy, hd⟩⟩

theorem divergence_difference_upper {a b c : PathSpace} {p : Path}
    (h : p ∈ divergence (diff a b) c) : p ∈ divergence a c := by
  apply divergence_mono (b := c) (d := c) (fun x hx => ((mem_diff a b x).mp hx).1)
    (fun _ hx => hx) p h

theorem divergence_difference_lower {a b c : PathSpace} {p : Path}
    (h : p ∈ divergence a c) (hn : p ∉ divergence b c) :
    p ∈ divergence (diff a b) c := by
  obtain ⟨x, hx, y, hy, hd⟩ := (mem_divergence _ _ _).mp h
  have nx : x ∉ b := fun hb => hn ((mem_divergence _ _ _).mpr ⟨x, hb, y, hy, hd⟩)
  exact (mem_divergence _ _ _).mpr ⟨x, (mem_diff _ _ _).mpr ⟨hx, nx⟩, y, hy, hd⟩

theorem branches_union (a b : PathSpace) (p : Path) :
    p ∈ branches (union a b) ↔ p ∈ branches a ∨ p ∈ branches b ∨ p ∈ divergence a b := by
  change p ∈ divergence (union a b) (union a b) ↔ _
  rw [divergence_union_left]
  simp only [mem_union]
  have ha := divergence_union_right a a b p
  have hb := divergence_union_right b a b p
  simp only [mem_union] at ha hb
  have hc := divergence_comm b a p
  dsimp [branches]
  grind

/-- Singletons recover strict pair divergence from Br. -/
theorem singleton_polarization (a b : Path) (p : Path) :
    p ∈ divergence [a] [b] ↔ p ∈ branches [a,b] := by
  simp [branches, mem_divergence, Path.divergence_comm b a]

/-- A symmetric bilinear operation with this diagonal is uniquely determined.
The empty laws are listed explicitly, as in the executable catalog. -/
theorem divergence_unique
    (f : PathSpace → PathSpace → Path → Prop)
    (he : ∀ a p, ¬ f (ofPaths []) a p ∧ ¬ f a (ofPaths []) p)
    (hs : ∀ a b p, f a b p ↔ f b a p)
    (hl : ∀ a b c p, f (a ++ b) c p ↔ f a c p ∨ f b c p)
    (hr : ∀ a b c p, f a (b ++ c) p ↔ f a b p ∨ f a c p)
    (hd : ∀ a p, f a a p ↔ p ∈ branches a) :
    ∀ a b p, f a b p ↔ p ∈ divergence a b := by
  have hsingle : ∀ x y p, f [x] [y] p ↔ p ∈ divergence (ofPaths [x]) (ofPaths [y]) := by
    intro x y p
    have hxx : ¬ f [x] [x] p := by simpa [branches, mem_divergence] using (hd [x] p)
    have hyy : ¬ f [y] [y] p := by simpa [branches, mem_divergence] using (hd [y] p)
    have hh := hd ([x] ++ [y]) p
    rw [hl, hr, hr] at hh
    have hxy := hs [y] [x] p
    have hp := singleton_polarization x y p
    rw [ofPaths_cons x [y]] at hp
    simp only [append_eq_union] at hh
    grind
  intro a b p
  induction a using space_induction generalizing b with
  | nil => simp [he]
  | cons x xs ih =>
    have hxb : f [x] b p ↔ p ∈ divergence [x] b := by
      induction b using space_induction with
      | nil => simp [he]
      | cons y ys ihb =>
        change f [x] ([y] ++ ys) p ↔ _
        rw [hr, hsingle, ihb]
        simpa [union] using (divergence_union_right [x] [y] ys p).symm
    change f ([x] ++ xs) b p ↔ _
    rw [hl, hxb, ih]
    rw [divergence_union_left]; simp only [mem_union]
/-- Empty annihilation follows from the other three characterizing laws. -/
theorem divergence_unique_three
    (f : PathSpace → PathSpace → Path → Prop)
    (hs : ∀ a b p, f a b p ↔ f b a p)
    (hl : ∀ a b c p, f (a ++ b) c p ↔ f a c p ∨ f b c p)
    (hr : ∀ a b c p, f a (b ++ c) p ↔ f a b p ∨ f a c p)
    (hd : ∀ a p, f a a p ↔ p ∈ branches a) :
    ∀ a b p, f a b p ↔ p ∈ divergence a b := by
  have hempty : ∀ a p, ¬ f (ofPaths []) a p := by
    intro a p
    induction a using space_induction with
    | nil => simpa [branches, mem_divergence] using hd (ofPaths []) p
    | cons x xs ih =>
      have hself : ¬ f [x] [x] p := by simpa [branches, mem_divergence] using hd [x] p
      have hx : ¬ f (ofPaths []) [x] p := fun h => hself (by
        simpa only [append_eq_union, ofPaths_nil, Zippy.empty_union] using
          ((hl (ofPaths []) [x] [x] p).mpr (Or.inl h)))
      change ¬ f (ofPaths []) ([x] ++ xs) p
      rw [hr]
      exact fun h => h.elim hx ih
  exact divergence_unique f (fun a p => ⟨hempty a p, fun h => hempty a p ((hs a (ofPaths []) p).mp h)⟩)
    hs hl hr hd

theorem divergence_no_unit (u : PathSpace) : divergence (ofPaths [[]]) u ≠ (ofPaths [[]]) := by
  intro h
  have he : ([] : Path) ∈ divergence (ofPaths [[]]) u := h.symm ▸ (by simp)
  simp at he

theorem divergence_not_associative :
    ¬ ∀ a b c : PathSpace, equiv (divergence (divergence a b) c)
      (divergence a (divergence b c)) = true := by
  intro h
  have bad := h (ofPaths [[0,0]]) (ofPaths [[0,1]]) (ofPaths [[1]])
  exact (by decide : equiv (divergence (divergence (ofPaths [[0,0]]) (ofPaths [[0,1]])) (ofPaths [[1]]))
    (divergence (ofPaths [[0,0]]) (divergence (ofPaths [[0,1]]) (ofPaths [[1]]))) ≠ true) bad

end PrunedModel.Convex

namespace PathMapModel.Path

/-- A successful pair divergence is a prefix of each input, even if no input
stores that interior prefix as a value. -/
theorem divergence_prefix_left {a b p : Path} (h : divergence a b = some p) :
    (p ≼ a) = true := by
  induction a generalizing b p with
  | nil => simp [divergence] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [divergence] at h
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        simp only [divergence, beq_self_eq_true, if_true, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        simp [isPrefixOf, ih hq]
      · simp [divergence, hxy] at h
        subst p
        simp [isPrefixOf]

/-- Extending a divergent witness preserves the same divergence. -/
theorem divergence_extend_left {a b p : Path} (tail : Path) (h : divergence a b = some p) :
    divergence (a ++ tail) b = some p := by
  induction a generalizing b p with
  | nil => simp [divergence] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [divergence] at h
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        simp only [divergence, beq_self_eq_true, if_true, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        simp [divergence, ih hq]
      · simp [divergence, hxy] at h ⊢
        exact h

theorem prefix_iff_extension (p q : Path) :
    (p ≼ q) = true ↔ ∃ r, q = p ++ r := PrunedModel.Path.isPrefixOf_iff p q
end PathMapModel.Path

namespace PrunedModel.Convex
open PathMapModel

theorem divergence_covered_mono {a b c : PathSpace}
    (hc : ∀ x ∈ a, ∃ y ∈ b, (x ≼ y) = true) :
    ∀ p, p ∈ divergence a c → p ∈ divergence b c := by
  intro p hp
  obtain ⟨x, hx, z, hz, hd⟩ := (mem_divergence _ _ _).mp hp
  obtain ⟨y, hy, hxy⟩ := hc x hx
  obtain ⟨tail, rfl⟩ := (Path.prefix_iff_extension x y).mp hxy
  exact (mem_divergence _ _ _).mpr ⟨x ++ tail, hy, z, hz, Path.divergence_extend_left tail hd⟩

theorem divergence_output_covered {a b : PathSpace} {p : Path}
    (h : p ∈ divergence a b) : ∃ x ∈ a, (p ≼ x) = true := by
  obtain ⟨x, hx, y, _, hd⟩ := (mem_divergence _ _ _).mp h
  exact ⟨x, hx, Path.divergence_prefix_left hd⟩

theorem divergence_nested_bound {a b c : PathSpace} {p : Path}
    (h : p ∈ divergence (divergence a b) c) :
    p ∈ divergence a c ∧ p ∈ divergence b c := by
  constructor
  · exact divergence_covered_mono (fun _ hx => divergence_output_covered hx) p h
  · apply divergence_covered_mono (a := divergence a b) (b := b) (c := c) ?_ p h
    intro x hx
    exact divergence_output_covered ((divergence_comm a b x).mp hx)
end PrunedModel.Convex
