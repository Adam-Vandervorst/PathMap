import PrunedModel.Convex.PathSetAlgebra
import Init.Data.List.MinMaxOn

namespace PathMapModel.Path
open PathMapModel

theorem prefix_iff_list (p q : Path) : (p ≼ q) = true ↔ p <+: q := by
  rw [prefix_iff_extension, List.prefix_iff_exists_eq_append]

@[simp] theorem prefix_self (p : Path) : (p ≼ p) = true :=
  PrunedModel.isPrefixOf_self p

theorem prefix_trans {p q r : Path} (h : (p ≼ q) = true) (k : (q ≼ r) = true) :
    (p ≼ r) = true := (prefix_iff_list _ _).mpr
      (((prefix_iff_list _ _).mp h).trans ((prefix_iff_list _ _).mp k))

theorem prefix_length {p q : Path} (h : (p ≼ q) = true) : p.length ≤ q.length :=
  ((prefix_iff_list _ _).mp h).length_le

theorem prefix_eq_of_length {p q : Path} (h : (p ≼ q) = true) (hl : q.length ≤ p.length) :
    p = q := ((prefix_iff_list _ _).mp h).eq_of_length_le hl

theorem prefix_antisymm {p q : Path} (h : (p ≼ q) = true) (k : (q ≼ p) = true) : p = q :=
  prefix_eq_of_length h (prefix_length k)

theorem prefixes_comparable {p q r : Path} (h : (p ≼ r) = true) (k : (q ≼ r) = true) :
    (p ≼ q) = true ∨ (q ≼ p) = true := by
  simpa only [prefix_iff_list] using List.prefix_or_prefix_of_prefix
    ((prefix_iff_list _ _).mp h) ((prefix_iff_list _ _).mp k)
end PathMapModel.Path

namespace PrunedModel.Convex
open PathMapModel

theorem hull_covers {a : PathSpace} {p : Path} (hp : p ∈ a) :
    ∃ q ∈ hull a, (p ≼ q) = true := by
  let s := a.keys.filter (p ≼ ·)
  have hs : p ∈ s := by simp [s,hp]
  let q := s.maxOn List.length (List.ne_nil_of_mem hs)
  have hq : q ∈ s := List.maxOn_mem
  have hqm : q ∈ a ∧ (p ≼ q) = true := by simpa [s] using hq
  refine ⟨q, (mem_hull a q).mpr ⟨hqm.1, ?_⟩, hqm.2⟩
  intro r hr hne
  cases he : (q ≼ r) with
  | false => rfl
  | true =>
    have hrs : r ∈ s := by simp [s, hr, Path.prefix_trans hqm.2 he]
    have hl : r.length ≤ q.length := List.le_apply_maxOn_of_mem hrs
    exact False.elim (hne (Path.prefix_eq_of_length he hl).symm)

theorem basis_below {a : PathSpace} {p : Path} (hp : p ∈ a) :
    ∃ q ∈ basis a, (q ≼ p) = true := by
  let s := a.keys.filter (· ≼ p)
  have hs : p ∈ s := by simp [s,hp]
  let q := s.minOn List.length (List.ne_nil_of_mem hs)
  have hq : q ∈ s := List.minOn_mem
  have hqm : q ∈ a ∧ (q ≼ p) = true := by simpa [s] using hq
  refine ⟨q, (mem_basis a q).mpr ⟨hqm.1, ?_⟩, hqm.2⟩
  intro r hr hne
  cases he : (r ≼ q) with
  | false => rfl
  | true =>
    have hrs : r ∈ s := by simp [s, hr, Path.prefix_trans he hqm.2]
    have hl : q.length ≤ r.length := List.apply_minOn_le_of_mem hrs
    exact False.elim (hne (Path.prefix_eq_of_length he hl))

theorem hull_nonempty (a : PathSpace) : hull a = (ofPaths []) ↔ a = (ofPaths []) := by
  constructor
  · intro h
    apply (eq_empty_iff a).mpr
    intro p hp
    obtain ⟨q,hq,_⟩ := hull_covers hp
    simp [h] at hq
  · rintro rfl; rfl

theorem basis_nonempty (a : PathSpace) : basis a = (ofPaths []) ↔ a = (ofPaths []) := by
  constructor
  · intro h
    apply (eq_empty_iff a).mpr
    intro p hp
    obtain ⟨q,hq,_⟩ := basis_below hp
    simp [h] at hq
  · rintro rfl; rfl

theorem divergence_hull_left (a b : PathSpace) (p : Path) :
    p ∈ divergence (hull a) b ↔ p ∈ divergence a b := by
  exact ⟨divergence_mono (fun _ h => hull_subset a h) (fun _ h => h) p,
    divergence_covered_mono (fun _ h => hull_covers h) p⟩

theorem divergence_hull (a b : PathSpace) (p : Path) :
    p ∈ divergence (hull a) (hull b) ↔ p ∈ divergence a b := by
  rw [divergence_hull_left, divergence_comm, divergence_hull_left, divergence_comm]

theorem branch_hull (a : PathSpace) (p : Path) :
    p ∈ branches (hull a) ↔ p ∈ branches a := divergence_hull a a p

theorem basis_of_hull (a : PathSpace) (p : Path) : p ∈ basis (hull a) ↔ p ∈ hull a := by
  exact ⟨basis_subset _, fun hp => (mem_basis _ _).mpr
    ⟨hp, fun q hq hne => hull_antichain hq hp hne⟩⟩

theorem hull_of_basis (a : PathSpace) (p : Path) : p ∈ hull (basis a) ↔ p ∈ basis a := by
  exact ⟨hull_subset _, fun hp => (mem_hull _ _).mpr
    ⟨hp, fun q hq hne => basis_antichain hp hq (Ne.symm hne)⟩⟩

theorem mem_restrict (a b : PathSpace) (p : Path) :
    p ∈ restrict a b ↔ p ∈ a ∧ ∃ q ∈ b, (q ≼ p) = true := by
  rw [Zippy.mem_restriction]
  simp only [Path.prefix_iff_extension]
  grind

theorem restriction_basis_mask (a b : PathSpace) (p : Path) :
    p ∈ restrict a (basis b) ↔ p ∈ restrict a b := by
  simp only [mem_restrict]
  constructor
  · rintro ⟨hp,q,hq,hqp⟩; exact ⟨hp,q,basis_subset b hq,hqp⟩
  · rintro ⟨hp,q,hq,hqp⟩
    obtain ⟨r,hr,hrq⟩ := basis_below hq
    exact ⟨hp,r,hr,Path.prefix_trans hrq hqp⟩

/-- Replacing a space by any cofinal subset preserves its maximal members. -/
theorem hull_cofinal {a b : PathSpace} (hs : ∀ p ∈ b, p ∈ a)
    (hc : ∀ p ∈ a, ∃ q ∈ b, (p ≼ q) = true) (p : Path) :
    p ∈ hull a ↔ p ∈ hull b := by
  constructor
  · intro hp
    obtain ⟨q,hq,hpq⟩ := hc p (hull_subset a hp)
    have he : q = p := by
      by_cases hn : q = p
      · exact hn
      exfalso
      have hf := ((mem_hull a p).mp hp).2 q (hs q hq) hn
      simp [hpq] at hf
    subst q
    exact (mem_hull b p).mpr ⟨hq, fun q hq hn => ((mem_hull a p).mp hp).2 q (hs q hq) hn⟩
  · intro hp
    refine (mem_hull a p).mpr ⟨hs p (hull_subset b hp), ?_⟩
    intro q hq hn
    cases he : (p ≼ q) with
    | false => rfl
    | true =>
      obtain ⟨r,hr,hqr⟩ := hc q hq
      have hpr := Path.prefix_trans he hqr
      have hrn : r ≠ p := by intro hh; subst r; exact hn (Path.prefix_antisymm he hqr).symm
      have hf := ((mem_hull b p).mp hp).2 r hr hrn
      simp [hpr] at hf

theorem basis_coinitial {a b : PathSpace} (hs : ∀ p ∈ b, p ∈ a)
    (hc : ∀ p ∈ a, ∃ q ∈ b, (q ≼ p) = true) (p : Path) :
    p ∈ basis a ↔ p ∈ basis b := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := hc p (basis_subset a hp)
    have he : q = p := by
      by_cases hn : q = p
      · exact hn
      exfalso
      have hf := ((mem_basis a p).mp hp).2 q (hs q hq) hn
      simp [hqp] at hf
    subst q
    exact (mem_basis b p).mpr ⟨hq, fun q hq hn => ((mem_basis a p).mp hp).2 q (hs q hq) hn⟩
  · intro hp
    refine (mem_basis a p).mpr ⟨hs p (basis_subset b hp), ?_⟩
    intro q hq hn
    cases he : (q ≼ p) with
    | false => rfl
    | true =>
      obtain ⟨r,hr,hrq⟩ := hc q hq
      have hrp := Path.prefix_trans hrq he
      have hrn : r ≠ p := by intro hh; subst r; exact hn (Path.prefix_antisymm hrq he).symm
      have hf := ((mem_basis b p).mp hp).2 r hr hrn
      simp [hrp] at hf

theorem hull_union (a b : PathSpace) (p : Path) :
    p ∈ hull (union a b) ↔ p ∈ hull (union (hull a) (hull b)) := by
  apply hull_cofinal
  · intro q hq
    simp only [mem_union] at hq ⊢
    exact hq.elim (fun h => Or.inl (hull_subset a h)) (fun h => Or.inr (hull_subset b h))
  · intro q hq
    simp only [mem_union] at hq ⊢
    rcases hq with hq | hq
    · obtain ⟨r,hr,hqr⟩ := hull_covers hq; exact ⟨r,Or.inl hr,hqr⟩
    · obtain ⟨r,hr,hqr⟩ := hull_covers hq; exact ⟨r,Or.inr hr,hqr⟩

theorem basis_union (a b : PathSpace) (p : Path) :
    p ∈ basis (union a b) ↔ p ∈ basis (union (basis a) (basis b)) := by
  apply basis_coinitial
  · intro q hq
    simp only [mem_union] at hq ⊢
    exact hq.elim (fun h => Or.inl (basis_subset a h)) (fun h => Or.inr (basis_subset b h))
  · intro q hq
    simp only [mem_union] at hq ⊢
    rcases hq with hq | hq
    · obtain ⟨r,hr,hrq⟩ := basis_below hq; exact ⟨r,Or.inl hr,hrq⟩
    · obtain ⟨r,hr,hrq⟩ := basis_below hq; exact ⟨r,Or.inr hr,hrq⟩
end PrunedModel.Convex
