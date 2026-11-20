import PrunedModel.Convex.PathSetPowers

namespace PrunedModel.Convex
open PathMapModel

theorem hull_is_antichain (a : PathSpace) : Antichain (hull a) := by
  intro p hp q hq he
  by_cases hn : p = q
  · exact hn
  · have hf := hull_antichain hp hq hn
    simp [he] at hf

theorem divergence_empty_iff (a b : PathSpace) : divergence a b = ofPaths [] ↔
    ∀ x ∈ a, ∀ y ∈ b, (x ≼ y) = true ∨ (y ≼ x) = true := by
  constructor
  · intro h x hx y hy
    apply (Path.divergence_none_iff x y).mp
    cases hd : Path.divergence x y with
    | none => rfl
    | some p =>
      have hp := (mem_divergence a b p).mpr ⟨x,hx,y,hy,hd⟩
      simp [h] at hp
  · intro h
    apply (eq_empty_iff _).mpr
    intro p hp
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
    have hn := (Path.divergence_none_iff x y).mpr (h x hx y hy)
    simp [hd] at hn

/-- On two antichains, a single oriented comparable pair fixes the whole side. -/
theorem comparable_antichains {a b : PathSpace} (ha : Antichain a) (hb : Antichain b)
    (hc : ∀ x ∈ a, ∀ y ∈ b, (x ≼ y) = true ∨ (y ≼ x) = true)
    {x y : Path} (hx : x ∈ a) (hy : y ∈ b) (hxy : (x ≼ y) = true) :
    (∀ u ∈ a, u = x) ∧ (∀ v ∈ b, (x ≼ v) = true) := by
  constructor
  · intro u hu
    rcases hc u hu y hy with huy | hyu
    · rcases Path.prefixes_comparable huy hxy with hux | hxu
      · exact ha u hu x hx hux
      · exact (ha x hx u hu hxu).symm
    · exact (ha x hx u hu (Path.prefix_trans hxy hyu)).symm
  · intro v hv
    rcases hc x hx v hv with hxv | hvx
    · exact hxv
    · have he := hb v hv y hy (Path.prefix_trans hvx hxy)
      subst v; exact hxy

/-- The exact zero criterion in terms of the maximal paths on each side. -/
theorem zero_criterion (a b : PathSpace) : divergence a b = ofPaths [] ↔
    a = ofPaths [] ∨ b = ofPaths [] ∨
    (∃ x, (∀ u, u ∈ hull a ↔ u = x) ∧ ∀ v ∈ hull b, (x ≼ v) = true) ∨
    (∃ y, (∀ v, v ∈ hull b ↔ v = y) ∧ ∀ u ∈ hull a, (y ≼ u) = true) := by
  have he : divergence a b = ofPaths [] ↔ divergence (hull a) (hull b) = ofPaths [] := by
    simp only [eq_empty_iff,divergence_hull]
  rw [he,divergence_empty_iff]
  constructor
  · intro hc
    by_cases ha : a = ofPaths []
    · exact Or.inl ha
    by_cases hb : b = ofPaths []
    · exact Or.inr (Or.inl hb)
    have hha : hull a ≠ ofPaths [] := fun h => ha ((hull_nonempty a).mp h)
    have hhb : hull b ≠ ofPaths [] := fun h => hb ((hull_nonempty b).mp h)
    obtain ⟨x,hx,_⟩ := height_attained hha
    obtain ⟨y,hy,_⟩ := height_attained hhb
    rcases hc x hx y hy with hxy | hyx
    · obtain ⟨hs,hext⟩ := comparable_antichains (hull_is_antichain a) (hull_is_antichain b) hc hx hy hxy
      exact Or.inr (Or.inr (Or.inl ⟨x,fun u => ⟨hs u,fun h => h ▸ hx⟩,hext⟩))
    · have hc' : ∀ y ∈ hull b, ∀ x ∈ hull a, (y ≼ x) = true ∨ (x ≼ y) = true := by
        intro y hy x hx; exact (hc x hx y hy).symm
      obtain ⟨hs,hext⟩ := comparable_antichains (hull_is_antichain b) (hull_is_antichain a) hc' hy hx hyx
      exact Or.inr (Or.inr (Or.inr ⟨y,fun v => ⟨hs v,fun h => h ▸ hy⟩,hext⟩))
  · rintro (rfl | rfl | ⟨x,hx,hext⟩ | ⟨y,hy,hext⟩)
    · simp [hull]
    · simp [hull]
    · intro u hu v hv; have he := (hx u).mp hu; subst u; exact Or.inl (hext v hv)
    · intro u hu v hv; have he := (hy v).mp hv; subst v; exact Or.inr (hext u hu)

theorem commonPrefix_spec (a : PathSpace) (ha : a ≠ ofPaths []) (p : Path) :
    (p ≼ commonPrefix a) = true ↔ ∀ q ∈ a, (p ≼ q) = true := by
  have go : ∀ (xs : List Path) (q : Path), (p ≼ xs.foldl Path.lcp q) = true ↔
      (p ≼ q) = true ∧ ∀ r ∈ xs, (p ≼ r) = true := by
    intro xs
    induction xs with
    | nil => simp
    | cons r rs ih => intro q; simp [ih,Path.prefix_lcp]; grind
  cases he : a.keys with
  | nil => exact False.elim (ha ((keys_eq_nil_iff a).mp he))
  | cons q qs =>
    have hh := go qs q
    simp only [commonPrefix,he]
    simpa only [← mem_keys a,he,List.mem_cons,forall_eq_or_imp] using hh

theorem first_divergence_covers_left {a b : PathSpace} (ha : Antichain a) {p : Path}
    (hp : p ∈ basis (divergence a b)) : ∀ u ∈ a, (p ≼ u) = true := by
  have hmin := (mem_basis _ _).mp hp
  obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hmin.1
  have hpx := Path.divergence_prefix_left hd
  have hpy := Path.divergence_prefix_left ((Path.divergence_comm y x).trans hd)
  intro u hu
  rcases Path.divergence_or_comparable u p with hup | hup | hpu
  · let q := Path.lcp u p
    have hq : q ∈ divergence a b := by
      obtain ⟨r,rfl⟩ := (Path.prefix_iff_extension p y).mp hpy
      exact (mem_divergence _ _ _).mpr ⟨u,hu,p++r,hy,by
        rw [Path.divergence_comm]
        exact Path.divergence_extend_left r ((Path.divergence_comm p u).trans hup)⟩
    have hqp := Path.lcp_prefix_right u p
    have hn : q ≠ p := by have hl := Path.divergence_length_right hup; intro hh; dsimp [q] at hh; rw [hh] at hl; omega
    have hf := hmin.2 q hq hn
    simp [q,hqp] at hf
  · have he := ha u hu x hx (Path.prefix_trans hup hpx)
    subst u
    have hl := Path.prefix_length hup
    have hs := Path.divergence_length_left hd
    omega
  · exact hpu

theorem first_divergence (a b : PathSpace) (h : divergence a b ≠ ofPaths []) (p : Path) :
    p ∈ basis (divergence a b) ↔ p = commonPrefix (union (hull a) (hull b)) := by
  let x := divergence (hull a) (hull b)
  have hx : ∀ q, q ∈ x ↔ q ∈ divergence a b := divergence_hull a b
  have hbas : ∀ q, q ∈ basis x ↔ q ∈ basis (divergence a b) := by
    intro q; simp only [mem_basis,hx]
  have hn : x ≠ ofPaths [] := by
    intro hh
    apply h
    apply (eq_empty_iff _).mpr
    intro q hq
    have hm := (hx q).mpr hq
    simp [hh] at hm
  have hall : ∀ q ∈ basis x, q = commonPrefix (union (hull a) (hull b)) := by
    intro q hq
    have hqa := first_divergence_covers_left (hull_is_antichain a) hq
    have hswap : q ∈ basis (divergence (hull b) (hull a)) := by
      simpa only [mem_basis,divergence_comm (hull b) (hull a)] using hq
    have hqb := first_divergence_covers_left (hull_is_antichain b) hswap
    obtain ⟨u,hu,v,hv,hd⟩ := (mem_divergence _ _ _).mp (basis_subset _ hq)
    have hun : union (hull a) (hull b) ≠ ofPaths [] := (ne_empty_iff _).mpr ⟨u,(mem_union _ _ _).mpr (Or.inl hu)⟩
    have hpref := (commonPrefix_spec _ hun q).mpr (by
      intro r hr; rcases (mem_union _ _ _).mp hr with hr | hr
      · exact hqa r hr
      · exact hqb r hr)
    have hcp := (commonPrefix_spec _ hun (commonPrefix (union (hull a) (hull b)))).mp (Path.prefix_self _)
    have hcq := (Path.prefix_lcp _ u v).mpr ⟨hcp u ((mem_union _ _ _).mpr (Or.inl hu)),hcp v ((mem_union _ _ _).mpr (Or.inr hv))⟩
    rw [Path.divergence_lcp hd] at hcq
    exact Path.prefix_antisymm hpref hcq
  rw [← hbas p]
  constructor
  · exact hall p
  · intro he
    obtain ⟨q,hq,_⟩ := height_attained (fun hh => hn ((basis_nonempty x).mp hh))
    have heq := (hall q hq).trans he.symm
    exact heq ▸ hq
end PrunedModel.Convex
