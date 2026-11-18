import PrunedModel.Convex.PathSetRecursive
import PrunedModel.Convex.PathSetLaws

namespace PathMapModel.Path
open PathMapModel

theorem divergence_extend_both {a b p : Path} (x y : Path)
    (h : divergence a b = some p) : divergence (a ++ x) (b ++ y) = some p := by
  rw [divergence_comm]
  exact divergence_extend_left y ((divergence_comm b (a++x)).trans (divergence_extend_left x h))
end PathMapModel.Path

namespace PrunedModel.Convex
open PathMapModel

theorem mem_proper_overlap (a b : PathSpace) (f : Path → Path → PathSpace) (p : Path) :
    p ∈ properOverlap a b f ↔
    ∃ u ∈ a, ∃ r, r ≠ [] ∧ u ++ r ∈ b ∧ p ∈ f u r := by
  simp only [properOverlap,mem_ofPaths,List.mem_flatMap,mem_keys]
  constructor
  · rintro ⟨u,hu,v,hv,hp⟩
    cases hs : Path.stripPrefix u v with
    | none => simp [hs] at hp
    | some r =>
      have hvu := (Path.stripPrefix_eq_some u v r).mp hs
      subst v
      cases r with
      | nil => simp only [List.append_nil] at hs; simp [hs] at hp
      | cons c rs => exact ⟨u,hu,c::rs,by simp,hv,by simpa [hs] using hp⟩
  · rintro ⟨u,hu,r,hr,hv,hp⟩
    refine ⟨u,hu,u++r,hv,?_⟩
    have hs := (Path.stripPrefix_eq_some u (u++r) r).mpr rfl
    cases r with
    | nil => exact False.elim (hr rfl)
    | cons c rs => simpa [hs] using hp

theorem mem_leftOverlap (a b x y : PathSpace) (p : Path) :
    p ∈ PathSetLaws.leftOverlap a b x y ↔ ∃ u ∈ a, ∃ r, r ≠ [] ∧ u ++ r ∈ b ∧
      ∃ q ∈ divergence x (wrap r y), u ++ q = p := by
  simp only [PathSetLaws.leftOverlap,PathSetLaws.D]
  rw [mem_proper_overlap a b (fun u r => wrap u ((divergence x (wrap r y)))) p]
  change (∃ u ∈ a, ∃ r, r ≠ [] ∧ u ++ r ∈ b ∧ p ∈ wrap u ((divergence x (wrap r y)))) ↔ _
  simp only [mem_wrap]

theorem mem_rightOverlap (a b x y : PathSpace) (p : Path) :
    p ∈ PathSetLaws.rightOverlap a b x y ↔ ∃ v ∈ b, ∃ r, r ≠ [] ∧ v ++ r ∈ a ∧
      ∃ q ∈ divergence (wrap r x) y, v ++ q = p := by
  simp only [PathSetLaws.rightOverlap,PathSetLaws.D]
  rw [mem_proper_overlap b a (fun v r => wrap v ((divergence (wrap r x) y))) p]
  change (∃ v ∈ b, ∃ r, r ≠ [] ∧ v ++ r ∈ a ∧ p ∈ wrap v ((divergence (wrap r x) y))) ↔ _
  simp only [mem_wrap]

theorem divergence_product_nonempty (a b x y : PathSpace) (hx : x ≠ ofPaths []) (hy : y ≠ ofPaths []) (p : Path) :
    p ∈ divergence (product a x) (product b y) ↔
    p ∈ divergence a b ∨ p ∈ product (inter a b) (divergence x y) ∨
    p ∈ PathSetLaws.leftOverlap a b x y ∨ p ∈ PathSetLaws.rightOverlap a b x y := by
  constructor
  · intro h
    obtain ⟨ux,hux,vy,hvy,hd⟩ := (mem_divergence _ _ _).mp h
    obtain ⟨u,hu,s,hs,rfl⟩ := (mem_product _ _ _).mp hux
    obtain ⟨v,hv,t,ht,rfl⟩ := (mem_product _ _ _).mp hvy
    rcases Path.divergence_or_comparable u v with hd' | hp | hp
    · have he := Path.divergence_extend_both s t hd'
      rw [hd,Option.some.injEq] at he
      exact Or.inl ((mem_divergence _ _ _).mpr ⟨u,hu,v,hv,he ▸ hd'⟩)
    · obtain ⟨r,rfl⟩ := (Path.prefix_iff_extension u v).mp hp
      rw [List.append_assoc,Path.divergence_wrap] at hd
      obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hd
      cases r with
      | nil =>
        exact Or.inr (Or.inl ((mem_product _ _ _).mpr ⟨u,(mem_inter _ _ _).mpr ⟨hu,by simpa using hv⟩,
          q,(mem_divergence _ _ _).mpr ⟨s,hs,t,ht,hq⟩,rfl⟩))
      | cons c rs =>
        exact Or.inr (Or.inr (Or.inl ((mem_leftOverlap _ _ _ _ _).mpr
          ⟨u,hu,c::rs,by simp,hv,q,(mem_divergence _ _ _).mpr
            ⟨s,hs,(c::rs)++t,(mem_wrap _ _ _).mpr ⟨t,ht,rfl⟩,hq⟩,rfl⟩)))
    · obtain ⟨r,rfl⟩ := (Path.prefix_iff_extension v u).mp hp
      rw [List.append_assoc,Path.divergence_wrap] at hd
      obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hd
      cases r with
      | nil =>
        exact Or.inr (Or.inl ((mem_product _ _ _).mpr ⟨v,(mem_inter _ _ _).mpr ⟨by simpa using hu,hv⟩,
          q,(mem_divergence _ _ _).mpr ⟨s,hs,t,ht,hq⟩,rfl⟩))
      | cons c rs =>
        exact Or.inr (Or.inr (Or.inr ((mem_rightOverlap _ _ _ _ _).mpr
          ⟨v,hv,c::rs,by simp,hu,q,(mem_divergence _ _ _).mpr
            ⟨(c::rs)++s,(mem_wrap _ _ _).mpr ⟨s,hs,rfl⟩,t,ht,hq⟩,rfl⟩)))
  · rintro (h | h | h | h)
    · obtain ⟨u,hu,v,hv,hd⟩ := (mem_divergence _ _ _).mp h
      obtain ⟨s,hs⟩ := (ne_empty_iff x).mp hx
      obtain ⟨t,ht⟩ := (ne_empty_iff y).mp hy
      exact (mem_divergence _ _ _).mpr
        ⟨u++s,(mem_product _ _ _).mpr ⟨u,hu,s,hs,rfl⟩,
        v++t,(mem_product _ _ _).mpr ⟨v,hv,t,ht,rfl⟩,Path.divergence_extend_both s t hd⟩
    · obtain ⟨u,hu,q,hq,rfl⟩ := (mem_product _ _ _).mp h
      obtain ⟨hua,hub⟩ := (mem_inter _ _ _).mp hu
      obtain ⟨s,hs,t,ht,hd⟩ := (mem_divergence _ _ _).mp hq
      exact (mem_divergence _ _ _).mpr
        ⟨u++s,(mem_product _ _ _).mpr ⟨u,hua,s,hs,rfl⟩,
        u++t,(mem_product _ _ _).mpr ⟨u,hub,t,ht,rfl⟩,by simp [Path.divergence_wrap,hd]⟩
    · obtain ⟨u,hu,r,_,hv,q,hq,rfl⟩ := (mem_leftOverlap _ _ _ _ _).mp h
      obtain ⟨s,hs,rt,hrt,hd⟩ := (mem_divergence _ _ _).mp hq
      obtain ⟨t,ht,rfl⟩ := (mem_wrap _ _ _).mp hrt
      exact (mem_divergence _ _ _).mpr
        ⟨u++s,(mem_product _ _ _).mpr ⟨u,hu,s,hs,rfl⟩,
        (u++r)++t,(mem_product _ _ _).mpr ⟨u++r,hv,t,ht,rfl⟩,
        by simp [List.append_assoc,Path.divergence_wrap,hd]⟩
    · obtain ⟨v,hv,r,_,hu,q,hq,rfl⟩ := (mem_rightOverlap _ _ _ _ _).mp h
      obtain ⟨rs,hrs,t,ht,hd⟩ := (mem_divergence _ _ _).mp hq
      obtain ⟨s,hs,rfl⟩ := (mem_wrap _ _ _).mp hrs
      exact (mem_divergence _ _ _).mpr
        ⟨(v++r)++s,(mem_product _ _ _).mpr ⟨v++r,hu,s,hs,rfl⟩,
        v++t,(mem_product _ _ _).mpr ⟨v,hv,t,ht,rfl⟩,
        by simp [List.append_assoc,Path.divergence_wrap,hd]⟩

theorem equiv_members {a b : PathSpace} (h : equiv a b = true) (p : Path) : p ∈ a ↔ p ∈ b := by
  have he : a = b := of_decide_eq_true h
  subst b
  exact Iff.rfl

def Antichain (a : PathSpace) : Prop := ∀ p ∈ a, ∀ q ∈ a, (p ≼ q) = true → p = q

theorem prefixFree_antichain {a : PathSpace} (h : prefixFree a = true) : Antichain a := by
  intro p hp q hq hpq
  have he := equiv_members h q
  have hmin := (mem_basis a q).mp (he.mp hq)
  by_cases hh : p = q
  · exact hh
  · have hf := hmin.2 p hp hh
    simp [hpq] at hf

theorem prefix_free_product {a b x y : PathSpace} (hf : Antichain (union a b))
    (hx : x ≠ ofPaths []) (hy : y ≠ ofPaths []) (p : Path) :
    p ∈ divergence (product a x) (product b y) ↔
    p ∈ divergence a b ∨ p ∈ product (inter a b) (divergence x y) := by
  rw [divergence_product_nonempty a b x y hx hy]
  have hl : p ∉ PathSetLaws.leftOverlap a b x y := by
    intro h
    obtain ⟨u,hu,r,hr,hv,_⟩ := (mem_leftOverlap _ _ _ _ _).mp h
    have he := hf u ((mem_union a b _).mpr (Or.inl hu)) (u++r) ((mem_union a b _).mpr (Or.inr hv))
      ((Path.prefix_iff_extension _ _).mpr ⟨r,rfl⟩)
    have hn : r = [] := by have hh := congrArg List.length he; simpa using hh
    exact hr hn
  have hr : p ∉ PathSetLaws.rightOverlap a b x y := by
    intro h
    obtain ⟨v,hv,r,hr,hu,_⟩ := (mem_rightOverlap _ _ _ _ _).mp h
    have he := hf v ((mem_union a b _).mpr (Or.inr hv)) (v++r) ((mem_union a b _).mpr (Or.inl hu))
      ((Path.prefix_iff_extension _ _).mpr ⟨r,rfl⟩)
    have hn : r = [] := by have hh := congrArg List.length he; simpa using hh
    exact hr hn
  simp [hl,hr]

theorem common_prefix_code {a x y : PathSpace} (hf : Antichain a)
    (hx : x ≠ ofPaths []) (hy : y ≠ ofPaths []) (p : Path) :
    p ∈ divergence (product a x) (product a y) ↔
    p ∈ union (branches a) (product a (divergence x y)) := by
  have hf' : Antichain (union a a) := by intro u hu v hv; apply hf u (by simpa [mem_union] using hu) v (by simpa [mem_union] using hv)
  rw [prefix_free_product hf' hx hy]
  simp [branches,mem_union,mem_product,mem_inter]
end PrunedModel.Convex
