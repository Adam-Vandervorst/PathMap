import PrunedModel.Convex.Pruning

namespace PrunedModel.Convex
open PathMapModel

/-- Prefix-order convexity; this does not require prefix closure. -/
def IsConvex (a : PathSpace) : Prop := ∀ p ∈ a, ∀ r ∈ a, ∀ q,
  (p ≼ q) = true → (q ≼ r) = true → q ∈ a
def IsPrefixClosed (a : PathSpace) : Prop := ∀ r ∈ a, ∀ p, (p ≼ r) = true → p ∈ a

theorem retain_lower {a t : PathSpace} {p q : Path} (hp : p ∈ a)
    (hq : q ∈ retain a t) (hpq : (p ≼ q) = true) : p ∈ retain a t := by
  obtain ⟨_,r,hr,hqr⟩ := (mem_retain _ _ _).mp hq
  exact (mem_retain _ _ _).mpr ⟨hp,r,hr,Path.prefix_trans hpq hqr⟩

theorem retain_convex {a : PathSpace} (ha : IsConvex a) (t : PathSpace) : IsConvex (retain a t) := by
  intro p hp r hr q hpq hqr
  exact retain_lower (ha p ((mem_retain _ _ _).mp hp).1 r ((mem_retain _ _ _).mp hr).1 q hpq hqr) hr hqr

theorem retain_prefixClosed {a : PathSpace} (ha : IsPrefixClosed a) (t : PathSpace) : IsPrefixClosed (retain a t) := by
  intro r hr p hpr; exact retain_lower (ha r ((mem_retain _ _ _).mp hr).1 p hpr) hr hpr

theorem convexMeet_convex {a b : PathSpace} (ha : IsConvex a) (hb : IsConvex b) : IsConvex (convexMeet a b) := by
  apply retain_convex
  intro p hp r hr q hpq hqr
  exact (mem_inter _ _ _).mpr ⟨ha p ((mem_inter _ _ _).mp hp).1 r ((mem_inter _ _ _).mp hr).1 q hpq hqr,
    hb p ((mem_inter _ _ _).mp hp).2 r ((mem_inter _ _ _).mp hr).2 q hpq hqr⟩

theorem convexSubtract_convex {a : PathSpace} (ha : IsConvex a) (b : PathSpace) : IsConvex (convexSubtract a b) := retain_convex ha _

theorem convexMeet_prefixClosed {a b : PathSpace} (ha : IsPrefixClosed a) (hb : IsPrefixClosed b) : IsPrefixClosed (convexMeet a b) := by
  apply retain_prefixClosed
  intro r hr p hpr; exact (mem_inter _ _ _).mpr ⟨ha r ((mem_inter _ _ _).mp hr).1 p hpr,hb r ((mem_inter _ _ _).mp hr).2 p hpr⟩

theorem convexSubtract_prefixClosed {a : PathSpace} (ha : IsPrefixClosed a) (b : PathSpace) : IsPrefixClosed (convexSubtract a b) := retain_prefixClosed ha _

/-- Basis of the discarded region generates precisely the pruning cut. -/
theorem pruning_basis_cut (x t : PathSpace) :
    Same (restrict x (basis (diff x (retain x t)))) (diff x (retain x t)) := by
  intro p; rw [restriction_basis_mask,mem_restrict,mem_diff]
  constructor
  · rintro ⟨hp,q,hq,hqp⟩
    have hqn := ((mem_diff _ _ _).mp hq).2
    exact ⟨hp,fun hr => hqn (retain_lower ((mem_diff _ _ _).mp hq).1 hr hqp)⟩
  · rintro ⟨hp,hn⟩; exact ⟨hp,p,(mem_diff _ _ _).mpr ⟨hp,hn⟩,Path.prefix_self p⟩

theorem pruning_basis_raffinate (x t : PathSpace) :
    Same (raffinate x (basis (diff x (retain x t)))) (retain x t) := by
  intro p; simp only [raffinate,Zippy.raffination,mem_diff,pruning_basis_cut,mem_retain]; grind

theorem convexMeet_basis (a b : PathSpace) :
    Same (raffinate (inter a b) (basis (diff (inter a b) (convexMeet a b)))) (convexMeet a b) := pruning_basis_raffinate _ _

theorem convexSubtract_basis (a b : PathSpace) :
    Same (raffinate a (basis (diff a (convexSubtract a b)))) (convexSubtract a b) := pruning_basis_raffinate _ _

theorem divergence_convexMeet (a b c : PathSpace) :
    Same (divergence (convexMeet a b) c) (divergence (inter (hull a) (hull b)) (hull c)) := by
  intro p; exact (divergence_hull _ _ p).symm.trans (divergence_congr (hull_convexMeet a b) (fun _ => Iff.rfl) p)

theorem divergence_convexSubtract (a b c : PathSpace) :
    Same (divergence (convexSubtract a b) c) (divergence (diff (hull a) b) (hull c)) := by
  intro p; exact (divergence_hull _ _ p).symm.trans (divergence_congr (hull_convexSubtract a b) (fun _ => Iff.rfl) p)

theorem divergence_subtract_partition (a b c : PathSpace) :
    Same (divergence a c) (union (divergence (convexSubtract a b) c) (divergence (inter (hull a) b) c)) := by
  have hs : Same (hull a) (union (diff (hull a) b) (inter (hull a) b)) := by
    intro p; simp only [mem_union,mem_diff,mem_inter]; grind
  intro p
  rw [← divergence_hull_left a c p,divergence_congr hs (fun _ => Iff.rfl),divergence_union_left]
  simp only [mem_union]
  have he : Same (divergence (convexSubtract a b) c) (divergence (diff (hull a) b) c) := by
    intro q; exact (divergence_hull_left _ _ q).symm.trans (divergence_congr (hull_convexSubtract a b) (fun _ => Iff.rfl) q)
  rw [he]

theorem branches_convexMeet (a b : PathSpace) : Included (branches (convexMeet a b)) (inter (branches a) (branches b)) := by
  intro p hp
  have hs := convexMeet_subset a b
  exact (mem_inter _ _ _).mpr ⟨divergence_mono (fun q hq => ((mem_inter _ _ _).mp (hs q hq)).1) (fun q hq => ((mem_inter _ _ _).mp (hs q hq)).1) p hp,
    divergence_mono (fun q hq => ((mem_inter _ _ _).mp (hs q hq)).2) (fun q hq => ((mem_inter _ _ _).mp (hs q hq)).2) p hp⟩

theorem branches_convexSubtract (a b : PathSpace) : Included (branches (convexSubtract a b)) (branches a) :=
  divergence_mono (convexSubtract_subset a b) (convexSubtract_subset a b)

theorem convex_partition (a b : PathSpace) :
    Same (union (convexSubtract a b) (convexSubtract a (diff (hull a) b))) a := by
  intro p; simp only [mem_union,mem_convexSubtract,mem_diff]
  constructor
  · grind
  · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
    by_cases hb : t ∈ b
    · exact Or.inr ⟨hp,t,ht,fun hh => hh.2 hb,hpt⟩
    · exact Or.inl ⟨hp,t,ht,hb,hpt⟩

theorem convex_partition_disjoint (a b : PathSpace) :
    Same (convexMeet (convexSubtract a b) (convexSubtract a (diff (hull a) b))) (ofPaths []) := by
  intro p; simp only [mem_convexMeet,hull_convexSubtract,mem_diff,mem_ofPaths,List.not_mem_nil,iff_false]; grind

theorem branches_convex_partition (a b : PathSpace) (p : Path) :
    p ∈ branches a ↔ p ∈ branches (convexSubtract a b) ∨
      p ∈ branches (convexSubtract a (diff (hull a) b)) ∨
      p ∈ divergence (convexSubtract a b) (convexSubtract a (diff (hull a) b)) := by
  exact (divergence_congr (convex_partition a b) (convex_partition a b) p).symm.trans (branches_union _ _ p)

/-- Literal subtraction is a separate operator and can introduce gaps. -/
def convexLiteralSubtract (a b : PathSpace) : PathSpace := retain (diff a b) (diff (hull a) b)

theorem convexLiteralSubtract_diff (a b : PathSpace) : Same (convexLiteralSubtract a b) (diff (convexSubtract a b) b) := by
  intro p; simp only [convexLiteralSubtract,mem_retain,mem_diff,mem_convexSubtract]; grind

theorem hull_surviving_diff {a b : PathSpace} {t : Path} (ht : t ∈ hull a) (hn : t ∉ b) : t ∈ hull (diff a b) := by
  apply (mem_hull _ _).mpr
  exact ⟨(mem_diff _ _ _).mpr ⟨hull_subset a ht,hn⟩,fun q hq hne => ((mem_hull _ _).mp ht).2 q ((mem_diff _ _ _).mp hq).1 hne⟩

theorem convexLiteralSubtract_meet (a b : PathSpace) : Same (convexLiteralSubtract a b) (convexMeet a (diff a b)) := by
  intro p; simp only [convexLiteralSubtract,mem_retain,mem_diff,mem_convexMeet]
  constructor
  · rintro ⟨⟨hp,hn⟩,t,⟨ht,htn⟩,hpt⟩; exact ⟨hp,⟨hp,hn⟩,t,ht,hull_surviving_diff ht htn,hpt⟩
  · rintro ⟨hp,⟨_,hn⟩,t,ht,htd,hpt⟩
    exact ⟨⟨hp,hn⟩,t,⟨ht,((mem_diff _ _ _).mp (hull_subset _ htd)).2⟩,hpt⟩

theorem convexLiteralSubtract_hull (a b : PathSpace) :
    Same (hull (convexLiteralSubtract a b)) (diff (hull a) b) := by
  apply hull_retain
  intro t ht; obtain ⟨hh,hn⟩ := (mem_diff _ _ _).mp ht
  exact hull_surviving_diff hh hn

end PrunedModel.Convex
