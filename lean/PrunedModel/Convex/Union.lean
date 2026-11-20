import PrunedModel.Convex.Morphisms

namespace PrunedModel.Convex
open PathMapModel

theorem hull_in_subset {a b : PathSpace} (h : Included a b) {p : Path} (hp : p ∈ a)
    (ht : p ∈ hull b) : p ∈ hull a := by
  rw [mem_hull_max]; exact ⟨hp,fun q hq hpq => hull_max ht (h q hq) hpq⟩

theorem hull_union_cases {a b : PathSpace} {p : Path} (h : p ∈ hull (union a b)) :
    p ∈ hull a ∨ p ∈ hull b := by
  rcases (mem_union _ _ _).mp (hull_subset _ h) with ha | hb
  · exact Or.inl (hull_in_subset (fun _ hq => mem_union_left _ hq) ha h)
  · exact Or.inr (hull_in_subset (fun _ hq => mem_union_right _ hq) hb h)

theorem convexMeet_union_subset (a : PathSpace) {b c : PathSpace}
    (hb : IsPrefixClosed b) (hc : IsPrefixClosed c) :
    Included (convexMeet a (union b c)) (union (convexMeet a b) (convexMeet a c)) := by
  intro p hp; obtain ⟨ha,_,t,hta,ht,hpt⟩ := (mem_convexMeet _ _ _).mp hp
  rcases hull_union_cases ht with htb | htc
  · exact mem_union_left _ ((mem_convexMeet _ _ _).mpr ⟨ha,hb t (hull_subset _ htb) p hpt,t,hta,htb,hpt⟩)
  · exact mem_union_right _ ((mem_convexMeet _ _ _).mpr ⟨ha,hc t (hull_subset _ htc) p hpt,t,hta,htc,hpt⟩)

theorem convexMeet_union (a : PathSpace) {b c : PathSpace}
    (hb : IsPrefixClosed b) (hc : IsPrefixClosed c) (h : Antichain (union (hull b) (hull c))) :
    Same (convexMeet a (union b c)) (union (convexMeet a b) (convexMeet a c)) := by
  intro p; refine ⟨convexMeet_union_subset a hb hc p,?_⟩
  intro hp; rcases (mem_union _ _ _).mp hp with hp | hp
  · obtain ⟨ha,hb,t,hta,htb,hpt⟩ := (mem_convexMeet _ _ _).mp hp
    exact (mem_convexMeet _ _ _).mpr ⟨ha,mem_union_left _ hb,t,hta,(hull_union_compatible h t).mpr (mem_union_left _ htb),hpt⟩
  · obtain ⟨ha,hc,t,hta,htc,hpt⟩ := (mem_convexMeet _ _ _).mp hp
    exact (mem_convexMeet _ _ _).mpr ⟨ha,mem_union_right _ hc,t,hta,(hull_union_compatible h t).mpr (mem_union_right _ htc),hpt⟩

theorem convexSubtract_union_source {a b c : PathSpace}
    (ha : IsPrefixClosed a) (hb : IsPrefixClosed b) (hc : IsPrefixClosed c) :
    Same (convexSubtract (union a b) c) (union (convexSubtract a c) (convexSubtract b c)) := by
  intro p; constructor
  · intro hp; obtain ⟨_,t,ht,hn,hpt⟩ := (mem_convexSubtract _ _ _).mp hp
    rcases hull_union_cases ht with hta | htb
    · exact mem_union_left _ ((mem_convexSubtract _ _ _).mpr ⟨ha t (hull_subset _ hta) p hpt,t,hta,hn,hpt⟩)
    · exact mem_union_right _ ((mem_convexSubtract _ _ _).mpr ⟨hb t (hull_subset _ htb) p hpt,t,htb,hn,hpt⟩)
  · have lift : ∀ t ∈ union a b, t ∉ c → ∃ r ∈ hull (union a b), r ∉ c ∧ (t ≼ r) = true := by
      intro t ht hn; obtain ⟨r,hr,htr⟩ := hull_covers ht
      exact ⟨r,hr,fun hrc => hn (hc r hrc t htr),htr⟩
    intro hp; rcases (mem_union _ _ _).mp hp with hp | hp
    · obtain ⟨hp,t,ht,hn,hpt⟩ := (mem_convexSubtract _ _ _).mp hp
      obtain ⟨r,hr,hrn,htr⟩ := lift t (mem_union_left _ (hull_subset _ ht)) hn
      exact (mem_convexSubtract _ _ _).mpr ⟨mem_union_left _ hp,r,hr,hrn,Path.prefix_trans hpt htr⟩
    · obtain ⟨hp,t,ht,hn,hpt⟩ := (mem_convexSubtract _ _ _).mp hp
      obtain ⟨r,hr,hrn,htr⟩ := lift t (mem_union_right _ (hull_subset _ ht)) hn
      exact (mem_convexSubtract _ _ _).mpr ⟨mem_union_right _ hp,r,hr,hrn,Path.prefix_trans hpt htr⟩

end PrunedModel.Convex
