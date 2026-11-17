import PathMapModel.Retain

namespace PathMapModel.PathSpace

/-- Restriction commutes with convex meet when applied to both inputs. -/
theorem restrict_convexMeet (a b c : PathSpace) :
    Same (restrict (convexMeet a b) c) (convexMeet (restrict a c) (restrict b c)) := by
  intro p; simp only [mem_convexMeet,hull_restrict,mem_restrict]; constructor
  · rintro ⟨⟨ha,hb,t,hta,htb,hpt⟩,q,hq,hqp⟩
    exact ⟨⟨ha,q,hq,hqp⟩,⟨hb,q,hq,hqp⟩,t,
      ⟨hta,q,hq,Path.prefix_trans hqp hpt⟩,⟨htb,q,hq,Path.prefix_trans hqp hpt⟩,hpt⟩
  · rintro ⟨⟨ha,q,hq,hqp⟩,⟨hb,_⟩,t,⟨hta,_⟩,⟨htb,_⟩,hpt⟩
    exact ⟨⟨ha,hb,t,hta,htb,hpt⟩,q,hq,hqp⟩

theorem restrict_convexSubtract (a b c : PathSpace) :
    Same (restrict (convexSubtract a b) c) (convexSubtract (restrict a c) b) := by
  intro p; simp only [mem_convexSubtract,hull_restrict,mem_restrict]; constructor
  · rintro ⟨⟨ha,t,ht,hn,hpt⟩,q,hq,hqp⟩
    exact ⟨⟨ha,q,hq,hqp⟩,t,⟨ht,q,hq,Path.prefix_trans hqp hpt⟩,hn,hpt⟩
  · rintro ⟨⟨ha,q,hq,hqp⟩,t,⟨ht,_⟩,hn,hpt⟩
    exact ⟨⟨ha,t,ht,hn,hpt⟩,q,hq,hqp⟩

theorem restrict_convexSubtract_both (a b c : PathSpace) :
    Same (restrict (convexSubtract a b) c) (convexSubtract (restrict a c) (restrict b c)) := by
  intro p; rw [restrict_convexSubtract]
  simp only [mem_convexSubtract,hull_restrict,mem_restrict]; grind

/-- Selecting original tips permits exact normalization of a convex meet. -/
theorem convexMeet_retain_tips {a t : PathSpace} (ht : Included t (hull a)) (b : PathSpace) :
    Same (convexMeet (retain a t) b) (retain (inter a b) (inter t (hull b))) := by
  intro p; simp only [mem_convexMeet,hull_retain ht,mem_retain,mem_inter]; grind

theorem convexMeet_retain_both {a b t u : PathSpace}
    (ht : Included t (hull a)) (hu : Included u (hull b)) :
    Same (convexMeet (retain a t) (retain b u)) (retain (inter a b) (inter t u)) := by
  intro p; simp only [mem_convexMeet,hull_retain ht,hull_retain hu,mem_retain,mem_inter]; grind

theorem convexMeet_pruning {a t : PathSpace} (ht : Included t (hull a)) :
    Same (convexMeet a (retain a t)) (retain a t) := by
  intro p; simp only [mem_convexMeet,hull_retain ht,mem_retain]; constructor
  · grind
  · rintro ⟨hp,q,hq,hpq⟩; exact ⟨hp,⟨hp,q,hq,hpq⟩,q,ht q hq,hq,hpq⟩

/-- Ordinary retention can expose a new tip; convex retention protects old tips. -/
theorem convex_pruning_retain_bound (a b : PathSpace) :
    Included (retain a (retain (hull a) b)) (retain a b) := by
  intro p hp
  exact (retain_congr (retain_hull a) (fun _ => Iff.rfl) p).mp
    (retain_nested_bound a (hull a) b p hp)

theorem convexMeet_retained_mask (a b : PathSpace) :
    Same (convexMeet a b) (retain (inter a b) (inter (hull a) (hull b))) := fun _ => Iff.rfl

theorem convexSubtract_retained_mask (a b : PathSpace) :
    Same (convexSubtract a b) (retain a (diff (hull a) b)) := fun _ => Iff.rfl

end PathMapModel.PathSpace

namespace PathMapModel.Map

theorem retain_support {V W : Type} (a : PathMap V) (b : PathMap W) :
    PathSpace.Same (PathSpace.ofMap (retain a b)) (PathSpace.retain (PathSpace.ofMap a) (PathSpace.ofMap b)) := by
  intro p
  change p ∈ PathSpace.ofMap (selectConvexSupport a (PathSpace.retain (PathSpace.ofMap a) (PathSpace.ofMap b))) ↔ _
  rw [selectConvexSupport_keys]; constructor
  · exact And.right
  · intro h; exact ⟨PathSpace.retain_subset _ _ p h,h⟩

end PathMapModel.Map
