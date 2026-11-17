import PathMapModel.PathSetCertificates

/-! Stable convex operations. Equations ignore list order and duplicates.
Subtraction retains supporting interiors; its mask selects original tips. -/
namespace PathMapModel.PathSpace

def convexMeet (a b : PathSpace) : PathSpace := retain (inter a b) (inter (hull a) (hull b))
def convexSubtract (a b : PathSpace) : PathSpace := retain a (diff (hull a) b)
abbrev Included (a b : PathSpace) : Prop := ∀ p, p ∈ a → p ∈ b
abbrev Same (a b : PathSpace) : Prop := ∀ p, p ∈ a ↔ p ∈ b
def ConvexLE (a b : PathSpace) : Prop := Included a b ∧ Included (hull a) (hull b)

theorem same_equiv (a b : PathSpace) : Same a b ↔ equiv a b = true := (equiv_iff a b).symm

theorem mem_convexMeet (a b : PathSpace) (p : Path) :
    p ∈ convexMeet a b ↔ p ∈ a ∧ p ∈ b ∧ ∃ t, t ∈ hull a ∧ t ∈ hull b ∧ (p ≼ t) = true := by
  simp only [convexMeet, mem_retain, mem_inter]; grind

theorem mem_convexSubtract (a b : PathSpace) (p : Path) :
    p ∈ convexSubtract a b ↔ p ∈ a ∧ ∃ t, t ∈ hull a ∧ t ∉ b ∧ (p ≼ t) = true := by
  simp only [convexSubtract, mem_retain, mem_diff]; grind

theorem retain_congr {a b t u : PathSpace} (h : Same a b) (k : Same t u) : Same (retain a t) (retain b u) := by
  intro p; simp only [mem_retain, h, k]

theorem hull_max {a : PathSpace} {p q : Path} (hp : p ∈ hull a) (hq : q ∈ a)
    (h : (p ≼ q) = true) : p = q := by
  by_cases hn : p = q
  · exact hn
  · have := ((mem_hull a p).mp hp).2 q hq (Ne.symm hn)
    simp [h] at this

theorem hull_isAntichain (a : PathSpace) : Antichain (hull a) :=
  fun _ hp _ hq h => hull_max hp (hull_subset a hq) h

theorem hull_of_antichain {a : PathSpace} (h : Antichain a) : Same (hull a) a := by
  intro p; rw [mem_hull]; constructor
  · exact And.left
  · intro hp; refine ⟨hp, ?_⟩
    intro q hq hn; cases he : p ≼ q with
    | false => rfl
    | true => exact False.elim (hn (h p hp q hq he).symm)

theorem retain_hull (a : PathSpace) : Same (retain a (hull a)) a := by
  intro p; rw [mem_retain]; exact ⟨And.left, fun hp => ⟨hp, hull_covers hp⟩⟩

theorem hull_retain {a t : PathSpace} (ht : Included t (hull a)) : Same (hull (retain a t)) t := by
  intro p; constructor
  · intro hp
    obtain ⟨ha, q, hq, hpq⟩ := (mem_retain a t p).mp (hull_subset _ hp)
    have hqm : q ∈ retain a t := (mem_retain _ _ _).mpr ⟨hull_subset _ (ht q hq), q, hq, Path.prefix_self q⟩
    have he := hull_max hp hqm hpq
    exact he ▸ hq
  · intro hp
    apply (mem_hull _ _).mpr
    refine ⟨(mem_retain _ _ _).mpr ⟨hull_subset _ (ht p hp), p, hp, Path.prefix_self p⟩, ?_⟩
    intro q hq hn
    exact ((mem_hull a p).mp (ht p hp)).2 q ((mem_retain _ _ _).mp hq).1 hn

theorem meet_tips_subset (a b : PathSpace) : Included (inter (hull a) (hull b)) (hull (inter a b)) := by
  intro p hp; obtain ⟨ha,hb⟩ := (mem_inter _ _ _).mp hp
  apply (mem_hull _ _).mpr
  exact ⟨(mem_inter _ _ _).mpr ⟨hull_subset _ ha, hull_subset _ hb⟩,
    fun q hq hn => ((mem_hull a p).mp ha).2 q ((mem_inter _ _ _).mp hq).1 hn⟩

theorem hull_convexMeet (a b : PathSpace) : Same (hull (convexMeet a b)) (inter (hull a) (hull b)) :=
  hull_retain (meet_tips_subset a b)

theorem hull_convexSubtract (a b : PathSpace) : Same (hull (convexSubtract a b)) (diff (hull a) b) :=
  hull_retain (fun _ h => ((mem_diff _ _ _).mp h).1)

theorem convexMeet_congr {a b c d : PathSpace} (h : Same a c) (k : Same b d) :
    Same (convexMeet a b) (convexMeet c d) := by
  intro p; simp only [mem_convexMeet, h, k, hull_congr h, hull_congr k]

theorem convexSubtract_congr {a b c d : PathSpace} (h : Same a c) (k : Same b d) :
    Same (convexSubtract a b) (convexSubtract c d) := by
  intro p; simp only [mem_convexSubtract, h, k, hull_congr h]

theorem convexMeet_subset (a b : PathSpace) : Included (convexMeet a b) (inter a b) := by
  intro p hp; have := (mem_convexMeet a b p).mp hp; exact (mem_inter _ _ _).mpr ⟨this.1,this.2.1⟩

theorem convexSubtract_subset (a b : PathSpace) : Included (convexSubtract a b) a :=
  fun p hp => ((mem_convexSubtract a b p).mp hp).1

theorem convexMeet_comm (a b : PathSpace) : Same (convexMeet a b) (convexMeet b a) := by
  intro p; simp only [mem_convexMeet]; grind

theorem convexMeet_idem (a : PathSpace) : Same (convexMeet a a) a := by
  intro p; simp only [mem_convexMeet]; constructor
  · rintro ⟨h,_⟩; exact h
  · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp; exact ⟨hp,hp,t,ht,ht,hpt⟩

theorem convexMeet_assoc (a b c : PathSpace) : Same (convexMeet (convexMeet a b) c) (convexMeet a (convexMeet b c)) := by
  intro p; simp only [mem_convexMeet, hull_convexMeet, mem_inter]; grind

theorem convexMeet_empty (a : PathSpace) : Same (convexMeet a []) [] := by
  intro p; simp [mem_convexMeet]

theorem convexSubtract_empty_right (a : PathSpace) : Same (convexSubtract a []) a := by
  intro p; simpa [convexSubtract, mem_retain, mem_diff] using retain_hull a p

theorem convexSubtract_empty_left (a : PathSpace) : Same (convexSubtract [] a) [] := by
  intro p; simp [mem_convexSubtract]

theorem convexSubtract_self (a : PathSpace) : Same (convexSubtract a a) [] := by
  intro p; simp only [mem_convexSubtract, List.not_mem_nil, iff_false]
  rintro ⟨_,t,ht,hn,_⟩; exact hn (hull_subset a ht)

theorem convexMeet_zero (a b : PathSpace) : Same (convexMeet a b) [] ↔ Same (inter (hull a) (hull b)) [] := by
  constructor
  · intro h p; have hh := (hull_convexMeet a b p).symm.trans (hull_congr h p)
    simpa only [hull, List.filter_nil] using hh
  · intro h p; simp only [convexMeet, mem_retain]; have := h; simp only [Same, List.not_mem_nil, iff_false] at this; grind

theorem convexSubtract_zero (a b : PathSpace) : Same (convexSubtract a b) [] ↔ Included (hull a) b := by
  constructor
  · intro h p hp
    have hh := hull_congr h p
    rw [hull_convexSubtract] at hh
    simp only [mem_diff, hull, List.filter_nil, List.not_mem_nil, iff_false] at hh
    by_cases hn : p ∈ b
    · exact hn
    · exact False.elim (hh ⟨hp,hn⟩)
  · intro h p; simp only [mem_convexSubtract, List.not_mem_nil, iff_false]; grind

theorem convexSubtract_identity (a b : PathSpace) : Same (convexSubtract a b) a ↔ Same (inter (hull a) b) [] := by
  constructor
  · intro h p
    have hh := hull_congr h p
    simp only [hull_convexSubtract,mem_diff] at hh
    simp only [mem_inter,List.not_mem_nil,iff_false]; grind
  · intro h p; rw [mem_convexSubtract]; constructor
    · exact And.left
    · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
      exact ⟨hp,t,ht,fun hb => List.not_mem_nil ((h t).mp ((mem_inter _ _ _).mpr ⟨ht,hb⟩)),hpt⟩

theorem convexMeet_ordinary (a b : PathSpace) : Same (convexMeet a b) (inter a b) ↔ Included (hull (inter a b)) (inter (hull a) (hull b)) := by
  constructor
  · intro h p hp; exact (hull_convexMeet a b p).mp ((hull_congr h p).mpr hp)
  · intro h p; rw [convexMeet,mem_retain]; constructor
    · exact And.left
    · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp; exact ⟨hp,t,h t ht,hpt⟩

theorem convexSubtract_masks (a b : PathSpace) :
    Same (convexSubtract a b) (convexSubtract a (inter a b)) ∧
    Same (convexSubtract a b) (convexSubtract a (inter (hull a) b)) := by
  constructor <;> intro p <;> simp only [mem_convexSubtract,mem_inter]
  · constructor
    · grind
    · rintro ⟨hp,t,ht,hn,hpt⟩; exact ⟨hp,t,ht,fun hb => hn ⟨hull_subset _ ht,hb⟩,hpt⟩
  · grind

theorem convexSubtract_action (a b c : PathSpace) : Same (convexSubtract (convexSubtract a b) c) (convexSubtract a (union b c)) := by
  intro p; simp only [mem_convexSubtract,hull_convexSubtract,mem_diff,union,List.mem_append]; grind

theorem convexSubtract_commute (a b c : PathSpace) : Same (convexSubtract (convexSubtract a b) c) (convexSubtract (convexSubtract a c) b) := by
  intro p; simp only [convexSubtract_action]; simp only [mem_convexSubtract,union,List.mem_append]; grind

theorem convexSubtract_idem (a b : PathSpace) : Same (convexSubtract (convexSubtract a b) b) (convexSubtract a b) := by
  intro p; simp only [convexSubtract_action]; simp only [mem_convexSubtract,union,List.mem_append,or_self]

theorem convexSubtract_redundant (a b c : PathSpace) : Same (convexSubtract (convexSubtract a b) c) (convexSubtract (convexSubtract a b) (diff c b)) := by
  intro p; simp only [convexSubtract_action]; simp only [mem_convexSubtract,union,List.mem_append,mem_diff]; grind

theorem convexSubtract_meet_left (a b c : PathSpace) : Same (convexSubtract (convexMeet a b) c) (convexMeet (convexSubtract a c) b) := by
  intro p; simp only [mem_convexSubtract,mem_convexMeet,hull_convexMeet,hull_convexSubtract,mem_inter,mem_diff]; grind

theorem convexSubtract_meet_right (a b c : PathSpace) : Same (convexSubtract (convexMeet a b) c) (convexMeet a (convexSubtract b c)) := by
  intro p; simp only [mem_convexSubtract,mem_convexMeet,hull_convexMeet,hull_convexSubtract,mem_inter,mem_diff]; grind

theorem convex_four_factor (a b c d : PathSpace) : Same (convexMeet (convexSubtract a b) (convexSubtract c d)) (convexSubtract (convexMeet a c) (union b d)) := by
  intro p; simp only [mem_convexSubtract,mem_convexMeet,hull_convexMeet,hull_convexSubtract,mem_inter,mem_diff,union,List.mem_append]; grind

theorem convexSubtract_meet_both (a b c : PathSpace) : Same (convexSubtract (convexMeet a b) c) (convexMeet (convexSubtract a c) (convexSubtract b c)) := by
  intro p; simp only [convex_four_factor,mem_convexSubtract,union,List.mem_append,or_self]

theorem convexSubtract_inter (a b c : PathSpace) : Same (convexSubtract a (inter b c)) (union (convexSubtract a b) (convexSubtract a c)) := by
  intro p; simp only [mem_convexSubtract,mem_inter,union,List.mem_append]; grind

theorem convexSubtract_union (a b c : PathSpace) : Same (convexSubtract a (union b c)) (convexMeet (convexSubtract a b) (convexSubtract a c)) := by
  intro p; rw [convex_four_factor]
  exact (convexSubtract_congr (convexMeet_idem a) (fun _ => Iff.rfl) p).symm

theorem convexSubtract_disjoint (a b : PathSpace) : Same (convexMeet (convexSubtract a b) b) [] := by
  intro p; simp only [mem_convexMeet,hull_convexSubtract,mem_diff,List.not_mem_nil,iff_false]
  rintro ⟨_,_,t,⟨_,hn⟩,ht,_⟩; exact hn (hull_subset _ ht)

theorem convexMeet_via_subtract (a b : PathSpace) : Same (convexMeet a b) (convexSubtract (inter a b) (diff (hull (inter a b)) (inter (hull a) (hull b)))) := by
  intro p; simp only [mem_convexMeet,mem_convexSubtract,mem_inter,mem_diff]
  have ht := meet_tips_subset a b
  simp only [Included,mem_inter] at ht
  grind

theorem convexMeet_hulls (a b : PathSpace) : Same (convexMeet (hull a) (hull b)) (inter (hull a) (hull b)) := by
  intro p; simp only [mem_convexMeet,hull_idempotent,mem_inter]
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,p,h.1,h.2,Path.prefix_self p⟩⟩

theorem convexSubtract_hull (a b : PathSpace) : Same (convexSubtract (hull a) b) (diff (hull a) b) := by
  intro p; simp only [mem_convexSubtract,hull_idempotent,mem_diff]
  constructor
  · rintro ⟨hp,t,ht,hn,hpt⟩; have he := hull_max hp (hull_subset _ ht) hpt; exact ⟨hp,he ▸ hn⟩
  · rintro ⟨hp,hn⟩; exact ⟨hp,p,hp,hn,Path.prefix_self p⟩

theorem convexMeet_empty_left (a : PathSpace) : Same (convexMeet [] a) [] :=
  fun p => (convexMeet_comm [] a p).trans (convexMeet_empty a p)

theorem convexSubtract_hull_disjoint (a b : PathSpace) :
    Same (inter (hull (convexSubtract a b)) b) [] := by
  intro p; simp only [mem_inter,hull_convexSubtract,mem_diff,List.not_mem_nil,iff_false]; grind

end PathMapModel.PathSpace
