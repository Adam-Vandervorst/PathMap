import PathMapModel.ConvexOrder

namespace PathMapModel.PathSpace

/-- Remove every currently exposed, unprotected tip. -/
def convexPruneStep (x tips : PathSpace) : PathSpace := diff x (diff (hull x) tips)
def convexPrune (tips : PathSpace) : Nat → PathSpace → PathSpace
  | 0, x => x
  | n + 1, x => convexPruneStep (convexPrune tips n x) tips

theorem mem_pruneStep (x tips : PathSpace) (p : Path) :
    p ∈ convexPruneStep x tips ↔ p ∈ x ∧ (p ∈ tips ∨ ∃ q ∈ x, p ≠ q ∧ (p ≼ q) = true) := by
  simp only [convexPruneStep,mem_diff,mem_hull]; grind

theorem prune_subset (tips : PathSpace) (n : Nat) (x : PathSpace) : Included (convexPrune tips n x) x := by
  induction n with
  | zero => exact fun _ h => h
  | succ n ih => intro p hp; exact ih p ((mem_pruneStep _ _ _).mp hp).1

theorem prune_protected {tips x : PathSpace} (ht : Included tips x) (n : Nat) : Included tips (convexPrune tips n x) := by
  induction n with
  | zero => exact ht
  | succ n ih => intro p hp; exact (mem_pruneStep _ _ _).mpr ⟨ih p hp,Or.inl hp⟩

theorem prune_preserves_live {tips x : PathSpace} (ht : Included tips x) (n : Nat) :
    Included (live x tips) (convexPrune tips n x) := by
  induction n with
  | zero => intro p hp; exact ((mem_live _ _ _).mp hp).1
  | succ n ih =>
    intro p hp; obtain ⟨_,t,htip,hpt⟩ := (mem_live _ _ _).mp hp
    apply (mem_pruneStep _ _ _).mpr; refine ⟨ih p hp,?_⟩
    by_cases he : p = t
    · exact Or.inl (he ▸ htip)
    · exact Or.inr ⟨t,prune_protected ht n t htip,he,hpt⟩

/-- Every unsupported survivor forces a chain at least n symbols longer. -/
theorem prune_unsupported_length (tips x : PathSpace) (n : Nat) {p : Path}
    (hp : p ∈ convexPrune tips n x) (hn : ¬ ∃ t ∈ tips, (p ≼ t) = true) :
    p.length + n ≤ height x := by
  induction n generalizing p with
  | zero => simpa only [convexPrune, Nat.add_zero] using length_le_height hp
  | succ n ih =>
    obtain ⟨_,ht | ⟨q,hq,hne,hpq⟩⟩ := (mem_pruneStep _ _ _).mp hp
    · exact False.elim (hn ⟨p,ht,Path.prefix_self p⟩)
    · have hqn : ¬ ∃ t ∈ tips, (q ≼ t) = true := by
        rintro ⟨t,ht,hqt⟩; exact hn ⟨t,ht,Path.prefix_trans hpq hqt⟩
      have hi := ih hq hqn
      have hl := Path.prefix_length hpq
      have hs : p.length < q.length := by
        by_cases h : q.length ≤ p.length
        · exact False.elim (hne (Path.prefix_eq_of_length hpq h))
        · omega
      omega

/-- A uniform height bound, valid even when the protected set is not maximal. -/
theorem convexPrune_stable {tips x : PathSpace} (ht : Included tips x) {n : Nat}
    (hn : height x < n) : Same (convexPrune tips n x) (live x tips) := by
  intro p; constructor
  · intro hp
    have hx := prune_subset tips n x p hp
    by_cases he : ∃ t ∈ tips, (p ≼ t) = true
    · exact (mem_live _ _ _).mpr ⟨hx,he⟩
    · have hh := prune_unsupported_length tips x n hp he; omega
  · exact prune_preserves_live ht n p

theorem live_prune_fixed {tips x : PathSpace} (ht : Included tips x) :
    Same (convexPruneStep (live x tips) tips) (live x tips) := by
  intro p; rw [mem_pruneStep]; constructor
  · exact And.left
  · intro hp; obtain ⟨_,t,htip,hpt⟩ := (mem_live _ _ _).mp hp
    refine ⟨hp,?_⟩
    by_cases he : p = t
    · exact Or.inl (he ▸ htip)
    · exact Or.inr ⟨t,(mem_live _ _ _).mpr ⟨ht t htip,t,htip,Path.prefix_self t⟩,he,hpt⟩

/-- Asynchronous pruning may remove any collection of exposed unprotected tips. -/
def PruneMove (tips x y : PathSpace) : Prop :=
  Included y x ∧ Included (convexPruneStep x tips) y
inductive PruneTrace (tips : PathSpace) : PathSpace → PathSpace → Prop
  | refl (x) : PruneTrace tips x x
  | step {x y z} : PruneTrace tips x y → PruneMove tips y z → PruneTrace tips x z

theorem pruneMove_live {tips x y : PathSpace} (ht : Included tips x)
    (h : PruneMove tips x y) : Same (live x tips) (live y tips) := by
  intro p; rw [mem_live,mem_live]; constructor
  · rintro ⟨hp,t,hti,hpt⟩
    refine ⟨h.2 p ((mem_pruneStep _ _ _).mpr ⟨hp,?_⟩),t,hti,hpt⟩
    by_cases he : p = t
    · exact Or.inl (he ▸ hti)
    · exact Or.inr ⟨t,ht t hti,he,hpt⟩
  · rintro ⟨hp,t,hti,hpt⟩; exact ⟨h.1 p hp,t,hti,hpt⟩

theorem pruneTrace_invariant {tips x y : PathSpace} (ht : Included tips x)
    (h : PruneTrace tips x y) : Included tips y ∧ Same (live x tips) (live y tips) := by
  induction h with
  | refl => exact ⟨ht,fun _ => Iff.rfl⟩
  | step h hm ih =>
    refine ⟨?_,fun p => (ih.2 p).trans (pruneMove_live ih.1 hm p)⟩
    intro p hp; exact hm.2 p ((mem_pruneStep _ _ _).mpr ⟨ih.1 p hp,Or.inl hp⟩)

theorem prune_fixed_iff (tips x : PathSpace) :
    Same (convexPruneStep x tips) x → Same x (live x tips) := by
  intro h p; rw [mem_live]; constructor
  · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
    have hh := (mem_pruneStep _ _ _).mp ((h t).mpr (hull_subset _ ht))
    rcases hh.2 with htip | ⟨q,hq,hne,htq⟩
    · exact ⟨hp,t,htip,hpt⟩
    · exact False.elim (hne (hull_max ht hq htq))
  · exact And.left

/-- Every terminal result of arbitrary tip-removal order is the same closed form. -/
theorem convexPrune_confluent {tips x y : PathSpace} (ht : Included tips x)
    (h : PruneTrace tips x y) (hf : Same (convexPruneStep y tips) y) :
    Same y (live x tips) := by
  intro p; exact (prune_fixed_iff tips y hf p).trans ((pruneTrace_invariant ht h).2 p).symm

/-- Every effective asynchronous deletion strictly decreases finite cardinality. -/
theorem pruneMove_decreases {tips x y : PathSpace} (h : PruneMove tips x y)
    (hn : ¬ Same x y) : count y < count x := by
  classical
  have hex : ∃ p, p ∈ x ∧ p ∉ y := by
    have hs := h.1
    grind
  obtain ⟨p,hp,hpn⟩ := hex
  have hf : y.filter (fun q => !q == p) = y := by
    apply List.filter_eq_self.mpr
    intro q hq
    have he : q ≠ p := fun he => hpn (he ▸ hq)
    simp [he]
  have hc : count (p :: y) = count y + 1 := by simp only [count,List.eraseDups_cons,hf,List.length_cons]
  have hl : count (p :: y) ≤ count x := count_mono (by
    intro q hq; rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact h.1 q hq)
  omega

/-- Synchronous pruning is one permitted asynchronous schedule. -/
theorem convexPrune_trace (tips x : PathSpace) (n : Nat) : PruneTrace tips x (convexPrune tips n x) := by
  induction n with
  | zero => exact .refl x
  | succ n ih =>
    exact .step ih ⟨fun p hp => ((mem_pruneStep _ _ _).mp hp).1,fun _ h => h⟩

/-- Every reachable state has a bounded continuation to the same normal form. -/
theorem convexPrune_join {tips x y : PathSpace} (ht : Included tips x) (h : PruneTrace tips x y) :
    Same (convexPrune tips (height y + 1) y) (live x tips) := by
  have hi := pruneTrace_invariant ht h
  intro p; exact (convexPrune_stable hi.1 (Nat.lt_succ_self _) p).trans (hi.2 p).symm

def convexMeetRec (a b : PathSpace) : PathSpace :=
  convexPrune (inter (hull a) (hull b)) (height (inter a b) + 1) (inter a b)
def convexSubtractRec (a b : PathSpace) : PathSpace :=
  let x := diff a (inter (hull a) b)
  convexPrune (diff (hull a) b) (height x + 1) x

theorem convexMeetRec_correct (a b : PathSpace) : Same (convexMeetRec a b) (convexMeet a b) :=
  convexPrune_stable (fun p hp => hull_subset _ (meet_tips_subset a b p hp)) (Nat.lt_succ_self _)

theorem convexSubtractRec_correct (a b : PathSpace) : Same (convexSubtractRec a b) (convexSubtract a b) := by
  have ht : Included (diff (hull a) b) (diff a (inter (hull a) b)) := by
    intro p hp; obtain ⟨hh,hn⟩ := (mem_diff _ _ _).mp hp
    exact (mem_diff _ _ _).mpr ⟨hull_subset a hh,fun hi => hn ((mem_inter _ _ _).mp hi).2⟩
  intro p
  have hh := convexPrune_stable ht (Nat.lt_succ_self (height (diff a (inter (hull a) b)))) p
  apply hh.trans
  simp only [mem_live,mem_diff,mem_inter,mem_convexSubtract]
  constructor
  · grind
  · rintro ⟨hp,t,htip,hn,hpt⟩
    refine ⟨⟨hp,?_⟩,t,⟨htip,hn⟩,hpt⟩
    rintro ⟨hh,hb⟩
    exact hn ((hull_max hh (hull_subset a htip) hpt) ▸ hb)

end PathMapModel.PathSpace
