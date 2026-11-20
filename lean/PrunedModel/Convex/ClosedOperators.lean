import PrunedModel.Convex.ClosedGeometry
/-! The exact corrections to the four completion bounds are proved in `CompletionGaps.lean`. -/
namespace PrunedModel.Convex
open PathMapModel

theorem closed_retain {a : PathSpace} (ha : IsClosed a) (b : PathSpace) : IsClosed (retain a b) := by
  intro x hx y hy
  obtain ⟨hx,u,hu,hxu⟩ := (mem_retain _ _ _).mp hx
  have hy := ((mem_retain _ _ _).mp hy).1
  exact (mem_retain _ _ _).mpr ⟨ha x hx y hy,u,hu,Path.prefix_trans (Path.lcp_prefix_left x y) hxu⟩

theorem closed_raffinate {a : PathSpace} (ha : IsClosed a) (b : PathSpace) : IsClosed (raffinate a b) := by
  intro x hx y hy
  obtain ⟨hx,hn⟩ := (mem_raffinate _ _ _).mp hx
  have hy := ((mem_raffinate _ _ _).mp hy).1
  apply (mem_raffinate _ _ _).mpr
  refine ⟨ha x hx y hy,fun q hq => ?_⟩
  cases he : q ≼ Path.lcp x y with
  | false => rfl
  | true =>
    have ht := Path.prefix_trans he (Path.lcp_prefix_left x y)
    have hf := hn q hq
    simp [ht] at hf

theorem closed_restrict {a b : PathSpace} (ha : IsClosed a) (hb : IsClosed b) :
    IsClosed (restrict a b) := by
  intro x hx y hy
  obtain ⟨hx,u,hu,hux⟩ := (mem_restrict _ _ _).mp hx
  obtain ⟨hy,v,hv,hvy⟩ := (mem_restrict _ _ _).mp hy
  exact (mem_restrict _ _ _).mpr ⟨ha x hx y hy,Path.lcp u v,hb u hu v hv,
    (Path.prefix_lcp _ _ _).mpr ⟨Path.prefix_trans (Path.lcp_prefix_left u v) hux,
      Path.prefix_trans (Path.lcp_prefix_right u v) hvy⟩⟩

/-- The exact correction when a restriction mask is not closed. -/
theorem completion_restrict (a b : PathSpace) :
    Same (completion (restrict a b))
      (union (restrict (completion a) b) (branches (retain b a))) := by
  intro p
  have hd := divergence_same_mask a a b p
  simp only [mem_completion, branches, hd]
  simp only [mem_union, mem_restrict, mem_completion, branches]
  grind

theorem completion_restrict_closed {b : PathSpace} (hb : IsClosed b) (a : PathSpace) :
    Same (completion (restrict a b)) (restrict (completion a) b) := by
  intro p; rw [completion_restrict]
  simp only [mem_union]
  constructor
  · rintro (h | h)
    · exact h
    · have hc : p ∈ completion (restrict a b) :=
        (mem_completion _ _).mpr (Or.inr ((divergence_same_mask a a b p).mpr (Or.inr h)))
      have ha := completion_mono (fun q hq => ((mem_restrict _ _ q).mp hq).1) p hc
      have hp := (closed_iff_branches _).mp (closed_retain hb a) p h
      exact (mem_restrict _ _ _).mpr ⟨ha,p,((mem_retain _ _ _).mp hp).1,Path.prefix_self p⟩
  · exact Or.inl

theorem completion_retain_bound (a b : PathSpace) :
    Included (completion (retain a b)) (retain (completion a) b) :=
  (completion_least (closed_retain (closed_completion a) b)).mpr
    (retain_mono (completion_extensive a) (fun _ h => h))

theorem completion_raffinate_bound (a b : PathSpace) :
    Included (completion (raffinate a b)) (raffinate (completion a) b) := by
  apply (completion_least (closed_raffinate (closed_completion a) b)).mpr
  intro p hp; obtain ⟨hp,hn⟩ := (mem_raffinate _ _ _).mp hp
  exact (mem_raffinate _ _ _).mpr ⟨completion_extensive a p hp,hn⟩

theorem closed_convexMeet {a b : PathSpace} (ha : IsClosed a) (hb : IsClosed b) :
    IsClosed (convexMeet a b) := closed_retain (closed_inter ha hb) _

theorem closed_convexSubtract {a : PathSpace} (ha : IsClosed a) (b : PathSpace) :
    IsClosed (convexSubtract a b) := closed_retain ha _

theorem completion_convexMeet_bound (a b : PathSpace) :
    Included (completion (convexMeet a b)) (convexMeet (completion a) (completion b)) := by
  apply (completion_least (closed_convexMeet (closed_completion a) (closed_completion b))).mpr
  intro p hp
  obtain ⟨ha,hb,t,hta,htb,hpt⟩ := (mem_convexMeet _ _ _).mp hp
  exact (mem_convexMeet _ _ _).mpr ⟨completion_extensive a p ha,completion_extensive b p hb,
    t,(hull_completion a t).mpr hta,(hull_completion b t).mpr htb,hpt⟩

theorem completion_convexSubtract_bound (a b : PathSpace) :
    Included (completion (convexSubtract a b)) (convexSubtract (completion a) b) := by
  apply (completion_least (closed_convexSubtract (closed_completion a) b)).mpr
  intro p hp
  obtain ⟨ha,t,ht,hn,hpt⟩ := (mem_convexSubtract _ _ _).mp hp
  exact (mem_convexSubtract _ _ _).mpr ⟨completion_extensive a p ha,t,(hull_completion a t).mpr ht,hn,hpt⟩

theorem hull_completion_convexMeet (a b : PathSpace) :
    Same (hull (completion (convexMeet a b))) (hull (convexMeet (completion a) (completion b))) := by
  intro p; simp only [hull_completion, hull_convexMeet, mem_inter]

theorem hull_completion_convexSubtract (a b : PathSpace) :
    Same (hull (completion (convexSubtract a b))) (hull (convexSubtract (completion a) b)) := by
  intro p; simp only [hull_completion, hull_convexSubtract, mem_diff]

theorem lcp_retain_bound (a b c d : PathSpace) :
    Included (lcpProduct (retain a c) (retain b d)) (retain (lcpProduct a b) (lcpProduct c d)) := by
  intro p hp
  obtain ⟨x,hx,y,hy,rfl⟩ := (mem_lcpProduct _ _ _).mp hp
  obtain ⟨hx,u,hu,hxu⟩ := (mem_retain _ _ _).mp hx
  obtain ⟨hy,v,hv,hyv⟩ := (mem_retain _ _ _).mp hy
  exact (mem_retain _ _ _).mpr ⟨(mem_lcpProduct _ _ _).mpr ⟨x,hx,y,hy,rfl⟩,
    Path.lcp u v,(mem_lcpProduct _ _ _).mpr ⟨u,hu,v,hv,rfl⟩,
    (Path.prefix_lcp _ _ _).mpr ⟨Path.prefix_trans (Path.lcp_prefix_left x y) hxu,
      Path.prefix_trans (Path.lcp_prefix_right x y) hyv⟩⟩

theorem lcp_inter_bound (a b c : PathSpace) :
    Included (lcpProduct (inter a b) c) (inter (lcpProduct a c) (lcpProduct b c)) := by
  intro p hp; exact (mem_inter _ _ _).mpr
    ⟨lcp_mono (fun q hq => ((mem_inter _ _ q).mp hq).1) (fun _ h => h) p hp,
     lcp_mono (fun q hq => ((mem_inter _ _ q).mp hq).2) (fun _ h => h) p hp⟩

theorem lcp_diff_bound (a b c : PathSpace) :
    Included (diff (lcpProduct a c) (lcpProduct b c)) (lcpProduct (diff a b) c) := by
  intro p hp; obtain ⟨hp,hn⟩ := (mem_diff _ _ _).mp hp
  obtain ⟨x,hx,y,hy,he⟩ := (mem_lcpProduct _ _ _).mp hp
  exact (mem_lcpProduct _ _ _).mpr ⟨x,(mem_diff _ _ _).mpr
    ⟨hx,fun hb => hn ((mem_lcpProduct _ _ _).mpr ⟨x,hb,y,hy,he⟩)⟩,y,hy,he⟩

/-- All genuinely new output marks are strict divergences. -/
theorem lcp_new_marks (a b : PathSpace) :
    Same (diff (lcpProduct a b) (union a b)) (diff (divergence a b) (union a b)) := by
  intro p; simp only [mem_diff, lcp_correction, mem_retain, mem_union]; grind

theorem lcp_union_bound (a b : PathSpace) : Included (lcpProduct a b) (completion (union a b)) := by
  intro p hp; obtain ⟨x,hx,y,hy,he⟩ := (mem_lcpProduct _ _ _).mp hp
  exact (completion_pair_witness _ _).mpr ⟨x,mem_union_left _ hx,y,mem_union_right _ hy,he⟩

theorem retain_lcp_operand (a b : PathSpace) : Same (retain a (lcpProduct a b)) (retain a b) := by
  intro p
  exact (retain_lcp_masks a a b p).symm.trans (retain_congr (retain_self a) (fun _ => Iff.rfl) p)

/-- Hulls of L-products are the canonical common retention masks. -/
theorem hull_lcp_hulls (a b : PathSpace) :
    Same (hull (lcpProduct (hull a) (hull b))) (hull (lcpProduct a b)) := by
  apply (retain_mask_equiv _ _).mp
  intro x p
  rw [← retain_lcp_masks, ← retain_lcp_masks]
  exact (retain_congr (retain_hull_mask x a) (fun _ => Iff.rfl) p).trans (retain_hull_mask _ b p)

/-- The L-product has its own semilattice order; this is not ordinary inclusion. -/
def LcpLE (a b : PathSpace) : Prop := Same (lcpProduct a b) a

theorem lcpLE_refl_iff (a : PathSpace) : LcpLE a a ↔ IsClosed a := by
  simp only [LcpLE, closed_iff_completion, Same, lcp_diagonal]

theorem lcpLE_closed {a b : PathSpace} (h : LcpLE a b) : IsClosed a :=
  (closed_congr h).mp (closed_lcp a b)

theorem lcpLE_antisymm {a b : PathSpace} (h : LcpLE a b) (k : LcpLE b a) : Same a b :=
  fun p => (h p).symm.trans ((lcp_symmetry a b p).trans (k p))

theorem lcpLE_trans {a b c : PathSpace} (h : LcpLE a b) (k : LcpLE b c) : LcpLE a c := by
  intro p
  exact (lcp_congr (fun q => (h q).symm) (fun _ => Iff.rfl) p).trans
    ((lcp_associativity a b c p).trans ((lcp_congr (fun _ => Iff.rfl) k p).trans (h p)))

theorem lcpLE_product_left (a b : PathSpace) : LcpLE (lcpProduct a b) a :=
  fun p => (lcp_symmetry _ _ p).trans (lcp_repeat a b p)

theorem lcpLE_product_right (a b : PathSpace) : LcpLE (lcpProduct a b) b := by
  intro p; rw [lcp_associativity]
  exact (lcp_congr (fun _ => Iff.rfl) (lcp_diagonal b) p).trans (lcp_completion_right a b p)

theorem lcpLE_product_iff (x a b : PathSpace) :
    LcpLE x (lcpProduct a b) ↔ LcpLE x a ∧ LcpLE x b := by
  constructor
  · intro h; exact ⟨lcpLE_trans h (lcpLE_product_left a b),lcpLE_trans h (lcpLE_product_right a b)⟩
  · rintro ⟨h,k⟩; intro p
    exact (lcp_associativity x a b p).symm.trans ((lcp_congr h (fun _ => Iff.rfl) p).trans (k p))

theorem lcpLE_empty (a : PathSpace) : LcpLE (ofPaths []) a := lcp_empty_left a

/-- Coverage alone is insufficient: both extra output contributions must already lie in A. -/
theorem lcpLE_iff (a b : PathSpace) : LcpLE a b ↔
    covers a b = true ∧ Included (divergence a b) a ∧ Included (retain b a) a := by
  constructor
  · intro h; refine ⟨?_,?_,?_⟩
    · apply (covers_iff a b).mpr
      intro p hp; exact lcp_output_covered ((lcp_symmetry a b p).mp ((h p).mpr hp))
    · intro p hp; exact (h p).mp ((lcp_correction a b p).mpr (Or.inl hp))
    · intro p hp; exact (h p).mp ((lcp_correction a b p).mpr (Or.inr (Or.inr hp)))
  · rintro ⟨hc,hd,ht⟩; intro p; rw [lcp_correction]; constructor
    · rintro (h | h | h)
      · exact hd p h
      · exact retain_subset a b p h
      · exact ht p h
    · intro hp; exact Or.inr (Or.inl ((retain_identity a b).mpr hc p |>.mpr hp))

/-- Restriction needs exactly the divergences between its retained mask paths. -/
theorem lcp_restrict (a b m : PathSpace) :
    Same (lcpProduct (restrict a m) (restrict b m))
      (union (restrict (lcpProduct a b) m) (divergence (retain m a) (retain m b))) := by
  intro p; constructor
  · intro hp
    rcases (lcp_correction _ _ p).mp hp with hd | ht | ht
    · rcases (divergence_same_mask a b m p).mp hd with hr | hr
      · obtain ⟨h,q,hq,hqp⟩ := (mem_restrict _ _ _).mp hr
        exact mem_union_left _ ((mem_restrict _ _ _).mpr
          ⟨(lcp_correction a b p).mpr (Or.inl h),q,hq,hqp⟩)
      · exact mem_union_right _ hr
    · obtain ⟨hr,y,hy,hpy⟩ := (mem_retain _ _ _).mp ht
      obtain ⟨ha,q,hq,hqp⟩ := (mem_restrict _ _ _).mp hr
      have hb := ((mem_restrict _ _ _).mp hy).1
      exact mem_union_left _ ((mem_restrict _ _ _).mpr
        ⟨(mem_lcpProduct _ _ _).mpr ⟨p,ha,y,hb,Path.lcp_of_prefix hpy⟩,q,hq,hqp⟩)
    · obtain ⟨hr,x,hx,hpx⟩ := (mem_retain _ _ _).mp ht
      obtain ⟨hb,q,hq,hqp⟩ := (mem_restrict _ _ _).mp hr
      have ha := ((mem_restrict _ _ _).mp hx).1
      exact mem_union_left _ ((mem_restrict _ _ _).mpr
        ⟨(mem_lcpProduct _ _ _).mpr ⟨x,ha,p,hb,(Path.lcp_comm x p).trans (Path.lcp_of_prefix hpx)⟩,q,hq,hqp⟩)
  · intro hp; rcases (mem_union _ _ _).mp hp with hr | hd
    · obtain ⟨hl,q,hq,hqp⟩ := (mem_restrict _ _ _).mp hr
      obtain ⟨x,hx,y,hy,rfl⟩ := (mem_lcpProduct _ _ _).mp hl
      obtain ⟨hqx,hqy⟩ := (Path.prefix_lcp _ _ _).mp hqp
      exact (mem_lcpProduct _ _ _).mpr ⟨x,(mem_restrict _ _ _).mpr ⟨hx,q,hq,hqx⟩,
        y,(mem_restrict _ _ _).mpr ⟨hy,q,hq,hqy⟩,rfl⟩
    · exact (lcp_correction _ _ p).mpr (Or.inl ((divergence_same_mask a b m p).mpr (Or.inr hd)))

theorem lcp_restrict_closed {m : PathSpace} (hm : IsClosed m) (a b : PathSpace) :
    Same (lcpProduct (restrict a m) (restrict b m)) (restrict (lcpProduct a b) m) := by
  intro p; rw [lcp_restrict]; constructor
  · intro hp; rcases (mem_union _ _ _).mp hp with hr | hd
    · exact hr
    · obtain ⟨x,hx,y,hy,he⟩ := (mem_divergence _ _ _).mp hd
      have hpm : p ∈ m := Path.divergence_lcp he ▸
        hm x ((mem_retain _ _ _).mp hx).1 y ((mem_retain _ _ _).mp hy).1
      have hl := (lcp_restrict a b m p).mpr (mem_union_right _ hd)
      have hs := lcp_mono (fun q hq => ((mem_restrict _ _ q).mp hq).1)
        (fun q hq => ((mem_restrict _ _ q).mp hq).1) p hl
      exact (mem_restrict _ _ _).mpr ⟨hs,p,hpm,Path.prefix_self p⟩
  · exact mem_union_left _

theorem completion_wrap (a : PathSpace) (q : Path) :
    Same (completion (wrap q a)) (wrap q (completion a)) := by
  intro p
  have hd := divergence_wrap a a q p
  simp only [mem_completion, branches, hd, mem_wrap]
  grind

theorem completion_unwrap (a : PathSpace) (q : Path) :
    Same (completion (unwrap a q)) (unwrap (completion a) q) := by
  intro p
  have hd := divergence_unwrap a a q p
  simp only [mem_completion, branches, hd, mem_unwrap]

theorem closed_join_comm (a b : PathSpace) :
    Same (completion (union a b)) (completion (union b a)) := by
  apply completion_congr; intro p; simp only [mem_union]; exact Or.comm

theorem closed_join_idem {a : PathSpace} (ha : IsClosed a) :
    Same (completion (union a a)) a := by
  have h : Same (union a a) a := by intro p; simp [union]
  exact fun p => (completion_congr h p).trans ((closed_iff_completion a).mp ha p)

theorem closed_join_empty {a : PathSpace} (ha : IsClosed a) :
    Same (completion (union a (ofPaths []))) a := by
  simpa only [ofPaths_nil, Zippy.union_empty] using (closed_iff_completion a).mp ha

end PrunedModel.Convex
