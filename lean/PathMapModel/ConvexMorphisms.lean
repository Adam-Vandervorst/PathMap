import PathMapModel.ConvexGeometry

namespace PathMapModel.Path

theorem prefix_append_same (r p q : Path) : (r ++ p ≼ r ++ q) = (p ≼ q) := by
  induction r with
  | nil => rfl
  | cons c cs ih => simpa [isPrefixOf] using ih

theorem prefix_append (p q : Path) : (p ≼ p ++ q) = true :=
  (prefix_iff_extension _ _).mpr ⟨q,rfl⟩
end PathMapModel.Path

namespace PathMapModel.PathSpace

theorem mem_hull_max (a : PathSpace) (p : Path) :
    p ∈ hull a ↔ p ∈ a ∧ ∀ q ∈ a, (p ≼ q) = true → p = q := by
  constructor
  · intro h; exact ⟨hull_subset _ h,fun _ hq hpq => hull_max h hq hpq⟩
  · rintro ⟨hp,h⟩; rw [mem_hull]; refine ⟨hp,?_⟩
    intro q hq hn; cases he : p ≼ q with
    | false => rfl
    | true => exact False.elim (hn (h q hq he).symm)

theorem hull_unwrap (a : PathSpace) (r p : Path) : p ∈ hull (unwrap a r) ↔ r ++ p ∈ hull a := by
  simp only [mem_hull_max,mem_unwrap]; constructor
  · rintro ⟨hp,h⟩; refine ⟨hp,?_⟩
    intro q hq hpq
    have hrq := Path.prefix_trans (Path.prefix_append r p) hpq
    obtain ⟨s,rfl⟩ := (Path.prefix_iff_extension _ _).mp hrq
    have he := h s hq (by simpa only [Path.prefix_append_same] using hpq)
    exact congrArg (r ++ ·) he
  · rintro ⟨hp,h⟩; refine ⟨hp,?_⟩
    intro q hq hpq
    exact List.append_cancel_left (h (r ++ q) hq (by simpa only [Path.prefix_append_same] using hpq))

theorem live_unwrap (a t : PathSpace) (r p : Path) :
    p ∈ live (unwrap a r) (unwrap t r) ↔ r ++ p ∈ live a t := by
  simp only [mem_live,mem_unwrap]; constructor
  · rintro ⟨hp,q,hq,hpq⟩; exact ⟨hp,r ++ q,hq,by simpa only [Path.prefix_append_same] using hpq⟩
  · rintro ⟨hp,q,hq,hpq⟩
    obtain ⟨s,rfl⟩ := (Path.prefix_iff_extension _ _).mp (Path.prefix_trans (Path.prefix_append r p) hpq)
    exact ⟨hp,s,hq,by simpa only [Path.prefix_append_same] using hpq⟩

theorem convexMeet_unwrap (a b : PathSpace) (r : Path) :
    Same (unwrap (convexMeet a b) r) (convexMeet (unwrap a r) (unwrap b r)) := by
  intro p
  have he : Same (inter (unwrap a r) (unwrap b r)) (unwrap (inter a b) r) := by
    intro q; simp only [mem_inter,mem_unwrap]
  have ht : Same (inter (hull (unwrap a r)) (hull (unwrap b r))) (unwrap (inter (hull a) (hull b)) r) := by
    intro q; simp only [mem_inter,mem_unwrap,hull_unwrap]
  exact (mem_unwrap _ _ _).trans ((live_unwrap (inter a b) (inter (hull a) (hull b)) r p).symm.trans (live_congr he ht p).symm)

theorem convexSubtract_unwrap (a b : PathSpace) (r : Path) :
    Same (unwrap (convexSubtract a b) r) (convexSubtract (unwrap a r) (unwrap b r)) := by
  intro p
  have ht : Same (diff (hull (unwrap a r)) (unwrap b r)) (unwrap (diff (hull a) b) r) := by
    intro q; simp only [mem_diff,mem_unwrap,hull_unwrap]
  exact (mem_unwrap _ _ _).trans ((live_unwrap a (diff (hull a) b) r p).symm.trans (live_congr (fun _ => Iff.rfl) ht p).symm)

/-- Distinct prefix-code cones cannot interfere, even for empty suffixes. -/
theorem code_prefix {code : PathSpace} (hc : Antichain code) {r s : Path}
    (hr : r ∈ code) (hs : s ∈ code) (x y : Path) :
    (r ++ x ≼ s ++ y) = true ↔ r = s ∧ (x ≼ y) = true := by
  constructor
  · intro h
    have hh := Path.prefix_trans (Path.prefix_append r x) h
    have he : r = s := by
      rcases Path.prefixes_comparable hh (Path.prefix_append s y) with hrs | hsr
      · exact hc r hr s hs hrs
      · exact (hc s hs r hr hsr).symm
    subst s; exact ⟨rfl,by simpa only [Path.prefix_append_same] using h⟩
  · rintro ⟨rfl,h⟩; simpa only [Path.prefix_append_same] using h

theorem product_at {code : PathSpace} (hc : Antichain code) {r : Path} (hr : r ∈ code)
    (a : PathSpace) (p : Path) : r ++ p ∈ product code a ↔ p ∈ a := by
  rw [mem_product]; constructor
  · rintro ⟨s,hs,q,hq,he⟩
    have hh := (code_prefix hc hr hs p q).mp (he ▸ Path.prefix_self (r ++ p))
    have heq : r = s := hh.1; subst s
    have hqp := List.append_cancel_left he
    exact hqp ▸ hq
  · intro hp; exact ⟨r,hr,p,hp,rfl⟩

theorem hull_product_at {code : PathSpace} (hc : Antichain code) {r : Path} (hr : r ∈ code)
    (a : PathSpace) (p : Path) : r ++ p ∈ hull (product code a) ↔ p ∈ hull a := by
  simp only [mem_hull_max,product_at hc hr]; constructor
  · rintro ⟨hp,h⟩; refine ⟨hp,?_⟩
    intro q hq hpq
    exact List.append_cancel_left (h (r ++ q) ((product_at hc hr a q).mpr hq) (by simpa only [Path.prefix_append_same] using hpq))
  · rintro ⟨hp,h⟩; refine ⟨hp,?_⟩
    intro q hq hpq
    obtain ⟨s,hs,t,ht,rfl⟩ := (mem_product _ _ _).mp hq
    obtain ⟨rfl,hpt⟩ := (code_prefix hc hr hs p t).mp hpq
    exact congrArg (r ++ ·) (h t ht hpt)

theorem convexMeet_product_at {code : PathSpace} (hc : Antichain code) {r : Path} (hr : r ∈ code)
    (a b : PathSpace) (p : Path) : r ++ p ∈ convexMeet (product code a) (product code b) ↔ p ∈ convexMeet a b := by
  simp only [mem_convexMeet,product_at hc hr]; constructor
  · rintro ⟨ha,hb,t,ht,hu,hpt⟩
    obtain ⟨s,hs,q,hq,rfl⟩ := (mem_product _ _ _).mp (hull_subset _ ht)
    obtain ⟨rfl,hpq⟩ := (code_prefix hc hr hs p q).mp hpt
    exact ⟨ha,hb,q,(hull_product_at hc hs a q).mp ht,(hull_product_at hc hs b q).mp hu,hpq⟩
  · rintro ⟨ha,hb,t,ht,hu,hpt⟩
    exact ⟨ha,hb,r ++ t,(hull_product_at hc hr a t).mpr ht,(hull_product_at hc hr b t).mpr hu,by simpa only [Path.prefix_append_same] using hpt⟩

theorem convexSubtract_product_at {code : PathSpace} (hc : Antichain code) {r : Path} (hr : r ∈ code)
    (a b : PathSpace) (p : Path) : r ++ p ∈ convexSubtract (product code a) (product code b) ↔ p ∈ convexSubtract a b := by
  simp only [mem_convexSubtract,product_at hc hr]; constructor
  · rintro ⟨ha,t,ht,hn,hpt⟩
    obtain ⟨s,hs,q,hq,rfl⟩ := (mem_product _ _ _).mp (hull_subset _ ht)
    obtain ⟨rfl,hpq⟩ := (code_prefix hc hr hs p q).mp hpt
    exact ⟨ha,q,(hull_product_at hc hs a q).mp ht,fun hb => hn ((product_at hc hs b q).mpr hb),hpq⟩
  · rintro ⟨ha,t,ht,hn,hpt⟩
    exact ⟨ha,r ++ t,(hull_product_at hc hr a t).mpr ht,fun hb => hn ((product_at hc hr b t).mp hb),by simpa only [Path.prefix_append_same] using hpt⟩

theorem convexMeet_product {code : PathSpace} (hc : Antichain code) (a b : PathSpace) :
    Same (convexMeet (product code a) (product code b)) (product code (convexMeet a b)) := by
  intro p; constructor
  · intro hp
    obtain ⟨r,hr,q,_,rfl⟩ := (mem_product _ _ _).mp ((mem_convexMeet _ _ _).mp hp).1
    exact (product_at hc hr _ _).mpr ((convexMeet_product_at hc hr a b q).mp hp)
  · intro hp; obtain ⟨r,hr,q,hq,rfl⟩ := (mem_product _ _ _).mp hp
    exact (convexMeet_product_at hc hr a b q).mpr hq

theorem convexSubtract_product {code : PathSpace} (hc : Antichain code) (a b : PathSpace) :
    Same (convexSubtract (product code a) (product code b)) (product code (convexSubtract a b)) := by
  intro p; constructor
  · intro hp
    obtain ⟨r,hr,q,_,rfl⟩ := (mem_product _ _ _).mp ((mem_convexSubtract _ _ _).mp hp).1
    exact (product_at hc hr _ _).mpr ((convexSubtract_product_at hc hr a b q).mp hp)
  · intro hp; obtain ⟨r,hr,q,hq,rfl⟩ := (mem_product _ _ _).mp hp
    exact (convexSubtract_product_at hc hr a b q).mpr hq

theorem convexMeet_wrap (r : Path) (a b : PathSpace) : Same (convexMeet (wrap r a) (wrap r b)) (wrap r (convexMeet a b)) := by
  have hc : Antichain [r] := by intro p hp q hq _; simp only [List.mem_singleton] at hp hq; exact hp.trans hq.symm
  simpa only [product,List.flatMap_cons,List.flatMap_nil,List.append_nil,wrap] using convexMeet_product hc a b

theorem convexSubtract_wrap (r : Path) (a b : PathSpace) : Same (convexSubtract (wrap r a) (wrap r b)) (wrap r (convexSubtract a b)) := by
  have hc : Antichain [r] := by intro p hp q hq _; simp only [List.mem_singleton] at hp hq; exact hp.trans hq.symm
  simpa only [product,List.flatMap_cons,List.flatMap_nil,List.append_nil,wrap] using convexSubtract_product hc a b

end PathMapModel.PathSpace
