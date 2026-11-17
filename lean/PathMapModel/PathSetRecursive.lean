import PathMapModel.PathSetFork

namespace PathMapModel.PathSpace

theorem basis_nil (a : PathSpace) : [] ∈ basis a ↔ [] ∈ a := by
  rw [mem_basis]
  constructor
  · exact And.left
  · intro h; refine ⟨h,?_⟩; intro q hq hn
    cases q with
    | nil => exact False.elim (hn rfl)
    | cons c qs => rfl

theorem basis_cons (a : PathSpace) (c : UInt8) (p : Path) :
    c :: p ∈ basis a ↔ [] ∉ a ∧ p ∈ basis (unwrap a [c]) := by
  constructor
  · intro h
    have hm := (mem_basis _ _).mp h
    refine ⟨?_,(mem_basis _ _).mpr ⟨(mem_unwrap _ _ _).mpr hm.1,?_⟩⟩
    · intro hn
      have hf := hm.2 [] hn (by simp)
      simp [Path.isPrefixOf] at hf
    · intro q hq hn
      have hf := hm.2 (c::q) ((mem_unwrap _ _ _).mp hq) (by simpa using hn)
      simpa [Path.isPrefixOf] using hf
  · rintro ⟨hn,h⟩
    have hm := (mem_basis _ _).mp h
    refine (mem_basis _ _).mpr ⟨(mem_unwrap _ _ _).mp hm.1,?_⟩
    intro q hq hne
    cases q with
    | nil => exact False.elim (hn hq)
    | cons d qs =>
      by_cases hd : d = c
      · subst d
        have hf := hm.2 qs ((mem_unwrap _ _ _).mpr hq) (by simpa using hne)
        simpa [Path.isPrefixOf] using hf
      · simp [Path.isPrefixOf,hd]

theorem hull_cons (a : PathSpace) (c : UInt8) (p : Path) :
    c :: p ∈ hull a ↔ p ∈ hull (unwrap a [c]) := by
  constructor
  · intro h
    have hm := (mem_hull _ _).mp h
    refine (mem_hull _ _).mpr ⟨(mem_unwrap _ _ _).mpr hm.1,?_⟩
    intro q hq hn
    have hf := hm.2 (c::q) ((mem_unwrap _ _ _).mp hq) (by simpa using hn)
    simpa [Path.isPrefixOf] using hf
  · intro h
    have hm := (mem_hull _ _).mp h
    refine (mem_hull _ _).mpr ⟨(mem_unwrap _ _ _).mp hm.1,?_⟩
    intro q hq hne
    cases q with
    | nil => rfl
    | cons d qs =>
      by_cases hd : d = c
      · subst d
        have hf := hm.2 qs ((mem_unwrap _ _ _).mpr hq) (by simpa using hne)
        simpa [Path.isPrefixOf] using hf
      · simp [Path.isPrefixOf,Ne.symm hd]

theorem head_empty (a : PathSpace) : head a = [] ↔ ∀ p ∈ a, p = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h p hp
    cases p with
    | nil => rfl
    | cons c ps => exact False.elim (h [c] ((mem_head _ _).mpr ⟨c,rfl,ps,hp⟩))
  · intro h p hp
    obtain ⟨c,rfl,ps,hp⟩ := (mem_head _ _).mp hp
    have hh := h (c::ps) hp
    simp at hh

theorem hull_nil (a : PathSpace) : [] ∈ hull a ↔ [] ∈ a ∧ head a = [] := by
  rw [mem_hull,head_empty]
  simp only [Path.isPrefixOf]
  grind

theorem live_nil (m a : PathSpace) : [] ∈ live m a ↔ [] ∈ m ∧ a ≠ [] := by
  cases a <;> simp [live,Path.isPrefixOf]

theorem live_cons (m a : PathSpace) (c : UInt8) (p : Path) :
    c :: p ∈ live m a ↔ p ∈ live (unwrap m [c]) (unwrap a [c]) := by
  simp only [mem_live,mem_unwrap,List.singleton_append]
  constructor
  · rintro ⟨hp,q,hq,he⟩
    cases q with
    | nil => simp [Path.isPrefixOf] at he
    | cons d qs =>
      simp only [Path.isPrefixOf,Bool.and_eq_true,beq_iff_eq] at he
      obtain ⟨rfl,he⟩ := he
      exact ⟨hp,qs,hq,he⟩
  · rintro ⟨hp,q,hq,he⟩
    exact ⟨hp,c::q,hq,by simpa [Path.isPrefixOf] using he⟩

theorem child_of_unwrap {a : PathSpace} {c : UInt8} {p : Path}
    (h : p ∈ unwrap a [c]) : Child a [] c := ⟨p,(mem_unwrap a [c] p).mp h⟩

theorem mem_head_expansion (a : PathSpace) (f : Path → PathSpace) (p : Path) :
    p ∈ (normalize (head a)).flatMap (fun q => wrap q (f q)) ↔
    ∃ c r, Child a [] c ∧ r ∈ f [c] ∧ c :: r = p := by
  simp only [List.mem_flatMap,mem_normalize,mem_head,mem_wrap]
  constructor
  · rintro ⟨q,⟨c,rfl,hc⟩,r,hr,rfl⟩; exact ⟨c,r,hc,hr,rfl⟩
  · rintro ⟨c,r,hc,hr,rfl⟩; exact ⟨[c],⟨c,rfl,hc⟩,r,hr,rfl⟩

theorem mem_common_head_expansion (a b : PathSpace) (f : Path → PathSpace) (p : Path) :
    p ∈ (inter (normalize (head a)) (normalize (head b))).flatMap (fun q => wrap q (f q)) ↔
    ∃ c r, Child a [] c ∧ Child b [] c ∧ r ∈ f [c] ∧ c :: r = p := by
  simp only [List.mem_flatMap,mem_inter,mem_normalize,mem_head,mem_wrap]
  constructor
  · rintro ⟨q,⟨⟨c,rfl,hc⟩,⟨d,hd,hd'⟩⟩,r,hr,rfl⟩
    have he : c = d := by simpa using hd
    subst d; exact ⟨c,r,hc,hd',hr,rfl⟩
  · rintro ⟨c,r,hc,hd,hr,rfl⟩; exact ⟨[c],⟨⟨c,rfl,hc⟩,⟨c,rfl,hd⟩⟩,r,hr,rfl⟩

theorem mem_live_head_expansion (a b : PathSpace) (f : Path → PathSpace) (p : Path) :
    p ∈ (normalize (inter (head a) (head b))).flatMap (fun q => wrap q (f q)) ↔
    ∃ c r, Child a [] c ∧ Child b [] c ∧ r ∈ f [c] ∧ c :: r = p := by
  simp only [List.mem_flatMap,mem_inter,mem_normalize,mem_head,mem_wrap]
  constructor
  · rintro ⟨q,⟨⟨c,rfl,hc⟩,⟨d,hd,hd'⟩⟩,r,hr,rfl⟩
    have he : c = d := by simpa using hd
    subst d; exact ⟨c,r,hc,hd',hr,rfl⟩
  · rintro ⟨c,r,hc,hd,hr,rfl⟩; exact ⟨[c],⟨⟨c,rfl,hc⟩,⟨c,rfl,hd⟩⟩,r,hr,rfl⟩

theorem divergence_root_test (a b : PathSpace) :
    ((normalize (head a)).any (fun x => (normalize (head b)).any (· != x))) = true ↔
    [] ∈ divergence a b := by
  simp only [List.any_eq_true,mem_normalize,mem_head,mem_divergence_children,bne_iff_ne]
  constructor
  · rintro ⟨x,⟨c,rfl,hc⟩,y,⟨d,rfl,hd⟩,hne⟩
    exact ⟨c,d,by simpa [Ne,eq_comm] using hne,hc,hd⟩
  · rintro ⟨c,d,hne,hc,hd⟩
    exact ⟨[c],⟨c,rfl,hc⟩,[d],⟨d,rfl,hd⟩,by simpa [Ne,eq_comm] using hne⟩

theorem basisRec_spec (n : Nat) (a : PathSpace) (p : Path) :
    p ∈ basisRec n a ↔ p ∈ basis a ∧ p.length < n := by
  induction n generalizing a p with
  | zero => simp [basisRec]
  | succ n ih =>
    rw [basisRec]
    by_cases he : [] ∈ a
    · simp only [List.contains_iff_mem.mpr he,if_true,List.mem_singleton]
      cases p with
      | nil => simp [basis_nil,he]
      | cons c ps => simp [basis_cons,he]
    · have hb : a.contains [] = false := by simpa using he
      simp only [hb,Bool.false_eq_true,if_false,mem_head_expansion]
      cases p with
      | nil => simp [basis_nil,he]
      | cons c ps =>
        simp only [List.cons.injEq,ih,List.length_cons,basis_cons,he,not_false_eq_true,true_and]
        constructor
        · rintro ⟨c',r,hc,⟨hp,hl⟩,rfl,rfl⟩; exact ⟨hp,by omega⟩
        · rintro ⟨hp,hl⟩; exact ⟨c,ps,child_of_unwrap (basis_subset _ hp),⟨hp,by omega⟩,rfl,rfl⟩

theorem hullRec_spec (n : Nat) (a : PathSpace) (p : Path) :
    p ∈ hullRec n a ↔ p ∈ hull a ∧ p.length < n := by
  induction n generalizing a p with
  | zero => simp [hullRec]
  | succ n ih =>
    simp only [hullRec,List.mem_append,mem_head_expansion]
    by_cases he : (a.contains [] && (head a).isEmpty) = true
    · have hh : [] ∈ a ∧ head a = [] := by simpa using he
      simp only [he]
      simp only [if_true]
      cases p with
      | nil => simp [hull_nil,hh]
      | cons c ps =>
        simp only [List.mem_singleton,List.cons_ne_nil,false_or,List.cons.injEq,ih,List.length_cons,hull_cons]
        exact ⟨fun ⟨_,_,_,⟨hp,hl⟩,rfl,rfl⟩ => ⟨hp,by omega⟩,
          fun ⟨hp,hl⟩ => ⟨c,ps,child_of_unwrap (hull_subset _ hp),⟨hp,by omega⟩,rfl,rfl⟩⟩
    · have hb : (a.contains [] && (head a).isEmpty) = false := by simpa using he
      simp only [hb,Bool.false_eq_true,if_false]
      cases p with
      | nil => simp [hull_nil]; simpa using he
      | cons c ps =>
        simp only [List.not_mem_nil,false_or,List.cons.injEq,ih,List.length_cons,hull_cons]
        exact ⟨fun ⟨_,_,_,⟨hp,hl⟩,rfl,rfl⟩ => ⟨hp,by omega⟩,
          fun ⟨hp,hl⟩ => ⟨c,ps,child_of_unwrap (hull_subset _ hp),⟨hp,by omega⟩,rfl,rfl⟩⟩

theorem divergenceRec_spec (n : Nat) (a b : PathSpace) (p : Path) :
    p ∈ divergenceRec n a b ↔ p ∈ divergence a b ∧ p.length < n := by
  induction n generalizing a b p with
  | zero => simp [divergenceRec]
  | succ n ih =>
    simp only [divergenceRec,List.mem_append,mem_common_head_expansion]
    by_cases he : (normalize (head a)).any (fun x => (normalize (head b)).any (· != x)) = true
    · simp only [he]
      simp only [if_true]
      cases p with
      | nil => simp [(divergence_root_test a b).mp he]
      | cons c ps =>
        simp only [List.mem_singleton,List.cons_ne_nil,false_or,List.cons.injEq,ih,List.length_cons]
        have hun := divergence_unwrap a b [c] ps
        simp only [List.singleton_append] at hun
        rw [← hun]
        constructor
        · rintro ⟨_,_,_,_,⟨hp,hl⟩,rfl,rfl⟩; exact ⟨hp,by omega⟩
        · rintro ⟨hp,hl⟩
          obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
          exact ⟨c,ps,child_of_unwrap hx,child_of_unwrap hy,⟨hp,by omega⟩,rfl,rfl⟩
    · have hb : (normalize (head a)).any (fun x => (normalize (head b)).any (· != x)) = false := by simpa using he
      simp only [hb,Bool.false_eq_true,if_false]
      cases p with
      | nil => simp; exact fun h => he ((divergence_root_test a b).mpr h)
      | cons c ps =>
        simp only [List.not_mem_nil,false_or,List.cons.injEq,ih,List.length_cons]
        have hun := divergence_unwrap a b [c] ps
        simp only [List.singleton_append] at hun
        rw [← hun]
        constructor
        · rintro ⟨_,_,_,_,⟨hp,hl⟩,rfl,rfl⟩; exact ⟨hp,by omega⟩
        · rintro ⟨hp,hl⟩
          obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
          exact ⟨c,ps,child_of_unwrap hx,child_of_unwrap hy,⟨hp,by omega⟩,rfl,rfl⟩

theorem liveRec_spec (n : Nat) (m a : PathSpace) (p : Path) :
    p ∈ liveRec n m a ↔ p ∈ live m a ∧ p.length < n := by
  induction n generalizing m a p with
  | zero => simp [liveRec]
  | succ n ih =>
    simp only [liveRec,List.mem_append,mem_live_head_expansion]
    by_cases he : (m.contains [] && !a.isEmpty) = true
    · have hh : [] ∈ live m a := (live_nil m a).mpr (by simpa using he)
      simp only [he]
      simp only [if_true]
      cases p with
      | nil => simp [hh]
      | cons c ps =>
        simp only [List.mem_singleton,List.cons_ne_nil,false_or,List.cons.injEq,ih,List.length_cons,live_cons]
        constructor
        · rintro ⟨_,_,_,_,⟨hp,hl⟩,rfl,rfl⟩; exact ⟨hp,by omega⟩
        · rintro ⟨hp,hl⟩
          obtain ⟨hm,q,hq,_⟩ := (mem_live _ _ _).mp hp
          exact ⟨c,ps,child_of_unwrap hm,child_of_unwrap hq,⟨hp,by omega⟩,rfl,rfl⟩
    · have hb : (m.contains [] && !a.isEmpty) = false := by simpa using he
      simp only [hb,Bool.false_eq_true,if_false]
      cases p with
      | nil => simp [live_nil]; simpa using he
      | cons c ps =>
        simp only [List.not_mem_nil,false_or,List.cons.injEq,ih,List.length_cons,live_cons]
        constructor
        · rintro ⟨_,_,_,_,⟨hp,hl⟩,rfl,rfl⟩; exact ⟨hp,by omega⟩
        · rintro ⟨hp,hl⟩
          obtain ⟨hm,q,hq,_⟩ := (mem_live _ _ _).mp hp
          exact ⟨c,ps,child_of_unwrap hm,child_of_unwrap hq,⟨hp,by omega⟩,rfl,rfl⟩

theorem basis_recursive (a : PathSpace) (p : Path) :
    p ∈ basisRec (height a + 1) a ↔ p ∈ basis a := by
  rw [basisRec_spec]
  exact ⟨And.left,fun h => ⟨h,Nat.lt_succ_of_le (length_le_height (basis_subset a h))⟩⟩

theorem hull_recursive (a : PathSpace) (p : Path) :
    p ∈ hullRec (height a + 1) a ↔ p ∈ hull a := by
  rw [hullRec_spec]
  exact ⟨And.left,fun h => ⟨h,Nat.lt_succ_of_le (length_le_height (hull_subset a h))⟩⟩

theorem divergence_recursive (a b : PathSpace) (p : Path) :
    p ∈ divergenceRec (min (height a) (height b) + 1) a b ↔ p ∈ divergence a b := by
  rw [divergenceRec_spec]
  constructor
  · exact And.left
  · intro h
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    have hpx := Path.divergence_length_left hd
    have hpy := Path.divergence_length_right hd
    have hax := length_le_height hx
    have hby := length_le_height hy
    exact ⟨h,by omega⟩

theorem branch_recursive (a : PathSpace) (p : Path) :
    p ∈ divergenceRec (height a + 1) a a ↔ p ∈ branches a := by
  simpa [branches] using divergence_recursive a a p

theorem live_recursive (m a : PathSpace) (p : Path) :
    p ∈ liveRec (height m + 1) m a ↔ p ∈ live m a := by
  rw [liveRec_spec]
  exact ⟨And.left,fun h => ⟨h,Nat.lt_succ_of_le (length_le_height ((mem_live _ _ _).mp h).1)⟩⟩
end PathMapModel.PathSpace
