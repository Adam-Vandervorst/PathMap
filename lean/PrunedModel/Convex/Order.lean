import PrunedModel.Convex.Algebra

namespace PrunedModel.Convex
open PathMapModel

theorem convexLE_refl (a : PathSpace) : ConvexLE a a := ⟨fun _ h => h, fun _ h => h⟩
theorem convexLE_trans {a b c : PathSpace} (h : ConvexLE a b) (k : ConvexLE b c) : ConvexLE a c :=
  ⟨fun p hp => k.1 p (h.1 p hp),fun p hp => k.2 p (h.2 p hp)⟩
theorem convexLE_antisymm {a b : PathSpace} (h : ConvexLE a b) (k : ConvexLE b a) : Same a b :=
  fun p => ⟨h.1 p,k.1 p⟩

theorem convexLE_iff_meet (a b : PathSpace) : ConvexLE a b ↔ Same (convexMeet a b) a := by
  constructor
  · intro h p; rw [mem_convexMeet]; constructor
    · exact And.left
    · intro hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
      exact ⟨hp,h.1 p hp,t,ht,h.2 t ht,hpt⟩
  · intro h; constructor
    · intro p hp; exact ((mem_convexMeet _ _ _).mp ((h p).mpr hp)).2.1
    · intro p hp; exact ((mem_inter _ _ _).mp ((hull_convexMeet _ _ _).mp ((hull_congr h p).mpr hp))).2

theorem convexMeet_glb (x a b : PathSpace) : ConvexLE x (convexMeet a b) ↔ ConvexLE x a ∧ ConvexLE x b := by
  constructor
  · intro h
    have hs : Included x a ∧ Included x b := by
      constructor <;> intro p hp <;> have hh := (mem_convexMeet a b p).mp (h.1 p hp)
      · exact hh.1
      · exact hh.2.1
    have ht : Included (hull x) (hull a) ∧ Included (hull x) (hull b) := by
      constructor <;> intro p hp <;> have hh := (mem_inter _ _ _).mp ((hull_convexMeet a b p).mp (h.2 p hp))
      · exact hh.1
      · exact hh.2
    exact ⟨⟨hs.1,ht.1⟩,⟨hs.2,ht.2⟩⟩
  · rintro ⟨ha,hb⟩; constructor
    · intro p hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
      exact (mem_convexMeet _ _ _).mpr ⟨ha.1 p hp,hb.1 p hp,t,ha.2 t ht,hb.2 t ht,hpt⟩
    · intro p hp; exact (hull_convexMeet a b p).mpr ((mem_inter _ _ _).mpr ⟨ha.2 p hp,hb.2 p hp⟩)

theorem convexSubtract_universal (x a b : PathSpace) :
    ConvexLE x (convexSubtract a b) ↔ ConvexLE x a ∧ ∀ p ∈ hull x, p ∉ b := by
  constructor
  · intro h
    have ht : ∀ p ∈ hull x, p ∈ hull a ∧ p ∉ b := by
      intro p hp; exact (mem_diff _ _ _).mp ((hull_convexSubtract a b p).mp (h.2 p hp))
    exact ⟨⟨fun p hp => convexSubtract_subset a b p (h.1 p hp),fun p hp => (ht p hp).1⟩,fun p hp => (ht p hp).2⟩
  · rintro ⟨ha,hb⟩; constructor
    · intro p hp; obtain ⟨t,ht,hpt⟩ := hull_covers hp
      exact (mem_convexSubtract _ _ _).mpr ⟨ha.1 p hp,t,ha.2 t ht,hb t ht,hpt⟩
    · intro p hp; exact (hull_convexSubtract a b p).mpr ((mem_diff _ _ _).mpr ⟨ha.2 p hp,hb p hp⟩)

theorem convexMeet_mono {a b c d : PathSpace} (ha : ConvexLE a c) (hb : ConvexLE b d) : ConvexLE (convexMeet a b) (convexMeet c d) := by
  have h := (convexMeet_glb (convexMeet a b) a b).mp (convexLE_refl _)
  exact (convexMeet_glb _ _ _).mpr ⟨convexLE_trans h.1 ha,convexLE_trans h.2 hb⟩

theorem convexSubtract_deflationary (a b : PathSpace) : ConvexLE (convexSubtract a b) a :=
  ((convexSubtract_universal _ _ _).mp (convexLE_refl _)).1

theorem convexSubtract_mono {a c : PathSpace} (h : ConvexLE a c) (b : PathSpace) : ConvexLE (convexSubtract a b) (convexSubtract c b) := by
  have hh := (convexSubtract_universal _ _ _).mp (convexLE_refl (convexSubtract a b))
  exact (convexSubtract_universal _ _ _).mpr ⟨convexLE_trans hh.1 h,hh.2⟩

theorem convexSubtract_antitone (a : PathSpace) {b c : PathSpace} (h : Included b c) : ConvexLE (convexSubtract a c) (convexSubtract a b) := by
  have hh := (convexSubtract_universal _ _ _).mp (convexLE_refl (convexSubtract a c))
  exact (convexSubtract_universal _ _ _).mpr ⟨hh.1,fun p hp hb => hh.2 p hp (h p hb)⟩

theorem hull_union_compatible {a b : PathSpace} (h : Antichain (union (hull a) (hull b))) :
    Same (hull (union a b)) (union (hull a) (hull b)) :=
  fun p => (hull_union a b p).trans (hull_of_antichain h p)

theorem convex_union_lub {a b : PathSpace} (h : Antichain (union (hull a) (hull b))) (x : PathSpace) :
    ConvexLE (union a b) x ↔ ConvexLE a x ∧ ConvexLE b x := by
  simp only [ConvexLE,Included,mem_union]
  have hh := hull_union_compatible h
  simp only [Same,mem_union] at hh
  simp only [hh]
  grind

theorem convex_compatible (a b : PathSpace) :
    (∃ c, ConvexLE a c ∧ ConvexLE b c) ↔ Antichain (union (hull a) (hull b)) := by
  constructor
  · rintro ⟨c,ha,hb⟩ p hp q hq hpq
    have hh : Included (union (hull a) (hull b)) (hull c) := by
      intro t ht; rcases ((mem_union _ _ _).mp ht) with ht | ht
      · exact ha.2 t ht
      · exact hb.2 t ht
    exact hull_is_antichain c p (hh p hp) q (hh q hq) hpq
  · intro h; exact ⟨union a b,(convex_union_lub h _).mp (convexLE_refl _)⟩

/-- All Boolean operations on canonical prunings reduce to operations on tips. -/
theorem pruning_meet {a t u : PathSpace} (ht : Included t (hull a)) (hu : Included u (hull a)) :
    Same (convexMeet (retain a t) (retain a u)) (retain a (inter t u)) := by
  intro p; simp only [mem_convexMeet,hull_retain ht,hull_retain hu,mem_retain,mem_inter]; grind

theorem pruning_union (a t u : PathSpace) : Same (union (retain a t) (retain a u)) (retain a (union t u)) := by
  intro p; simp only [mem_union,mem_retain]; grind

theorem pruning_subtract {a t : PathSpace} (ht : Included t (hull a)) (b : PathSpace) :
    Same (convexSubtract (retain a t) b) (retain a (diff t b)) := by
  intro p; simp only [mem_convexSubtract,hull_retain ht,mem_retain,mem_diff]; grind

theorem pruning_complement {a t : PathSpace} (ht : Included t (hull a)) :
    Same (convexSubtract a (hull (retain a t))) (retain a (diff (hull a) t)) := by
  intro p; simp only [mem_convexSubtract,hull_retain ht,mem_retain,mem_diff]; grind

theorem pruning_order {a t u : PathSpace} (ht : Included t (hull a)) (hu : Included u (hull a)) :
    ConvexLE (retain a t) (retain a u) ↔ Included t u := by
  constructor
  · intro h p hp; exact (hull_retain hu p).mp (h.2 p ((hull_retain ht p).mpr hp))
  · intro h; constructor
    · intro p hp; obtain ⟨hp,q,hq,hpq⟩ := (mem_retain _ _ _).mp hp
      exact (mem_retain _ _ _).mpr ⟨hp,q,h q hq,hpq⟩
    · intro p hp; exact (hull_retain hu p).mpr (h p ((hull_retain ht p).mp hp))

theorem pruning_injective {a t u : PathSpace} (ht : Included t (hull a)) (hu : Included u (hull a)) :
    Same (retain a t) (retain a u) ↔ Same t u := by
  constructor
  · intro h p; exact (hull_retain ht p).symm.trans ((hull_congr h p).trans (hull_retain hu p))
  · intro h; exact retain_congr (fun _ => Iff.rfl) h

theorem pruning_bottom (a : PathSpace) : Same (retain a (ofPaths [])) (ofPaths []) := by intro p; simp [mem_retain]

theorem convexSubtract_faithful (b c : PathSpace) :
    (∀ a, Same (convexSubtract a b) (convexSubtract a c)) ↔ Same b c := by
  constructor
  · intro h p
    have hh := h [p] p
    simp [mem_convexSubtract,mem_hull] at hh
    have hs := Path.prefix_self p
    grind
  · intro h a; exact convexSubtract_congr (fun _ => Iff.rfl) h

/-- A nonempty meet; the first source prevents an artificial universal space. -/
def convexMeetMany (a : PathSpace) : List PathSpace → PathSpace
  | [] => a
  | b :: bs => convexMeet a (convexMeetMany b bs)
def interMany (a : PathSpace) : List PathSpace → PathSpace
  | [] => a
  | b :: bs => inter a (interMany b bs)

theorem mem_interMany (a : PathSpace) (bs : List PathSpace) (p : Path) :
    p ∈ interMany a bs ↔ p ∈ a ∧ ∀ b ∈ bs, p ∈ b := by
  induction bs generalizing a with
  | nil => simp [interMany]
  | cons b bs ih => simp only [interMany,mem_inter,ih,List.mem_cons]; grind

theorem hull_convexMeetMany (a : PathSpace) (bs : List PathSpace) :
    Same (hull (convexMeetMany a bs)) (interMany (hull a) (bs.map hull)) := by
  induction bs generalizing a with
  | nil => intro p; rfl
  | cons b bs ih => intro p; simp only [convexMeetMany,hull_convexMeet,mem_inter,List.map_cons,interMany,ih]

theorem convexMeetMany_normal (a : PathSpace) (bs : List PathSpace) :
    Same (convexMeetMany a bs) (retain (interMany a bs) (interMany (hull a) (bs.map hull))) := by
  induction bs generalizing a with
  | nil => exact fun p => (retain_hull a p).symm
  | cons b bs ih =>
    intro p
    simp only [convexMeetMany,mem_convexMeet,hull_convexMeetMany,ih,mem_retain,List.map_cons,interMany,mem_inter]
    grind

def unionMany (spaces : List PathSpace) : PathSpace := spaces.foldr union (ofPaths [])

theorem convex_normal_form (a : PathSpace) (bs masks : List PathSpace) :
    Same (convexSubtract (convexMeetMany a bs) (unionMany masks))
      (retain (interMany a bs) (diff (interMany (hull a) (bs.map hull)) (unionMany masks))) := by
  intro p; simp only [mem_convexSubtract,hull_convexMeetMany,convexMeetMany_normal,mem_retain,mem_diff]; grind

def convexSubtractMany (a : PathSpace) : List PathSpace → PathSpace
  | [] => a
  | b :: bs => convexSubtractMany (convexSubtract a b) bs

theorem convexSubtractMany_normal (a : PathSpace) (masks : List PathSpace) :
    Same (convexSubtractMany a masks) (convexSubtract a (unionMany masks)) := by
  induction masks generalizing a with
  | nil => exact fun p => (convexSubtract_empty_right a p).symm
  | cons b bs ih => intro p; exact (ih (convexSubtract a b) p).trans (convexSubtract_action a b (unionMany bs) p)

theorem convex_many_normal_form (a : PathSpace) (bs masks : List PathSpace) :
    Same (convexSubtractMany (convexMeetMany a bs) masks)
      (retain (interMany a bs) (diff (interMany (hull a) (bs.map hull)) (unionMany masks))) :=
  fun p => (convexSubtractMany_normal _ _ p).trans (convex_normal_form a bs masks p)

end PrunedModel.Convex
