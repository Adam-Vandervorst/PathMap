import PrunedModel.Write
import PrunedModel.Pointwise

/-!
# What each write operation does to the trie

Every write operation in `Write.lean` touches the trie only at and below the
focus.  This file proves that, operation by operation, in one shape:

    (z.op …).2 = z.withTrie (z.trie.replaceAt z.focus M)

where `replaceAt t f M` is `t` with everything at and below `f` replaced by the
map `M` (root value included), and `M` is named: `join ops z.makeMap m` for
`join_map_into`, `meet ops z.makeMap src.makeMap` for `meet_into`, and so on.

That one equation says two things at once:

* **frame** — nothing outside the focus's subtrie changes, and the cursor does
  not move;
* **refinement** — read back at the focus (`makeMap`), the operation computes
  `M`, a map-level operation on the two focused subtries.

`Zippy.lean` builds the set algebra from these.  Where `M` is *not* the obvious
set operation — `restrict` keeps the focus value, `join_into` ignores the
source's, `insert_prefix` leaves the focus value where it was — the difference
is in `M`, and `Zippy.lean` states it as a law of its own.

Equality of values is decided by `ValOps.beq`, and two branches of the algebraic
operations return the zipper untouched when `beqT` says the result equals the
input.  Those branches agree with the others only if `beq` is sound, so the
algebraic lemmas take `LawfulBeqOps ops`.  `unitOps` and `u64Ops` both are.
-/

namespace PrunedModel

open PathMapModel

/-- `ValOps.beq` decides equality. -/
def LawfulBeqOps {V : Type} (ops : ValOps V) : Prop := ∀ a b, ops.beq a b = true → a = b

theorem unitOps_lawful : LawfulBeqOps unitOps := fun _ _ _ => rfl

theorem u64Ops_lawful : LawfulBeqOps u64Ops := by
  intro a b h
  simpa [u64Ops] using h

namespace PrunedMap

variable {V : Type}

/-! ## Replacing a subtrie -/

/-- `t` with everything at and below `f` replaced by `m`; `m`'s root value goes
to `f`. -/
def replaceAt (t : PrunedMap V) (f : Path) (m : PrunedMap V) : PrunedMap V :=
  mk' ((t.removeAt f).entries ++ m.entries.map fun kv => (f ++ kv.1, kv.2))

theorem valAt_replaceAt (t : PrunedMap V) (f : Path) (m : PrunedMap V) (k : Path) :
    (t.replaceAt f m).valAt k =
      match Path.stripPrefix f k with
      | some r => m.valAt r
      | none => t.valAt k := by
  rw [replaceAt, valAt_mk', lookup_append]
  have hA : (t.removeAt f).entries.lookup k = (t.removeAt f).valAt k := rfl
  rw [hA, valAt_removeAt, lookup_map_prepend, Path.isPrefixOf_eq_isSome_stripPrefix]
  cases Path.stripPrefix f k <;> simp <;> rfl

theorem valAt_replaceAt_append (t : PrunedMap V) (f : Path) (m : PrunedMap V) (r : Path) :
    (t.replaceAt f m).valAt (f ++ r) = m.valAt r := by
  rw [valAt_replaceAt, Path.stripPrefix_append]

theorem valAt_replaceAt_of_not {t : PrunedMap V} {f : Path} {m : PrunedMap V} {k : Path}
    (h : ∀ r, k ≠ f ++ r) : (t.replaceAt f m).valAt k = t.valAt k := by
  rw [valAt_replaceAt, (Path.stripPrefix_eq_none f k).mpr h]

/-- Replacing at the root replaces everything. -/
theorem replaceAt_nil (t m : PrunedMap V) : t.replaceAt [] m = m :=
  ext fun k => by
    show (t.replaceAt [] m).valAt k = m.valAt k
    exact valAt_replaceAt_append t [] m k

/-- Reading back what was written. -/
theorem subtrie_replaceAt (t : PrunedMap V) (f : Path) (m : PrunedMap V) :
    (t.replaceAt f m).subtrie f = m :=
  ext fun k => by
    show ((t.replaceAt f m).subtrie f).valAt k = m.valAt k
    rw [valAt_subtrie, valAt_replaceAt_append]

/-- **The three-case check.**  `t'` is `t` with `m` written at `f` iff they agree
away from `f`, at `f` (the root value), and strictly below `f` (the node). -/
theorem eq_replaceAt {t t' : PrunedMap V} {f : Path} {m : PrunedMap V}
    (hout : ∀ k, (∀ r, k ≠ f ++ r) → t'.valAt k = t.valAt k)
    (hroot : t'.valAt f = m.valAt [])
    (hbelow : ∀ b r, t'.valAt (f ++ b :: r) = m.valAt (b :: r)) :
    t' = t.replaceAt f m := by
  apply ext; intro k
  show t'.valAt k = (t.replaceAt f m).valAt k
  rw [valAt_replaceAt]
  cases hs : Path.stripPrefix f k with
  | none => exact hout k ((Path.stripPrefix_eq_none f k).mp hs)
  | some r =>
      have := (Path.stripPrefix_eq_some f k r).mp hs; subst this
      cases r with
      | nil => simpa using hroot
      | cons b r => exact hbelow b r

/-- A path off `f`'s subtrie is not `f`. -/
theorem ne_of_off {k f : Path} (h : ∀ r, k ≠ f ++ r) : k ≠ f := by
  intro e; exact h [] (by simp [e])

/-- …and `graftBelow f` does not see it. -/
theorem stripPrefix_off {k f : Path} (h : ∀ r, k ≠ f ++ r) : Path.stripPrefix f k = none :=
  (Path.stripPrefix_eq_none f k).mpr h

/-- `x`'s root value over `n`'s node: what an operation that works on nodes —
and leaves the focus value alone — writes at the focus. -/
def withRootOf (x n : PrunedMap V) : PrunedMap V :=
  mk' ((x.entries.filter fun kv => kv.1.isEmpty) ++ (n.entries.filter fun kv => !kv.1.isEmpty))

theorem valAt_withRootOf_nil (x n : PrunedMap V) : (withRootOf x n).valAt [] = x.valAt [] := by
  rw [withRootOf, valAt_mk', lookup_append, lookup_filter_key (fun k => k.isEmpty),
    lookup_filter_key (fun k => !k.isEmpty)]
  simp; rfl

theorem valAt_withRootOf_cons (x n : PrunedMap V) (b : UInt8) (r : Path) :
    (withRootOf x n).valAt (b :: r) = n.valAt (b :: r) := by
  rw [withRootOf, valAt_mk', lookup_append, lookup_filter_key (fun k => k.isEmpty),
    lookup_filter_key (fun k => !k.isEmpty)]
  simp; rfl

/-- `validatedBy` reads only non-empty paths, so a root value is invisible to it. -/
theorem validatedBy_congr {a b : PrunedMap V} (h : ∀ c r, a.valAt (c :: r) = b.valAt (c :: r))
    (q : Path) : validatedBy a q = validatedBy b q := by
  apply Bool.eq_iff_iff.mpr
  rw [validatedBy_iff, validatedBy_iff]
  constructor
  · rintro ⟨r, s, hr, hq, hv⟩
    cases r with
    | nil => exact absurd rfl hr
    | cons c r => exact ⟨c :: r, s, hr, hq, by rwa [← h]⟩
  · rintro ⟨r, s, hr, hq, hv⟩
    cases r with
    | nil => exact absurd rfl hr
    | cons c r => exact ⟨c :: r, s, hr, hq, by rwa [h]⟩

theorem validatedBy_empty (q : Path) : validatedBy (empty : PrunedMap V) q = false := by
  cases h : validatedBy (empty : PrunedMap V) q with
  | false => rfl
  | true =>
      obtain ⟨r, s, _, _, hv⟩ := (validatedBy_iff _ _).mp h
      simp at hv

/-! ## `beqT` is equality, when `beq` is -/

private theorem eq_of_zip_all {ops : ValOps V} (hbeq : LawfulBeqOps ops) :
    ∀ (l₁ l₂ : List (Path × V)), l₁.length = l₂.length →
      (l₁.zip l₂).all (fun xy => xy.1.1 == xy.2.1 && ops.beq xy.1.2 xy.2.2) = true → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, h => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have := eq_of_zip_all hbeq xs ys (by simpa using hl) h3
      obtain ⟨xk, xv⟩ := x; obtain ⟨yk, yv⟩ := y
      simp only at h1 h2
      rw [h1, hbeq _ _ h2, this]

theorem eq_of_beqT {ops : ValOps V} (hbeq : LawfulBeqOps ops) {a b : PrunedMap V}
    (h : beqT ops a b = true) : a = b := by
  rw [beqT, Bool.and_eq_true, beq_iff_eq] at h
  have he := eq_of_zip_all hbeq _ _ h.1 h.2
  exact ext fun k => by rw [he]

end PrunedMap

namespace PZip

open PrunedMap

variable {V : Type} (z : PZip V)

/-! ## Reading at the focus -/

@[simp] theorem withTrie_trie (t : PrunedMap V) : (z.withTrie t).trie = t := rfl
@[simp] theorem withTrie_focus (t : PrunedMap V) : (z.withTrie t).focus = z.focus := rfl
@[simp] theorem withTrie_withTrie (t u : PrunedMap V) :
    (z.withTrie t).withTrie u = z.withTrie u := rfl
@[simp] theorem withTrie_self : z.withTrie z.trie = z := rfl

theorem valAt_makeMap (k : Path) : z.makeMap.valAt k = z.trie.valAt (z.focus ++ k) :=
  valAt_subtrie _ _ _

theorem makeMap_valAt_nil : z.makeMap.valAt [] = z.val := by
  rw [valAt_makeMap, List.append_nil]; rfl

theorem valAt_focusNode (k : Path) :
    z.focusNode.valAt k = if k = [] then none else z.trie.valAt (z.focus ++ k) := by
  rw [focusNode, valAt_removeVal, valAt_makeMap]

theorem valAt_focusNode_cons (b : UInt8) (r : Path) :
    z.focusNode.valAt (b :: r) = z.trie.valAt (z.focus ++ b :: r) := by
  rw [valAt_focusNode]; simp

theorem focusNode_isEmptyMap_iff :
    z.focusNode.isEmptyMap = true ↔ ∀ b r, z.trie.valAt (z.focus ++ b :: r) = none := by
  rw [isEmptyMap_iff]
  constructor
  · intro h b r; rw [← valAt_focusNode_cons]; exact h _
  · intro h k
    cases k with
    | nil => rw [valAt_focusNode]; simp
    | cons b r => rw [valAt_focusNode_cons]; exact h b r

theorem focusNodeIsEmpty_iff :
    z.focusNodeIsEmpty = true ↔ ∀ b r, z.trie.valAt (z.focus ++ b :: r) = none :=
  belowIsEmpty_iff _ _

theorem focusNodeIsEmpty_eq : z.focusNodeIsEmpty = z.focusNode.isEmptyMap := by
  apply Bool.eq_iff_iff.mpr
  rw [focusNodeIsEmpty_iff, focusNode_isEmptyMap_iff]

/-! ## The value at the focus -/

theorem setVal_eq (v : V) :
    (z.setVal v).2 = z.withTrie (z.trie.replaceAt z.focus ((z.makeMap.setVal [] v).2)) := by
  have h0 : (z.setVal v).2 = z.withTrie (z.trie.setVal z.focus v).2 := rfl
  rw [h0]
  congr 1
  apply eq_replaceAt
  · intro k hk; rw [valAt_setVal, if_neg (ne_of_off hk)]
  · rw [valAt_setVal, valAt_setVal]; simp
  · intro b r
    rw [valAt_setVal, valAt_setVal, valAt_makeMap]
    simp

theorem removeVal_eq :
    (z.removeVal).2 = z.withTrie (z.trie.replaceAt z.focus ((z.makeMap.removeVal []).2)) := by
  have key : z.trie.replaceAt z.focus ((z.makeMap.removeVal []).2) = (z.trie.removeVal z.focus).2 := by
    symm
    apply eq_replaceAt
    · intro k hk; rw [valAt_removeVal, if_neg (ne_of_off hk)]
    · rw [valAt_removeVal, valAt_removeVal]; simp
    · intro b r
      rw [valAt_removeVal, valAt_removeVal, valAt_makeMap]
      simp
  rw [key]
  unfold removeVal
  cases hv : z.val with
  | some v => rfl
  | none =>
      simp only
      have : (z.trie.removeVal z.focus).2 = z.trie := by
        apply ext; intro k
        show (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k
        rw [valAt_removeVal]
        by_cases hk : k = z.focus
        · subst hk; simp only [if_true]; exact hv.symm
        · simp [hk]
      rw [this]; rfl

/-! ## Grafting -/

theorem graftMap_eq (m : PrunedMap V) :
    z.graftMap m = z.withTrie (z.trie.replaceAt z.focus m) := by
  show z.withTrie _ = _
  congr 1
  apply eq_replaceAt
  · intro k hk
    cases m.valAt [] <;>
      simp [valAt_setVal, valAt_removeVal, valAt_graftBelow, ne_of_off hk, stripPrefix_off hk]
  · cases hm : m.valAt [] <;> simp [valAt_setVal, valAt_removeVal]
  · intro b r
    have hne : z.focus ++ b :: r ≠ z.focus := by
      intro h; have := congrArg List.length h; simp at this
    cases m.valAt [] <;>
      simp [valAt_setVal, valAt_removeVal, valAt_graftBelow, hne, Path.stripPrefix_append]

theorem graft_eq (src : PZip V) : z.graft src = z.withTrie (z.trie.replaceAt z.focus src.makeMap) :=
  graftMap_eq z _

/-! ## The shared tail of the algebraic operations

Every algebraic operation ends the same way: compute a node `r`, and either
graft it below the focus or — when `beqT` says it equals what is there — leave
the zipper alone.  With a lawful `beq` the two branches agree, so each operation
is "graft `r`". -/

theorem graftBelow_focusNode : z.trie.graftBelow z.focus z.focusNode = z.trie := by
  apply ext; intro k
  show (z.trie.graftBelow z.focus z.focusNode).valAt k = z.trie.valAt k
  rw [valAt_graftBelow]
  cases hs : Path.stripPrefix z.focus k with
  | none => rfl
  | some r =>
      cases r with
      | nil => rfl
      | cons b r =>
          dsimp only
          rw [valAt_focusNode_cons, (Path.stripPrefix_eq_some _ _ _).mp hs]

theorem keep_eq_graft (z1 : PZip V) {r : PrunedMap V} (h : r = z1.focusNode) :
    z1 = z1.withTrie (z1.trie.graftBelow z1.focus r) := by
  rw [h, graftBelow_focusNode]; rfl

theorem ite_beqT_graft {ops : ValOps V} (hbeq : LawfulBeqOps ops) (z1 : PZip V) (r : PrunedMap V) :
    (if ((if beqT ops r z1.focusNode = true then AlgStatus.identity else AlgStatus.element)
          == AlgStatus.identity) = true then z1
      else z1.withTrie (z1.trie.graftBelow z1.focus r)) =
      z1.withTrie (z1.trie.graftBelow z1.focus r) := by
  by_cases h : beqT ops r z1.focusNode = true
  · simp only [h, if_true]; exact keep_eq_graft z1 (eq_of_beqT hbeq h)
  · simp [h]

theorem ite_nodeStatus_graft {ops : ValOps V} (hbeq : LawfulBeqOps ops) (z1 : PZip V)
    (r : PrunedMap V) :
    (if (nodeStatus ops z1.focusNode r == AlgStatus.identity) = true then z1
      else z1.withTrie (z1.trie.graftBelow z1.focus r)) =
      z1.withTrie (z1.trie.graftBelow z1.focus r) := by
  by_cases h : (nodeStatus ops z1.focusNode r == AlgStatus.identity) = true
  · rw [if_pos h]
    apply keep_eq_graft
    unfold nodeStatus at h
    by_cases he : r.isEmptyMap = true
    · simp [he] at h
    · by_cases hb : beqT ops r z1.focusNode = true
      · exact eq_of_beqT hbeq hb
      · simp [he, hb] at h
  · rw [if_neg h]

/-- Grafting below the focus of a zipper whose trie is `T`. -/
theorem withTrie_graft_eq (T R : PrunedMap V) :
    (z.withTrie T).withTrie ((z.withTrie T).trie.graftBelow (z.withTrie T).focus R) =
      z.withTrie (T.graftBelow z.focus R) := rfl

theorem removeVal_eq' : (z.removeVal).2 = z.withTrie (z.trie.removeVal z.focus).2 := by
  unfold removeVal
  cases hv : z.val with
  | some v => rfl
  | none =>
      simp only
      have : (z.trie.removeVal z.focus).2 = z.trie := by
        apply ext; intro k
        show (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k
        rw [valAt_removeVal]
        by_cases hk : k = z.focus
        · subst hk; simp only [if_true]; exact hv.symm
        · simp [hk]
      rw [this]; rfl

theorem setVal_eq' (v : V) : (z.setVal v).2 = z.withTrie (z.trie.setVal z.focus v).2 := rfl

end PZip

/-! ## Facts about the operations on `Option V` that hold for every value type -/

namespace PrunedMap
variable {V : Type} (ops : ValOps V)

@[simp] theorem joinVal_none_right (x : Option V) : joinVal ops x none = x := by
  cases x <;> rfl
@[simp] theorem joinVal_none_left (x : Option V) : joinVal ops none x = x := rfl
@[simp] theorem meetVal_none_right (x : Option V) : meetVal ops x none = none := by
  cases x <;> rfl
@[simp] theorem meetVal_none_left (x : Option V) : meetVal ops none x = none := rfl
@[simp] theorem subVal_none_right (x : Option V) : subVal ops x none = x := by
  cases x <;> rfl
@[simp] theorem subVal_none_left (x : Option V) : subVal ops none x = none := rfl

end PrunedMap

namespace PZip
open PrunedMap
variable {V : Type} (z : PZip V)

/-! ## Finishing an operation

After the value step the zipper is `z.withTrie T`, where `T` differs from
`z.trie` at most at the focus.  The node step then either keeps it or grafts a
node `R` below the focus.  These two lemmas turn either ending into the
`replaceAt` form, given what `T` and `R` hold. -/

theorem finish_keep (T M : PrunedMap V)
    (hout : ∀ k, (∀ r, k ≠ z.focus ++ r) → T.valAt k = z.trie.valAt k)
    (hroot : T.valAt z.focus = M.valAt [])
    (hbelow : ∀ b r, T.valAt (z.focus ++ b :: r) = M.valAt (b :: r)) :
    z.withTrie T = z.withTrie (z.trie.replaceAt z.focus M) := by
  congr 1
  exact eq_replaceAt hout hroot hbelow

theorem stripPrefix_self (p : Path) : Path.stripPrefix p p = some [] := by
  simpa using Path.stripPrefix_append p []

theorem finish_graft (T R M : PrunedMap V)
    (hout : ∀ k, k ≠ z.focus → T.valAt k = z.trie.valAt k)
    (hroot : T.valAt z.focus = M.valAt [])
    (hbelow : ∀ b r, R.valAt (b :: r) = M.valAt (b :: r)) :
    z.withTrie (T.graftBelow z.focus R) = z.withTrie (z.trie.replaceAt z.focus M) := by
  apply finish_keep
  · intro k hk
    rw [valAt_graftBelow, stripPrefix_off hk]
    exact hout k (ne_of_off hk)
  · rw [valAt_graftBelow, stripPrefix_self]
    exact hroot
  · intro b r
    rw [valAt_graftBelow, Path.stripPrefix_append]
    exact hbelow b r

/-! ## The algebraic operations -/

theorem joinMapInto_eq {ops : ValOps V} (hbeq : LawfulBeqOps ops) (m : PrunedMap V) :
    (z.joinMapInto ops m).2 = z.withTrie (z.trie.replaceAt z.focus (join ops z.makeMap m)) := by
  have tail : ∀ T : PrunedMap V, (∀ k, k ≠ z.focus → T.valAt k = z.trie.valAt k) →
      T.valAt z.focus = joinVal ops z.val (m.valAt []) →
      (if (m.removeVal []).2.isEmptyMap = true then z.withTrie T
       else z.withTrie (T.graftBelow z.focus (join ops (z.withTrie T).focusNode (m.removeVal []).2)))
        = z.withTrie (z.trie.replaceAt z.focus (join ops z.makeMap m)) := by
    intro T hout hroot
    have hroot' : T.valAt z.focus = (join ops z.makeMap m).valAt [] := by
      rw [valAt_join, makeMap_valAt_nil, hroot]
    split
    · next hE =>
      have hmb : ∀ b r, m.valAt (b :: r) = none := fun b r => by
        have := (isEmptyMap_iff _).mp hE (b :: r); rwa [valAt_removeVal, if_neg (by simp)] at this
      apply finish_keep
      · intro k hk; exact hout k (ne_of_off hk)
      · exact hroot'
      · intro b r; rw [valAt_join, valAt_makeMap, hmb, joinVal_none_right]; exact hout _ (by simp)
    · apply finish_graft _ _ _ _ hout hroot'
      intro b r
      rw [valAt_join, valAt_join, valAt_focusNode_cons, valAt_removeVal, if_neg (by simp), valAt_makeMap]
      simp only [withTrie_trie, withTrie_focus]
      rw [hout _ (by simp)]
  have offFocus : ∀ (v : V) k, k ≠ z.focus → (z.trie.setVal z.focus v).2.valAt k = z.trie.valAt k :=
    fun v k hk => by rw [valAt_setVal, if_neg hk]
  have offFocus' : ∀ k, k ≠ z.focus → (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k :=
    fun k hk => by rw [valAt_removeVal, if_neg hk]
  unfold joinMapInto
  cases hz : z.val with
  | none =>
    cases hm : m.valAt [] with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_beqT_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hm]; exact hz)
    | some mv =>
      simp only [apply_ite Prod.snd]
      rw [ite_beqT_graft hbeq]
      exact tail (z.trie.setVal z.focus mv).2 (offFocus mv) (by rw [valAt_setVal, if_pos rfl, hz, hm]; rfl)
  | some sv =>
    cases hm : m.valAt [] with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_beqT_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hm]; exact hz)
    | some mv =>
      cases hr : (ops.pjoin sv mv).resolve sv mv with
      | none =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_beqT_graft hbeq, removeVal_eq']
        exact tail (z.trie.removeVal z.focus).2 offFocus' (by rw [valAt_removeVal, if_pos rfl, hz, hm]; exact hr.symm)
      | some v =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_beqT_graft hbeq]
        exact tail (z.trie.setVal z.focus v).2 (offFocus v) (by rw [valAt_setVal, if_pos rfl, hz, hm]; exact hr.symm)

/-! ### `removeBelow` at the focus -/

theorem isPrefixOf_off {k f : Path} (h : ∀ r, k ≠ f ++ r) : Path.isPrefixOf f k = false := by
  rw [Path.isPrefixOf_eq_isSome_stripPrefix, stripPrefix_off h]; rfl

theorem valAt_removeBelow_off (T : PrunedMap V) {f k : Path} (h : ∀ r, k ≠ f ++ r) :
    (T.removeBelow f).valAt k = T.valAt k := by
  rw [valAt_removeBelow, isPrefixOf_off h]; simp

theorem valAt_removeBelow_self (T : PrunedMap V) (f : Path) :
    (T.removeBelow f).valAt f = T.valAt f := by
  rw [valAt_removeBelow]; simp

theorem valAt_removeBelow_cons (T : PrunedMap V) (f : Path) (b : UInt8) (r : Path) :
    (T.removeBelow f).valAt (f ++ b :: r) = none := by
  rw [valAt_removeBelow, if_pos ⟨(Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩, by simp⟩]

theorem focus_cons_ne (b : UInt8) (r : Path) : z.focus ++ b :: r ≠ z.focus := by simp

theorem ite_beqT_graft' {ops : ValOps V} (hbeq : LawfulBeqOps ops) (z1 : PZip V) (r : PrunedMap V) :
    (if beqT ops r z1.focusNode = true then z1
      else z1.withTrie (z1.trie.graftBelow z1.focus r)) =
      z1.withTrie (z1.trie.graftBelow z1.focus r) := by
  by_cases h : beqT ops r z1.focusNode = true
  · rw [if_pos h]; exact keep_eq_graft z1 (eq_of_beqT hbeq h)
  · rw [if_neg h]

theorem meetInto_eq {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : PZip V) :
    (z.meetInto ops src).2 = z.withTrie (z.trie.replaceAt z.focus (meet ops z.makeMap src.makeMap)) := by
  have tail : ∀ T : PrunedMap V, (∀ k, k ≠ z.focus → T.valAt k = z.trie.valAt k) →
      T.valAt z.focus = meetVal ops z.val src.val →
      (if (z.withTrie T).focusNode.isEmptyMap = true then z.withTrie T
       else if src.focusNode.isEmptyMap = true then z.withTrie (T.removeBelow z.focus)
       else z.withTrie (T.graftBelow z.focus (meet ops (z.withTrie T).focusNode src.focusNode)))
        = z.withTrie (z.trie.replaceAt z.focus (meet ops z.makeMap src.makeMap)) := by
    intro T hout hroot
    have hroot' : T.valAt z.focus = (meet ops z.makeMap src.makeMap).valAt [] := by
      rw [valAt_meet, makeMap_valAt_nil, makeMap_valAt_nil, hroot]
    have hT : ∀ b r, T.valAt (z.focus ++ b :: r) = z.trie.valAt (z.focus ++ b :: r) :=
      fun b r => hout _ (focus_cons_ne z b r)
    split
    · next hE =>
      apply finish_keep
      · intro k hk; exact hout k (ne_of_off hk)
      · exact hroot'
      · intro b r
        have h0 := (focusNode_isEmptyMap_iff _).mp hE b r
        simp only [withTrie_trie, withTrie_focus] at h0
        rw [valAt_meet, valAt_makeMap, ← hT, h0, meetVal_none_left]
    · split
      · next _ hE =>
        apply finish_keep
        · intro k hk; rw [valAt_removeBelow_off _ hk]; exact hout k (ne_of_off hk)
        · rw [valAt_removeBelow_self]; exact hroot'
        · intro b r
          rw [valAt_removeBelow_cons, valAt_meet, valAt_makeMap src,
            (focusNode_isEmptyMap_iff src).mp hE b r, meetVal_none_right]
      · apply finish_graft _ _ _ _ hout hroot'
        intro b r
        rw [valAt_meet, valAt_meet, valAt_focusNode_cons, valAt_focusNode_cons, valAt_makeMap,
          valAt_makeMap]
        simp only [withTrie_trie, withTrie_focus]; rw [hT]
  have offFocus : ∀ (v : V) k, k ≠ z.focus → (z.trie.setVal z.focus v).2.valAt k = z.trie.valAt k :=
    fun v k hk => by rw [valAt_setVal, if_neg hk]
  have offFocus' : ∀ k, k ≠ z.focus → (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k :=
    fun k hk => by rw [valAt_removeVal, if_neg hk]
  unfold meetInto
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
    | some ov =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
  | some sv =>
    cases hs : src.val with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq, removeVal_eq']
      exact tail (z.trie.removeVal z.focus).2 offFocus'
        (by rw [valAt_removeVal, if_pos rfl, hz, hs]; rfl)
    | some ov =>
      cases hr : (ops.pmeet sv ov).resolve sv ov with
      | none =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_nodeStatus_graft hbeq, removeVal_eq']
        exact tail (z.trie.removeVal z.focus).2 offFocus'
          (by rw [valAt_removeVal, if_pos rfl, hz, hs]; exact hr.symm)
      | some v =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_nodeStatus_graft hbeq]
        exact tail (z.trie.setVal z.focus v).2 (offFocus v)
          (by rw [valAt_setVal, if_pos rfl, hz, hs]; exact hr.symm)

theorem subtractInto_eq {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : PZip V) :
    (z.subtractInto ops src).2 = z.withTrie (z.trie.replaceAt z.focus (sub ops z.makeMap src.makeMap)) := by
  have tail : ∀ T : PrunedMap V, (∀ k, k ≠ z.focus → T.valAt k = z.trie.valAt k) →
      T.valAt z.focus = subVal ops z.val src.val →
      (if src.focusNode.isEmptyMap = true then z.withTrie T
       else if (z.withTrie T).focusNode.isEmptyMap = true then z.withTrie T
       else z.withTrie (T.graftBelow z.focus (sub ops (z.withTrie T).focusNode src.focusNode)))
        = z.withTrie (z.trie.replaceAt z.focus (sub ops z.makeMap src.makeMap)) := by
    intro T hout hroot
    have hroot' : T.valAt z.focus = (sub ops z.makeMap src.makeMap).valAt [] := by
      rw [valAt_sub, makeMap_valAt_nil, makeMap_valAt_nil, hroot]
    have hT : ∀ b r, T.valAt (z.focus ++ b :: r) = z.trie.valAt (z.focus ++ b :: r) :=
      fun b r => hout _ (focus_cons_ne z b r)
    split
    · next hE =>
      apply finish_keep
      · intro k hk; exact hout k (ne_of_off hk)
      · exact hroot'
      · intro b r
        rw [valAt_sub, valAt_makeMap, valAt_makeMap src, (focusNode_isEmptyMap_iff src).mp hE b r,
          subVal_none_right, hT]
    · split
      · next _ hE =>
        apply finish_keep
        · intro k hk; exact hout k (ne_of_off hk)
        · exact hroot'
        · intro b r
          have h0 := (focusNode_isEmptyMap_iff _).mp hE b r
          simp only [withTrie_trie, withTrie_focus] at h0
          rw [valAt_sub, valAt_makeMap, ← hT, h0, subVal_none_left]
      · apply finish_graft _ _ _ _ hout hroot'
        intro b r
        rw [valAt_sub, valAt_sub, valAt_focusNode_cons, valAt_focusNode_cons, valAt_makeMap,
          valAt_makeMap]
        simp only [withTrie_trie, withTrie_focus]; rw [hT]
  have offFocus : ∀ (v : V) k, k ≠ z.focus → (z.trie.setVal z.focus v).2.valAt k = z.trie.valAt k :=
    fun v k hk => by rw [valAt_setVal, if_neg hk]
  have offFocus' : ∀ k, k ≠ z.focus → (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k :=
    fun k hk => by rw [valAt_removeVal, if_neg hk]
  unfold subtractInto
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
    | some ov =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
  | some sv =>
    cases hs : src.val with
    | none =>
      simp only [apply_ite Prod.snd]
      rw [ite_nodeStatus_graft hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
    | some ov =>
      cases hr : (ops.psub sv ov).resolve sv ov with
      | none =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_nodeStatus_graft hbeq, removeVal_eq']
        exact tail (z.trie.removeVal z.focus).2 offFocus'
          (by rw [valAt_removeVal, if_pos rfl, hz, hs]; exact hr.symm)
      | some v =>
        simp only [apply_ite Prod.snd, hr]
        rw [ite_nodeStatus_graft hbeq]
        exact tail (z.trie.setVal z.focus v).2 (offFocus v)
          (by rw [valAt_setVal, if_pos rfl, hz, hs]; exact hr.symm)

/-- `join_into` writes the join of the two subtries, focus values included. -/
theorem joinInto_eq {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : PZip V) :
    (z.joinInto ops src).2 = z.withTrie (z.trie.replaceAt z.focus (join ops z.makeMap src.makeMap)) := by
  have tail : ∀ T : PrunedMap V, (∀ k, k ≠ z.focus → T.valAt k = z.trie.valAt k) →
      T.valAt z.focus = joinVal ops z.val src.val →
      (if src.focusNode.isEmptyMap = true then z.withTrie T
       else z.withTrie (T.graftBelow z.focus (join ops (z.withTrie T).focusNode src.focusNode)))
        = z.withTrie (z.trie.replaceAt z.focus (join ops z.makeMap src.makeMap)) := by
    intro T hout hroot
    have hroot' : T.valAt z.focus = (join ops z.makeMap src.makeMap).valAt [] := by
      rw [valAt_join, makeMap_valAt_nil, makeMap_valAt_nil, hroot]
    split
    · next hE =>
      apply finish_keep
      · intro k hk; exact hout k (ne_of_off hk)
      · exact hroot'
      · intro b r
        rw [valAt_join, valAt_makeMap, valAt_makeMap src, (focusNode_isEmptyMap_iff src).mp hE b r,
          joinVal_none_right]
        exact hout _ (focus_cons_ne z b r)
    · apply finish_graft _ _ _ _ hout hroot'
      intro b r
      rw [valAt_join, valAt_join, valAt_focusNode_cons, valAt_focusNode_cons, valAt_makeMap,
        valAt_makeMap]
      simp only [withTrie_trie, withTrie_focus]
      rw [hout _ (focus_cons_ne z b r)]
  have offFocus : ∀ (v : V) k, k ≠ z.focus → (z.trie.setVal z.focus v).2.valAt k = z.trie.valAt k :=
    fun v k hk => by rw [valAt_setVal, if_neg hk]
  have offFocus' : ∀ k, k ≠ z.focus → (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k :=
    fun k hk => by rw [valAt_removeVal, if_neg hk]
  unfold joinInto
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none =>
      simp only [ite_beqT_graft' hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
    | some mv =>
      simp only [ite_beqT_graft' hbeq]
      exact tail (z.trie.setVal z.focus mv).2 (offFocus mv) (by rw [valAt_setVal, if_pos rfl, hz, hs]; rfl)
  | some sv =>
    cases hs : src.val with
    | none =>
      simp only [ite_beqT_graft' hbeq]
      exact tail z.trie (fun _ _ => rfl) (by rw [hz, hs]; exact hz)
    | some mv =>
      cases hr : (ops.pjoin sv mv).resolve sv mv with
      | none =>
        simp only [hr, ite_beqT_graft' hbeq, removeVal_eq']
        exact tail (z.trie.removeVal z.focus).2 offFocus' (by rw [valAt_removeVal, if_pos rfl, hz, hs]; exact hr.symm)
      | some v =>
        simp only [hr, ite_beqT_graft' hbeq]
        exact tail (z.trie.setVal z.focus v).2 (offFocus v) (by rw [valAt_setVal, if_pos rfl, hz, hs]; exact hr.symm)

/-- `restrict` is `PathMap::restrict` on the two subtries: a source focus value
keeps everything, and otherwise a path is kept when a *non-empty* prefix of it is
valued in the source — so the destination's focus value goes. -/
theorem restrict_eq {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : PZip V) :
    (z.restrict ops src).2 = z.withTrie (z.trie.replaceAt z.focus
      (if src.val.isSome then z.makeMap else restrictBelowRoot z.makeMap src.makeMap)) := by
  unfold restrict
  by_cases hs : src.val.isSome = true
  · simp only [hs, if_true]
    apply finish_keep
    · intro _ _; rfl
    · rw [makeMap_valAt_nil]; rfl
    · intro b r; rw [valAt_makeMap]
  · simp only [hs, Bool.false_eq_true, if_false]
    have hv : ∀ q, validatedBy src.focusNode q = validatedBy src.makeMap q :=
      validatedBy_congr (fun c r => by rw [valAt_focusNode_cons, valAt_makeMap])
    have hroot : (z.trie.removeVal z.focus).2.valAt z.focus =
        (restrictBelowRoot z.makeMap src.makeMap).valAt [] := by
      rw [valAt_removeVal, if_pos rfl, valAt_restrictBelowRoot]; rfl
    have hout : ∀ k, k ≠ z.focus → (z.trie.removeVal z.focus).2.valAt k = z.trie.valAt k :=
      fun k hk => by rw [valAt_removeVal, if_neg hk]
    rw [removeVal_eq']
    simp only [apply_ite Prod.snd]
    rw [ite_nodeStatus_graft hbeq]
    split
    · next hE =>
      show z.withTrie ((z.trie.removeVal z.focus).2.removeBelow z.focus) = _
      apply finish_keep
      · intro k hk; rw [valAt_removeBelow_off _ hk]
        exact hout k (ne_of_off hk)
      · rw [valAt_removeBelow_self]; exact hroot
      · intro b r
        rw [valAt_removeBelow_cons, valAt_restrictBelowRoot, ← hv,
          validatedBy_congr (b := empty) (fun c r => (isEmptyMap_iff _).mp hE _), validatedBy_empty]
        rfl
    · split
      · next _ hE =>
        apply finish_keep _ _ _ (fun k hk => hout k (ne_of_off hk)) hroot
        intro b r
        have h0 := (focusNode_isEmptyMap_iff _).mp hE b r
        simp only [withTrie_trie, withTrie_focus] at h0
        rw [valAt_restrictBelowRoot, valAt_makeMap, ← hout _ (focus_cons_ne z b r), h0]
        split <;> rfl
      · rw [withTrie_graft_eq]
        apply finish_graft _ _ _ _ hout hroot
        intro b r
        rw [valAt_restrictBelowRoot, valAt_restrictBelowRoot, hv, valAt_focusNode_cons, valAt_makeMap]
        simp only [withTrie_trie, withTrie_focus]
        rw [hout _ (focus_cons_ne z b r)]

theorem removeBranches_eq :
    (z.removeBranches).2 = z.withTrie (z.trie.replaceAt z.focus (withRootOf z.makeMap empty)) := by
  apply finish_keep
  · intro k hk; rw [valAt_removeBelow_off _ hk]
  · rw [valAt_removeBelow_self, valAt_withRootOf_nil, makeMap_valAt_nil]; rfl
  · intro b r; rw [valAt_removeBelow_cons, valAt_withRootOf_cons]; rfl

/-- Where the focus does not exist, nothing lies at or below it. -/
theorem valAt_of_not_pathExists (h : z.pathExists = false) (r : Path) :
    z.trie.valAt (z.focus ++ r) = none := by
  cases hv : z.trie.valAt (z.focus ++ r) with
  | none => rfl
  | some v =>
    exfalso
    have hmem : z.focus ++ r ∈ z.trie.keys :=
      mem_keys_of_lookup_isSome (l := z.trie.entries)
        (show (z.trie.entries.lookup (z.focus ++ r)).isSome = true by
          rw [show z.trie.entries.lookup (z.focus ++ r) = some v from hv]; rfl)
    have he : z.trie.pathExists z.focus = true := by
      simp only [PrunedMap.pathExists, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨_, hmem, (Path.isPrefixOf_iff _ _).mpr ⟨r, rfl⟩⟩
    rw [show z.pathExists = z.trie.pathExists z.focus from rfl, he] at h
    cases h

theorem prepend_nil (m : PrunedMap V) : m.prepend [] = m := by
  apply ext; intro k
  show (m.prepend []).valAt k = m.valAt k
  rw [valAt_prepend]
  have := Path.stripPrefix_append [] k
  simp only [List.nil_append] at this
  rw [this]

/-- `insert_prefix` moves the whole subtrie, focus value included. -/
theorem insertPrefix_eq (pre : Path) :
    (z.insertPrefix pre).2 = z.withTrie (z.trie.replaceAt z.focus (z.makeMap.prepend pre)) := by
  unfold insertPrefix
  by_cases hx : z.pathExists = true
  · simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
    by_cases hp : pre.isEmpty = true
    · simp only [hp, if_true]
      rw [List.isEmpty_iff.mp hp, prepend_nil]
      apply finish_keep
      · intro _ _; rfl
      · rw [makeMap_valAt_nil]; rfl
      · intro b r; rw [valAt_makeMap]
    · simp only [hp, Bool.false_eq_true, if_false]
      exact graftMap_eq z _
  · have hx' : z.pathExists = false := by simpa using hx
    simp only [hx', Bool.not_false, if_true]
    have hnone : ∀ r, z.trie.valAt (z.focus ++ r) = none := valAt_of_not_pathExists z hx'
    apply finish_keep
    · intro _ _; rfl
    · rw [valAt_prepend]
      have := hnone []; rw [List.append_nil] at this; rw [this]
      split <;> first | rfl | (rw [valAt_makeMap, hnone])
    · intro b r
      rw [valAt_prepend, hnone]
      split <;> first | rfl | (rw [valAt_makeMap, hnone])

/-- `meet_2` writes the meet of the two sources' subtries, focus values included. -/
theorem meet2_eq {ops : ValOps V} (a b : PZip V) :
    (z.meet2 ops a b).2 = z.withTrie (z.trie.replaceAt z.focus (meet ops a.makeMap b.makeMap)) :=
  graftMap_eq z _

/-- `join_k_path_into k` writes `dropHead` of the subtrie. -/
theorem joinKPathInto_eq {ops : ValOps V} (k : Nat) :
    (z.joinKPathInto ops k).2 =
      if k == 0 then z else z.withTrie (z.trie.replaceAt z.focus (dropHead ops z.makeMap k)) := by
  unfold joinKPathInto
  split
  · rfl
  · exact graftMap_eq z _

/-- `meet_k_path_into k` grafts the meet of the subtries `k` bytes down, or the
empty map when there are none. -/
theorem meetKPathInto_snd {ops : ValOps V} (k : Nat) :
    (z.meetKPathInto ops k).2 = z.graftMap
      ((((z.trie.subtrie z.focus).kPaths k).foldl (meetStep ops z.trie z.focus) none).getD empty) := by
  unfold meetKPathInto
  dsimp only
  cases ((z.trie.subtrie z.focus).kPaths k).foldl (meetStep ops z.trie z.focus) none <;> rfl

/-- `remove_prefix n` ascends, then grafts what was the subtrie at the focus. -/
theorem removePrefix_snd (n : Nat) :
    (z.removePrefix n).2 = (z.ascend n).2.graftMap z.makeMap := rfl

/-- `take_map` removes the focus's subtrie, value included… -/
theorem takeMap_snd : (z.takeMap).2 = z.withTrie (z.trie.replaceAt z.focus empty) := by
  apply finish_keep
  · intro k hk
    show (z.trie.removeAt z.focus).valAt k = _
    rw [valAt_removeAt, isPrefixOf_off hk]; rfl
  · show (z.trie.removeAt z.focus).valAt z.focus = _
    rw [valAt_removeAt, if_pos ((Path.isPrefixOf_iff _ _).mpr ⟨[], by simp⟩)]; rfl
  · intro b r
    show (z.trie.removeAt z.focus).valAt _ = _
    rw [valAt_removeAt, if_pos ((Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩)]; rfl

/-- …and returns it: `make_map` before the removal, or `none` when there was
nothing there. -/
theorem takeMap_fst : (z.takeMap).1 = if z.makeMap.isEmptyMap then none else some z.makeMap := by
  have htaken : (match z.val with
      | some v => (z.focusNode.setVal [] v).2
      | none => z.focusNode) = z.makeMap := by
    apply ext; intro k
    show PrunedMap.valAt _ k = z.makeMap.valAt k
    cases hv : z.val with
    | some v =>
        simp only
        rw [valAt_setVal, valAt_focusNode, valAt_makeMap]
        by_cases hk : k = [] <;> simp [hk]; exact hv.symm
    | none =>
        simp only
        rw [valAt_focusNode, valAt_makeMap]
        by_cases hk : k = [] <;> simp [hk]; exact hv.symm
  have hemp : (z.focusNode.isEmptyMap && z.val.isNone) = z.makeMap.isEmptyMap := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true, focusNode_isEmptyMap_iff, isEmptyMap_iff, Option.isNone_iff_eq_none]
    constructor
    · rintro ⟨h1, h2⟩ k
      cases k with
      | nil => rw [makeMap_valAt_nil]; exact h2
      | cons b r => rw [valAt_makeMap]; exact h1 b r
    · intro h
      exact ⟨fun b r => by rw [← valAt_makeMap]; exact h _, by rw [← makeMap_valAt_nil]; exact h _⟩
  unfold takeMap
  simp only
  rw [hemp]
  by_cases h : z.makeMap.isEmptyMap = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; exact congrArg some htaken

end PZip
end PrunedModel
