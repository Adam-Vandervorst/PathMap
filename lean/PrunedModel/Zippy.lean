import PrunedModel.Refine

/-!
# Zippy's set algebra, as laws about zippers

[`formal.egg`](https://github.com/Adam-Vandervorst/Zippy/blob/b/formal.egg) is
the reference semantics of Zippy's space algebra: a space is a finite set of
paths, and each operator — `Union`, `Intersection`, `Subtraction`, `Wrap`,
`Unwrap`, `Composition`, `Restriction`, `Raffination`, `Head`, `TailsUnion`,
`TailsIntersection`, `IterC`, `Iter`, `Fix` — is given by egglog rewrite rules,
each annotated with the SMT proof that discharges it.  The file says of itself
that "no zipper logic lives here: zippers are an optimization and must be
observationally equivalent to this reference".

This file is that equivalence, for `pathmap`'s zippers, and then the rules.

## A space is a `PrunedMap Unit`

`Option Unit` is one bit, so a `PrunedMap Unit` is exactly a finite set of paths
(`Lattice.lean` §5).  `Path` is `List UInt8`, so egg's `Item i64` becomes a byte;
the tour's letters `a..z = 10..35` all fit.  `Eps` is `[]` and `Concat` is `++`.

## Every operator is a zipper program

Each operator is defined by what the model's write zipper does, not by a set
comprehension: `Union` is `join_map_into` at the root of a write zipper over the
first operand, `Unwrap` is `descend_to` then `make_map`, `Head` reads
`child_mask`, and so on (§1).  `Refine.lean` proves what each zipper operation
writes at its focus, and §2 turns that into one membership lemma per operator.
Every law in §3–§9 is then a statement about zipper programs, proved from those
membership lemmas alone.

On this branch (`focus_value_consistency`, issue #104) a subtrie includes the
value at its root, and the five raw zipper operations that used to differ from
their egg operator at the focus value now *are* it — §10 proves each:

* `join_into` is `Union`;
* `restrict` is `Restriction` (so §1 defines `Restriction` as `restrict`);
* `insert_prefix p` is `Wrap p`;
* `join_k_path_into 1` is `TailsUnion`;
* `meet_k_path_into 1` is `TailsIntersection` — since `482c248`, an empty meet
  clears the focus value (`remove_subtrie`) rather than keeping it
  (`remove_branches`).

The two tails operators are still defined by folding `join_map_into` and
`meet_into` over `child_mask`, as egg's rules compute them.

## What does not carry over

Nothing in `formal.egg` is false here.  Two of its rule groups are algorithms
rather than equations — the `drop-prefix` relation and the
`tails-intersection-acc` fold — and they appear as the equations they compute.
`Fix` is egg's *axiomatisation* of a least post-fixpoint; §9 states it as a
predicate, proves the three rules are its definition, that it is unique, and
that the inflationary iteration every Zippy executor runs reaches it when `F` is
monotone.  The `EB` membership-flag algebra is `Bool`'s own and needs no
statement.

The tour's `(check …)` lines are `#guard`s at the end, `(fail (check …))` as
`#guard !…`.
-/

namespace PrunedModel
namespace Zippy

open PathMapModel PrunedMap

/-- A space: a finite set of paths. -/
abbrev Space := PrunedMap Unit

instance : Membership Path Space := ⟨fun s p => (s.valAt p).isSome = true⟩

theorem mem_def {p : Path} {s : Space} : p ∈ s ↔ (s.valAt p).isSome = true := Iff.rfl

instance (p : Path) (s : Space) : Decidable (p ∈ s) :=
  inferInstanceAs (Decidable ((s.valAt p).isSome = true))

instance : DecidableEq Space := fun a b =>
  if h : a.entries = b.entries then isTrue (PrunedMap.ext fun k => by rw [h])
  else isFalse fun e => h (by rw [e])

/-- **Extensionality.**  Two spaces with the same members are equal — which is
what lets every law below be an equation. -/
theorem ext {a b : Space} (h : ∀ p, p ∈ a ↔ p ∈ b) : a = b := by
  apply PrunedMap.ext; intro k
  show a.valAt k = b.valAt k
  rw [unit_valAt_determined a k, unit_valAt_determined b k]
  have := h k
  rw [mem_def, mem_def] at this
  rw [Bool.eq_iff_iff.mpr this]

/-- `valAt` of a space is determined by membership. -/
theorem valAt_eq (s : Space) (p : Path) : s.valAt p = if p ∈ s then some () else none := by
  rw [unit_valAt_determined s p]; rfl

theorem not_mem_iff (s : Space) (p : Path) : p ∉ s ↔ s.valAt p = none := by
  rw [mem_def]; cases s.valAt p <;> simp

/-! ## 1. The operators, as zipper programs -/

/-- A write zipper at the root of `s`. -/
def wz (s : Space) : PZip Unit := ⟨s, [], []⟩

/-- `Empty`. -/
def empty : Space := PrunedMap.empty

/-- `Singleton p`: `descend_to p`, then `set_val`. -/
def singleton (p : Path) : Space := (((wz empty).descendTo p).setVal ()).2.trie

/-- `Union`: `join_map_into` — which joins the root value too — at the root. -/
def union (a b : Space) : Space := ((wz a).joinMapInto unitOps b).2.trie

/-- `Intersection`: `meet_into`. -/
def inter (a b : Space) : Space := ((wz a).meetInto unitOps (wz b)).2.trie

/-- `Subtraction`: `subtract_into`. -/
def subtr (a b : Space) : Space := ((wz a).subtractInto unitOps (wz b)).2.trie

/-- `Wrap p s`: `descend_to p` in an empty map, then `graft_map s`. -/
def wrap (p : Path) (s : Space) : Space := (((wz empty).descendTo p).graftMap s).trie

/-- `Unwrap s p`: `descend_to p`, then `make_map`. -/
def unwrap (s : Space) (p : Path) : Space := ((wz s).descendTo p).makeMap

/-- `Restriction x y`: the paths of `x` with a prefix in `y` — `restrict`, which
on this branch consults the source's focus value and clears the destination's
when it has none, as `PathMap::restrict` does. -/
def restriction (x y : Space) : Space := ((wz x).restrict unitOps (wz y)).2.trie

/-- `Raffination x y`, which egg *defines* as `x \ (x <| y)`. -/
def raffination (x y : Space) : Space := subtr x (restriction x y)

/-- `Composition s t`: for each path `u` of `s`, `descend_to u` and
`join_map_into t`. -/
def composition (s t : Space) : Space :=
  s.keys.foldl (fun acc u => (((wz acc).descendTo u).joinMapInto unitOps t).2.trie) empty

/-- `Head s`: one single-byte path per bit of `child_mask`. -/
def head (s : Space) : Space := (wz s).childMask.foldl (fun acc b => union acc (singleton [b])) empty

/-- `TailsUnion s`: the union, over `child_mask`, of `descend_to_byte b` then
`make_map`. -/
def tailsUnion (s : Space) : Space :=
  (wz s).childMask.foldl (fun acc b => union acc ((wz s).descendToByte b).makeMap) empty

/-- `TailsIntersection s`: the intersection of the same children — egg's
`tails-intersection-acc` fold, started at the first head.  No heads, no
tails. -/
def tailsInter (s : Space) : Space :=
  match (wz s).childMask with
  | [] => empty
  | b :: bs => bs.foldl (fun acc c => inter acc ((wz s).descendToByte c).makeMap)
      ((wz s).descendToByte b).makeMap

/-- One arm of an iteration: the body at head `h`, over `src`'s tails under `h`. -/
def iterArm (src : Space) (body : UInt8 → Space → Space) : Path → Space
  | [h] => body h (unwrap src [h])
  | _ => empty

/-- `IterH H src body`: the union of `body h (src's tails under h)` over the
single-byte paths `[h]` of `H`.  Paths of any other length contribute nothing;
egg has no rule for them, and only `iter` builds an `IterH`. -/
def iterH (H src : Space) (body : UInt8 → Space → Space) : Space :=
  H.keys.foldl (fun acc k => union acc (iterArm src body k)) empty

/-- `Iter src body`: head-dependent iteration, which egg rewrites to
`IterH (Head src) src body` (its rule L1) — so that is its definition here. -/
def iter (src : Space) (body : UInt8 → Space → Space) : Space := iterH (head src) src body

/-- `IterC src b`: iteration with a loop-invariant body. -/
def iterC (src b : Space) : Space := iter src fun _ _ => b

/-! ## 2. What each zipper program computes -/

@[simp] theorem wz_trie (s : Space) : (wz s).trie = s := rfl
@[simp] theorem wz_focus (s : Space) : (wz s).focus = [] := rfl
@[simp] theorem wz_descendTo_focus (s : Space) (p : Path) : ((wz s).descendTo p).focus = p := rfl
@[simp] theorem wz_descendTo_trie (s : Space) (p : Path) : ((wz s).descendTo p).trie = s := rfl

theorem subtrie_nil (t : Space) : t.subtrie [] = t :=
  PrunedMap.ext fun k => by
    show (t.subtrie []).valAt k = t.valAt k
    rw [valAt_subtrie]; rfl

@[simp] theorem wz_makeMap (s : Space) : (wz s).makeMap = s := subtrie_nil s

theorem not_mem_empty (p : Path) : p ∉ empty := by simp [mem_def, empty]

theorem mem_singleton {p q : Path} : p ∈ singleton q ↔ p = q := by
  rw [singleton, PZip.setVal_eq, PZip.withTrie_trie, mem_def, valAt_replaceAt]
  simp only [wz_descendTo_focus, wz_descendTo_trie]
  cases hs : Path.stripPrefix q p with
  | none =>
      simp only [empty, valAt_empty, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro h; subst h; rw [PZip.stripPrefix_self] at hs; cases hs
  | some r =>
      have := (Path.stripPrefix_eq_some q p r).mp hs; subst this
      dsimp only
      rw [valAt_setVal]
      by_cases hr : r = [] <;> simp [hr, PZip.valAt_makeMap, empty]

theorem union_eq_join (a b : Space) : union a b = join unitOps a b := by
  rw [union, PZip.joinMapInto_eq _ unitOps_lawful, PZip.withTrie_trie, wz_focus, replaceAt_nil,
    wz_makeMap]

theorem inter_eq_meet (a b : Space) : inter a b = meet unitOps a b := by
  rw [inter, PZip.meetInto_eq _ unitOps_lawful, PZip.withTrie_trie, wz_focus, replaceAt_nil,
    wz_makeMap, wz_makeMap]

theorem subtr_eq_sub (a b : Space) : subtr a b = sub unitOps a b := by
  rw [subtr, PZip.subtractInto_eq _ unitOps_lawful, PZip.withTrie_trie, wz_focus, replaceAt_nil,
    wz_makeMap, wz_makeMap]

theorem mem_union {p : Path} {a b : Space} : p ∈ union a b ↔ p ∈ a ∨ p ∈ b := by
  rw [union_eq_join, mem_def, unit_join_isSome, Bool.or_eq_true]; rfl

theorem mem_inter {p : Path} {a b : Space} : p ∈ inter a b ↔ p ∈ a ∧ p ∈ b := by
  rw [inter_eq_meet, mem_def, unit_meet_isSome, Bool.and_eq_true]; rfl

theorem mem_subtr {p : Path} {a b : Space} : p ∈ subtr a b ↔ p ∈ a ∧ p ∉ b := by
  rw [subtr_eq_sub, mem_def, valAt_sub, mem_def, not_mem_iff]
  cases a.valAt p <;> cases hb : b.valAt p <;> simp [subVal, unitOps, ValRes.resolve]

theorem wrap_eq (p : Path) (s : Space) : wrap p s = empty.replaceAt p s := by
  rw [wrap, PZip.graftMap_eq]; rfl

theorem mem_wrap {p q : Path} {s : Space} : p ∈ wrap q s ↔ ∃ r, p = q ++ r ∧ r ∈ s := by
  rw [wrap_eq, mem_def, valAt_replaceAt]
  cases hs : Path.stripPrefix q p with
  | none =>
      simp only [empty, valAt_empty, Option.isSome_none, Bool.false_eq_true, false_iff, not_exists,
        not_and]
      intro r hr; exact absurd hr ((Path.stripPrefix_eq_none q p).mp hs r)
  | some r =>
      have := (Path.stripPrefix_eq_some q p r).mp hs; subst this
      constructor
      · intro h; exact ⟨r, rfl, h⟩
      · rintro ⟨r', hr', h⟩
        rw [List.append_cancel_left hr']; exact h

theorem mem_unwrap {p q : Path} {s : Space} : p ∈ unwrap s q ↔ q ++ p ∈ s := by
  rw [unwrap, mem_def, PZip.valAt_makeMap]; rfl

theorem mem_keys {k : Path} {s : Space} : k ∈ s.keys ↔ k ∈ s := by
  constructor
  · intro h; exact lookup_isSome_of_mem_keys h
  · intro h; exact mem_keys_of_lookup_isSome h

theorem mem_ofList (b : UInt8) (bs : List UInt8) : b ∈ ByteMask.ofList bs ↔ b ∈ bs := by
  rw [ByteMask.ofList, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    simp only at hi
    split at hi
    · next hc => cases hi; exact List.contains_iff_mem.mp hc
    · cases hi
  · intro hb
    refine ⟨b.toNat, List.mem_range.mpr (UInt8.toNat_lt b), ?_⟩
    simp only
    rw [if_pos (by rw [UInt8.ofNat_toNat]; exact List.contains_iff_mem.mpr hb), UInt8.ofNat_toNat]

/-- `child_mask` at the root: the first bytes of the paths. -/
theorem mem_childMask {b : UInt8} {s : Space} : b ∈ (wz s).childMask ↔ ∃ r, b :: r ∈ s := by
  show b ∈ s.childMask [] ↔ _
  rw [childMask, mem_ofList, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hb⟩
    have hk' : k ∈ s := mem_keys.mp hk
    cases k with
    | nil => simp [Path.stripPrefix] at hb
    | cons c r =>
        simp only [Path.stripPrefix, Option.some.injEq] at hb
        subst hb; exact ⟨r, hk'⟩
  · rintro ⟨r, hr⟩
    exact ⟨b :: r, mem_keys.mpr hr, rfl⟩

/-- Folding a union over a list: a member of the result is a member of the
start or of some step. -/
theorem mem_foldl_union {α : Type} (f : α → Space) (p : Path) :
    ∀ (l : List α) (init : Space),
      p ∈ l.foldl (fun acc x => union acc (f x)) init ↔ p ∈ init ∨ ∃ x ∈ l, p ∈ f x
  | [], init => by simp
  | x :: xs, init => by
      rw [List.foldl_cons, mem_foldl_union f p xs, mem_union]
      constructor
      · rintro ((h | h) | ⟨y, hy, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, h⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩
      · rintro (h | ⟨y, hy, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨y, hy, h⟩

/-- Folding an intersection over a list. -/
theorem mem_foldl_inter {α : Type} (f : α → Space) (p : Path) :
    ∀ (l : List α) (init : Space),
      p ∈ l.foldl (fun acc x => inter acc (f x)) init ↔ p ∈ init ∧ ∀ x ∈ l, p ∈ f x
  | [], init => by simp
  | x :: xs, init => by
      rw [List.foldl_cons, mem_foldl_inter f p xs, mem_inter]
      constructor
      · rintro ⟨⟨h0, hx⟩, h⟩
        exact ⟨h0, fun y hy => (List.mem_cons.mp hy).elim (fun e => e ▸ hx) (h y)⟩
      · rintro ⟨h0, h⟩
        exact ⟨⟨h0, h x List.mem_cons_self⟩, fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem mem_restriction {p : Path} {x y : Space} :
    p ∈ restriction x y ↔ p ∈ x ∧ ∃ r s, p = r ++ s ∧ r ∈ y := by
  rw [restriction, PZip.restrict_eq _ unitOps_lawful, PZip.withTrie_trie, wz_focus, replaceAt_nil,
    wz_makeMap, wz_makeMap]
  by_cases hy : (wz y).val.isSome = true
  · rw [if_pos hy]
    have hy' : [] ∈ y := hy
    exact ⟨fun h => ⟨h, [], p, rfl, hy'⟩, fun h => h.1⟩
  · rw [if_neg hy, mem_def, valAt_restrictBelowRoot]
    have hy' : [] ∉ y := hy
    by_cases hv : validatedBy y p = true
    · rw [if_pos hv]
      obtain ⟨r, s, _, hrs, hr⟩ := (validatedBy_iff _ _).mp hv
      exact ⟨fun h => ⟨h, r, s, hrs, hr⟩, fun h => h.1⟩
    · rw [if_neg hv]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      rintro _ ⟨r, s, hrs, hr⟩
      apply hv
      refine (validatedBy_iff _ _).mpr ⟨r, s, ?_, hrs, hr⟩
      rintro rfl; exact hy' hr

theorem mem_composition_step {p u : Path} {acc t : Space} :
    p ∈ (((wz acc).descendTo u).joinMapInto unitOps t).2.trie ↔ p ∈ acc ∨ ∃ v, p = u ++ v ∧ v ∈ t := by
  rw [PZip.joinMapInto_eq _ unitOps_lawful, PZip.withTrie_trie, wz_descendTo_trie,
    wz_descendTo_focus, mem_def, valAt_replaceAt]
  cases hs : Path.stripPrefix u p with
  | none =>
      have hn := (Path.stripPrefix_eq_none u p).mp hs
      exact ⟨Or.inl, fun h => h.elim id (fun ⟨v, hv, _⟩ => absurd hv (hn v))⟩
  | some r =>
      have := (Path.stripPrefix_eq_some u p r).mp hs; subst this
      dsimp only
      rw [unit_join_isSome, PZip.valAt_makeMap, wz_descendTo_trie, wz_descendTo_focus,
        Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨r, rfl, h⟩
      · rintro (h | ⟨v, hv, h⟩)
        · exact Or.inl h
        · rw [List.append_cancel_left hv]; exact Or.inr h

theorem mem_composition {p : Path} {s t : Space} :
    p ∈ composition s t ↔ ∃ u v, p = u ++ v ∧ u ∈ s ∧ v ∈ t := by
  have key : ∀ (l : List Path) (init : Space),
      p ∈ l.foldl (fun acc u => (((wz acc).descendTo u).joinMapInto unitOps t).2.trie) init ↔
        p ∈ init ∨ ∃ u ∈ l, ∃ v, p = u ++ v ∧ v ∈ t := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons u us ih =>
        intro init
        rw [List.foldl_cons, ih, mem_composition_step]
        constructor
        · rintro ((h | h) | ⟨w, hw, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨u, List.mem_cons_self, h⟩
          · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h⟩
        · rintro (h | ⟨w, hw, h⟩)
          · exact Or.inl (Or.inl h)
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact Or.inl (Or.inr h)
            · exact Or.inr ⟨w, hw, h⟩
  rw [composition, key]
  simp only [not_mem_empty, false_or, mem_keys]
  constructor
  · rintro ⟨u, hu, v, rfl, hv⟩; exact ⟨u, v, rfl, hu, hv⟩
  · rintro ⟨u, v, rfl, hu, hv⟩; exact ⟨u, hu, v, rfl, hv⟩

theorem mem_head {p : Path} {s : Space} : p ∈ head s ↔ ∃ b r, p = [b] ∧ b :: r ∈ s := by
  rw [head, mem_foldl_union (fun b => singleton [b])]
  simp only [not_mem_empty, false_or, mem_singleton, mem_childMask]
  constructor
  · rintro ⟨b, ⟨r, hr⟩, rfl⟩; exact ⟨b, r, rfl, hr⟩
  · rintro ⟨b, r, rfl, hr⟩; exact ⟨b, ⟨r, hr⟩, rfl⟩

theorem mem_child {p : Path} {s : Space} {b : UInt8} :
    p ∈ ((wz s).descendToByte b).makeMap ↔ b :: p ∈ s := by
  rw [mem_def, PZip.valAt_makeMap]; rfl

theorem mem_tailsUnion {p : Path} {s : Space} : p ∈ tailsUnion s ↔ ∃ b, b :: p ∈ s := by
  rw [tailsUnion, mem_foldl_union (fun b => ((wz s).descendToByte b).makeMap)]
  simp only [not_mem_empty, false_or, mem_child, mem_childMask]
  constructor
  · rintro ⟨b, _, h⟩; exact ⟨b, h⟩
  · rintro ⟨b, h⟩; exact ⟨b, ⟨p, h⟩, h⟩

theorem mem_tailsInter {p : Path} {s : Space} :
    p ∈ tailsInter s ↔ (∃ b r, b :: r ∈ s) ∧ ∀ b, (∃ r, b :: r ∈ s) → b :: p ∈ s := by
  unfold tailsInter
  split
  · next hm =>
    simp only [not_mem_empty, false_iff, not_and]
    rintro ⟨b, r, hr⟩
    have : b ∈ (wz s).childMask := mem_childMask.mpr ⟨r, hr⟩
    rw [hm] at this; cases this
  · next b bs hm =>
    rw [mem_foldl_inter (fun c => ((wz s).descendToByte c).makeMap), mem_child]
    simp only [mem_child]
    have hmask : ∀ c, c ∈ b :: bs ↔ ∃ r, c :: r ∈ s := fun c => by rw [← hm, mem_childMask]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨⟨b, (hmask b).mp List.mem_cons_self⟩, fun c hc => ?_⟩
      rcases List.mem_cons.mp ((hmask c).mpr hc) with rfl | hc'
      · exact h0
      · exact h c hc'
    · rintro ⟨_, h⟩
      exact ⟨h b ((hmask b).mp List.mem_cons_self),
        fun c hc => h c ((hmask c).mp (List.mem_cons_of_mem _ hc))⟩

theorem mem_iterH {p : Path} {H src : Space} {body : UInt8 → Space → Space} :
    p ∈ iterH H src body ↔ ∃ h, [h] ∈ H ∧ p ∈ body h (unwrap src [h]) := by
  rw [iterH, mem_foldl_union (iterArm src body)]
  simp only [not_mem_empty, false_or, mem_keys]
  constructor
  · rintro ⟨k, hk, h⟩
    match k, hk, h with
    | [c], hk, h => exact ⟨c, hk, h⟩
    | [], _, h => exact absurd h (not_mem_empty p)
    | _ :: _ :: _, _, h => exact absurd h (not_mem_empty p)
  · rintro ⟨c, hc, h⟩; exact ⟨[c], hc, h⟩

theorem mem_iter {p : Path} {src : Space} {body : UInt8 → Space → Space} :
    p ∈ iter src body ↔ ∃ h, (∃ r, h :: r ∈ src) ∧ p ∈ body h (unwrap src [h]) := by
  rw [iter, mem_iterH]
  simp only [mem_head, List.cons.injEq, and_true]
  constructor
  · rintro ⟨h, ⟨b, r, rfl, hr⟩, hp⟩; exact ⟨h, ⟨r, hr⟩, hp⟩
  · rintro ⟨h, ⟨r, hr⟩, hp⟩; exact ⟨h, ⟨h, r, rfl, hr⟩, hp⟩

theorem mem_iterC {p : Path} {src b : Space} : p ∈ iterC src b ↔ (∃ h r, h :: r ∈ src) ∧ p ∈ b := by
  rw [iterC, mem_iter]
  constructor
  · rintro ⟨h, ⟨r, hr⟩, hp⟩; exact ⟨⟨h, r, hr⟩, hp⟩
  · rintro ⟨⟨h, r, hr⟩, hp⟩; exact ⟨h, ⟨r, hr⟩, hp⟩

theorem mem_raffination {p : Path} {x y : Space} :
    p ∈ raffination x y ↔ p ∈ x ∧ ¬ ∃ r s, p = r ++ s ∧ r ∈ y := by
  rw [raffination, mem_subtr, mem_restriction]
  constructor
  · rintro ⟨hx, hn⟩; exact ⟨hx, fun h => hn ⟨hx, h⟩⟩
  · rintro ⟨hx, hn⟩; exact ⟨hx, fun h => hn h.2⟩

/-! ## 3. Membership (`formal.egg` lines 76–88)

egg's `ElemP p s` judgment, with `EOr`/`EAnd`/`EAndNot` as `∨`/`∧`/`∧ ¬`.  The
singleton-disequality case (line 85) is negation-as-failure there, and sound
only at saturation; here it is an ordinary lemma. -/

/-- line 83 -/
theorem elemP_empty (p : Path) : p ∉ empty := not_mem_empty p
/-- line 84 -/
theorem elemP_singleton (p : Path) : p ∈ singleton p := mem_singleton.mpr rfl
/-- line 85 -/
theorem elemP_singleton_ne {p q : Path} (h : p ≠ q) : p ∉ singleton q := fun hm => h (mem_singleton.mp hm)
/-- line 86 -/
theorem elemP_union {p : Path} {a b : Space} : p ∈ union a b ↔ p ∈ a ∨ p ∈ b := mem_union
/-- line 87 -/
theorem elemP_inter {p : Path} {a b : Space} : p ∈ inter a b ↔ p ∈ a ∧ p ∈ b := mem_inter
/-- line 88 -/
theorem elemP_subtr {p : Path} {a b : Space} : p ∈ subtr a b ↔ p ∈ a ∧ p ∉ b := mem_subtr

/-! ## 4. Union, intersection, subtraction (lines 90–117)

`join_map_into`, `meet_into` and `subtract_into` at the root of a write zipper.
`Lattice.lean` already has most of these for `join`/`meet`; here they are about
the zipper programs, and subtraction is new. -/

section Boolean
variable (x y z : Space)

/-- line 90 -/
theorem union_idem : union x x = x := ext fun p => by rw [mem_union, or_self]
/-- line 91 -/
theorem inter_idem : inter x x = x := ext fun p => by rw [mem_inter, and_self]
/-- line 93 -/
theorem subtr_self : subtr x x = empty := ext fun p => by
  rw [mem_subtr]; exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (not_mem_empty p)⟩
/-- line 96 -/
theorem union_comm : union x y = union y x := ext fun p => by rw [mem_union, mem_union, or_comm]
/-- line 97 -/
theorem inter_comm : inter x y = inter y x := ext fun p => by rw [mem_inter, mem_inter, and_comm]
/-- line 99 -/
theorem union_empty : union x empty = x := ext fun p => by
  rw [mem_union]; exact ⟨fun h => h.resolve_right (not_mem_empty p), Or.inl⟩
/-- line 100 -/
theorem empty_union : union empty x = x := by rw [union_comm, union_empty]
/-- line 101 -/
theorem inter_empty : inter x empty = empty := ext fun p => by
  rw [mem_inter]; exact ⟨fun h => h.2, fun h => absurd h (not_mem_empty p)⟩
/-- line 102 -/
theorem empty_inter : inter empty x = empty := by rw [inter_comm, inter_empty]
/-- line 103 -/
theorem union_inter_distrib : inter (union x y) z = union (inter x z) (inter y z) := ext fun p => by
  simp only [mem_union, mem_inter]
  by_cases hx : p ∈ x <;> by_cases hy : p ∈ y <;> by_cases hz : p ∈ z <;> simp [hx, hy, hz]
/-- line 104 -/
theorem inter_union_distrib : inter x (union y z) = union (inter x y) (inter x z) := ext fun p => by
  simp only [mem_union, mem_inter]
  by_cases hx : p ∈ x <;> by_cases hy : p ∈ y <;> by_cases hz : p ∈ z <;> simp [hx, hy, hz]
/-- line 105 -/
theorem empty_subtr : subtr empty x = empty := ext fun p => by
  rw [mem_subtr]; exact ⟨fun h => h.1, fun h => absurd h (not_mem_empty p)⟩
/-- line 106 -/
theorem subtr_empty : subtr x empty = x := ext fun p => by
  rw [mem_subtr]; exact ⟨fun h => h.1, fun h => ⟨h, not_mem_empty p⟩⟩
/-- line 107 -/
theorem union_subtr_distrib : subtr (union x y) z = union (subtr x z) (subtr y z) := ext fun p => by
  simp only [mem_union, mem_subtr]
  by_cases hx : p ∈ x <;> by_cases hy : p ∈ y <;> by_cases hz : p ∈ z <;> simp [hx, hy, hz]
/-- line 108 -/
theorem subtr_union : subtr x (union y z) = subtr (subtr x y) z := ext fun p => by
  simp only [mem_union, mem_subtr]
  by_cases hx : p ∈ x <;> by_cases hy : p ∈ y <;> by_cases hz : p ∈ z <;> simp [hx, hy, hz]
/-- line 116 -/
theorem union_assoc : union (union x y) z = union x (union y z) := ext fun p => by
  simp only [mem_union, or_assoc]
/-- line 117 -/
theorem inter_assoc : inter (inter x y) z = inter x (inter y z) := ext fun p => by
  simp only [mem_inter, and_assoc]

end Boolean

/-- line 109 -/
theorem singleton_subtr_singleton {p q : Path} (h : p ≠ q) :
    subtr (singleton p) (singleton q) = singleton p := ext fun r => by
  simp only [mem_subtr, mem_singleton]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', fun e => h (h'.symm.trans e)⟩⟩
/-- line 110 -/
theorem singleton_inter_singleton {p q : Path} (h : p ≠ q) :
    inter (singleton p) (singleton q) = empty := ext fun r => by
  simp only [mem_inter, mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ => absurd (h1.symm.trans h2) h, fun h' => absurd h' (not_mem_empty r)⟩

/-! Paths (lines 112–115) are `List UInt8` under `++`; these are core lemmas. -/

/-- line 112 -/
theorem concat_eps (x : Path) : x ++ [] = x := List.append_nil x
/-- line 113 -/
theorem eps_concat (x : Path) : [] ++ x = x := List.nil_append x
/-- line 115 -/
theorem concat_assoc (x y z : Path) : (x ++ y) ++ z = x ++ (y ++ z) := List.append_assoc x y z

/-! ## 5. Wrap and unwrap (lines 119–153, 199–200)

`Wrap` is `graft_map` at a descended focus of an empty map; `Unwrap` is
`descend_to` then `make_map`.  egg needs the `drop-prefix` relation and ten rules
to compute `Unwrap` of a singleton; here it is one equation,
`unwrap_singleton`, and those rules are its cases. -/

/-- line 119 -/
theorem wrap_empty (x : Path) : wrap x empty = empty := ext fun p => by
  rw [mem_wrap]
  exact ⟨fun ⟨_, _, h⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 120 -/
theorem wrap_eps (s : Space) : wrap [] s = s := ext fun p => by
  rw [mem_wrap]; exact ⟨fun ⟨r, hr, h⟩ => by simpa [hr] using h, fun h => ⟨p, rfl, h⟩⟩
/-- line 121 -/
theorem wrap_singleton (x p : Path) : wrap x (singleton p) = singleton (x ++ p) := ext fun q => by
  rw [mem_wrap, mem_singleton]
  simp only [mem_singleton, exists_eq_right]
/-- line 122 -/
theorem wrap_union (x : Path) (s t : Space) : wrap x (union s t) = union (wrap x s) (wrap x t) :=
  ext fun p => by
    simp only [mem_wrap, mem_union]
    constructor
    · rintro ⟨r, rfl, h | h⟩
      · exact Or.inl ⟨r, rfl, h⟩
      · exact Or.inr ⟨r, rfl, h⟩
    · rintro (⟨r, rfl, h⟩ | ⟨r, rfl, h⟩)
      · exact ⟨r, rfl, Or.inl h⟩
      · exact ⟨r, rfl, Or.inr h⟩

/-- line 124 -/
theorem unwrap_empty (p : Path) : unwrap empty p = empty := ext fun q => by
  rw [mem_unwrap]; exact ⟨fun h => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty _)⟩
/-- line 125 -/
theorem unwrap_eps (s : Space) : unwrap s [] = s := ext fun q => by rw [mem_unwrap]; rfl
/-- line 126 -/
theorem unwrap_wrap (p : Path) (s : Space) : unwrap (wrap p s) p = s := ext fun q => by
  rw [mem_unwrap, mem_wrap]
  exact ⟨fun ⟨r, hr, h⟩ => by rwa [List.append_cancel_left hr], fun h => ⟨q, rfl, h⟩⟩
/-- line 127 -/
theorem unwrap_wrap_append (p q : Path) (s : Space) : unwrap (wrap (p ++ q) s) p = wrap q s :=
  ext fun r => by
    rw [mem_unwrap, mem_wrap, mem_wrap]
    simp only [List.append_assoc, List.append_cancel_left_eq]
/-- line 128 -/
theorem unwrap_wrap_of_append (p q : Path) (s : Space) : unwrap (wrap p s) (p ++ q) = unwrap s q :=
  ext fun r => by
    rw [mem_unwrap, mem_wrap, mem_unwrap]
    simp only [List.append_assoc, List.append_cancel_left_eq, exists_eq_left']
/-- line 129 -/
theorem unwrap_union (s t : Space) (x : Path) : unwrap (union s t) x = union (unwrap s x) (unwrap t x) :=
  ext fun q => by simp only [mem_unwrap, mem_union]
/-- line 199 -/
theorem unwrap_unwrap (s : Space) (p q : Path) : unwrap (unwrap s p) q = unwrap s (p ++ q) :=
  ext fun r => by simp only [mem_unwrap, List.append_assoc]
/-- line 200 -/
theorem unwrap_wrap_ne {a b : UInt8} (h : a ≠ b) (s : Space) : unwrap (wrap [a] s) [b] = empty :=
  ext fun q => by
    rw [mem_unwrap, mem_wrap]
    simp only [List.cons_append, List.nil_append, List.cons.injEq]
    exact ⟨fun ⟨_, ⟨e, _⟩, _⟩ => absurd e.symm h, fun h' => absurd h' (not_mem_empty q)⟩

/-- **Unwrapping a singleton** (lines 131–153, the `drop-prefix` relation).  `p`
unwraps `{w}` to `{r}` when `w = p ++ r`, and to nothing otherwise. -/
theorem unwrap_singleton (w p : Path) :
    unwrap (singleton w) p = match Path.stripPrefix p w with
      | some r => singleton r
      | none => empty := by
  apply ext; intro q
  rw [mem_unwrap, mem_singleton]
  cases hs : Path.stripPrefix p w with
  | none =>
      have hn := (Path.stripPrefix_eq_none p w).mp hs
      exact ⟨fun e => absurd e.symm (hn q), fun h => absurd h (not_mem_empty q)⟩
  | some r =>
      have := (Path.stripPrefix_eq_some p w r).mp hs; subst this
      rw [mem_singleton, List.append_cancel_left_eq]

/-- line 134: `drop-prefix ε` -/
theorem dropPrefix_eps (w : Path) : unwrap (singleton w) [] = singleton w := by
  rw [unwrap_singleton]; rfl
/-- line 136: the exact case -/
theorem dropPrefix_self (p : Path) : unwrap (singleton p) p = singleton [] := by
  rw [unwrap_singleton, PZip.stripPrefix_self]
/-- line 138: the proper-prefix case -/
theorem dropPrefix_append (p r : Path) : unwrap (singleton (p ++ r)) p = singleton r := by
  rw [unwrap_singleton, Path.stripPrefix_append]
/-- line 140: the descend case -/
theorem dropPrefix_descend (p q r : Path) :
    unwrap (singleton (p ++ r)) (p ++ q) = unwrap (singleton r) q := by
  rw [← unwrap_unwrap, dropPrefix_append]
/-- lines 142–153: every miss — the prefix is not a prefix of the path. -/
theorem dropPrefix_miss {w p : Path} (h : ∀ r, w ≠ p ++ r) : unwrap (singleton w) p = empty := by
  rw [unwrap_singleton, (Path.stripPrefix_eq_none p w).mpr h]
/-- lines 142 and 144: an item, or an item-headed path, misses `ε`. -/
theorem dropPrefix_miss_eps (a : UInt8) (p : Path) : unwrap (singleton []) (a :: p) = empty :=
  dropPrefix_miss (fun r h => by simp at h)
/-- lines 146–152: differing first items miss. -/
theorem dropPrefix_miss_item {a b : UInt8} (h : a ≠ b) (p r : Path) :
    unwrap (singleton (b :: r)) (a :: p) = empty :=
  dropPrefix_miss (fun r' e => by simp at e; exact h e.1.symm)

/-! ## 6. Composition (lines 155–160)

No `pathmap` operation computes it in one step; the program `descend_to`s each
path of the left operand and `join_map_into`s the right one there. -/

section Composition
variable (s t u : Space)

/-- line 155 -/
theorem empty_composition : composition empty t = empty := ext fun p => by
  rw [mem_composition]
  exact ⟨fun ⟨_, _, _, h, _⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 156 -/
theorem composition_empty : composition s empty = empty := ext fun p => by
  rw [mem_composition]
  exact ⟨fun ⟨_, _, _, _, h⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 157 -/
theorem union_composition : composition (union s t) u = union (composition s u) (composition t u) :=
  ext fun p => by
    simp only [mem_composition, mem_union]
    constructor
    · rintro ⟨a, b, rfl, ha | ha, hb⟩
      · exact Or.inl ⟨a, b, rfl, ha, hb⟩
      · exact Or.inr ⟨a, b, rfl, ha, hb⟩
    · rintro (⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩)
      · exact ⟨a, b, rfl, Or.inl ha, hb⟩
      · exact ⟨a, b, rfl, Or.inr ha, hb⟩
/-- line 158 -/
theorem composition_union : composition s (union t u) = union (composition s t) (composition s u) :=
  ext fun p => by
    simp only [mem_composition, mem_union]
    constructor
    · rintro ⟨a, b, rfl, ha, hb | hb⟩
      · exact Or.inl ⟨a, b, rfl, ha, hb⟩
      · exact Or.inr ⟨a, b, rfl, ha, hb⟩
    · rintro (⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩)
      · exact ⟨a, b, rfl, ha, Or.inl hb⟩
      · exact ⟨a, b, rfl, ha, Or.inr hb⟩
/-- line 160 -/
theorem singleton_composition (p : Path) : composition (singleton p) t = wrap p t := ext fun q => by
  simp only [mem_composition, mem_wrap, mem_singleton]
  constructor
  · rintro ⟨a, b, rfl, rfl, hb⟩; exact ⟨b, rfl, hb⟩
  · rintro ⟨b, rfl, hb⟩; exact ⟨p, b, rfl, rfl, hb⟩
/-- line 159 -/
theorem singleton_union_composition (p : Path) :
    composition (union (singleton p) s) t = union (wrap p t) (composition s t) := by
  rw [union_composition, singleton_composition]

end Composition

/-! ## 7. Tails, head, restriction, raffination (lines 162–198)

`TailsUnion` and `TailsIntersection` fold `join_map_into` and `meet_into` over
`child_mask`; `Head` reads `child_mask` alone.  egg's `tails-intersection` rules
(171–182) are a fold over an enumeration of the heads, and
`tailsInter_eq_foldl` is that fold for *any* enumeration, in any order, with
repeats. -/

/-- line 162 -/
theorem tailsUnion_empty : tailsUnion empty = empty := ext fun p => by
  rw [mem_tailsUnion]
  exact ⟨fun ⟨_, h⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 164 -/
theorem tailsUnion_eps : tailsUnion (singleton []) = empty := ext fun p => by
  rw [mem_tailsUnion]
  simp only [mem_singleton, reduceCtorEq, exists_false, false_iff]
  exact not_mem_empty p
/-- line 166 -/
theorem tailsUnion_cons (h : UInt8) (t : Path) : tailsUnion (singleton (h :: t)) = singleton t :=
  ext fun p => by
    simp only [mem_tailsUnion, mem_singleton, List.cons.injEq]
    exact ⟨fun ⟨_, _, e⟩ => e, fun e => ⟨h, rfl, e⟩⟩
/-- line 165 -/
theorem tailsUnion_item (h : UInt8) : tailsUnion (singleton [h]) = singleton [] := tailsUnion_cons h []
/-- line 167 -/
theorem tailsUnion_union (s t : Space) : tailsUnion (union s t) = union (tailsUnion s) (tailsUnion t) :=
  ext fun p => by
    simp only [mem_tailsUnion, mem_union]
    constructor
    · rintro ⟨b, h | h⟩
      · exact Or.inl ⟨b, h⟩
      · exact Or.inr ⟨b, h⟩
    · rintro (⟨b, h⟩ | ⟨b, h⟩)
      · exact ⟨b, Or.inl h⟩
      · exact ⟨b, Or.inr h⟩
/-- line 169 -/
theorem tailsUnion_wrap (a : UInt8) (s : Space) : tailsUnion (wrap [a] s) = s := ext fun p => by
  simp only [mem_tailsUnion, mem_wrap, List.singleton_append, List.cons.injEq]
  exact ⟨fun ⟨_, _, ⟨_, e⟩, h⟩ => e ▸ h, fun h => ⟨a, p, ⟨rfl, rfl⟩, h⟩⟩
/-- line 168 -/
theorem tailsUnion_wrap_union (a : UInt8) (s t : Space) :
    tailsUnion (union (wrap [a] s) t) = union s (tailsUnion t) := by
  rw [tailsUnion_union, tailsUnion_wrap]

/-- The head enumerations egg's fold may use: a list naming each head at least
once and nothing else. -/
def EnumHeads (x : Space) (hs : List UInt8) : Prop := ∀ c, c ∈ hs ↔ [c] ∈ head x

theorem enumHeads_iff {x : Space} {hs : List UInt8} :
    EnumHeads x hs ↔ ∀ c, c ∈ hs ↔ ∃ r, c :: r ∈ x := by
  unfold EnumHeads
  simp only [mem_head, List.cons.injEq, and_true]
  constructor
  · intro h c; rw [h c]; exact ⟨fun ⟨_, r, rfl, hr⟩ => ⟨r, hr⟩, fun ⟨r, hr⟩ => ⟨c, r, rfl, hr⟩⟩
  · intro h c; rw [h c]; exact ⟨fun ⟨r, hr⟩ => ⟨c, r, rfl, hr⟩, fun ⟨_, r, rfl, hr⟩ => ⟨r, hr⟩⟩

/-- line 173: no heads, no tails. -/
theorem tailsInter_of_head_empty {x : Space} (h : head x = empty) : tailsInter x = empty :=
  ext fun p => by
    rw [mem_tailsInter]
    refine ⟨fun ⟨⟨b, r, hr⟩, _⟩ => ?_, fun h' => absurd h' (not_mem_empty p)⟩
    have : [b] ∈ head x := mem_head.mpr ⟨b, r, rfl, hr⟩
    rw [h] at this; exact absurd this (not_mem_empty _)

/-- lines 177–182: egg's accumulating fold, `tails-intersection-acc`, over any
enumeration `h :: rest` of the heads. -/
theorem tailsInter_eq_foldl {x : Space} {h : UInt8} {rest : List UInt8}
    (he : EnumHeads x (h :: rest)) :
    tailsInter x = rest.foldl (fun acc c => inter acc (unwrap x [c])) (unwrap x [h]) := by
  have he' := enumHeads_iff.mp he
  apply ext; intro p
  rw [mem_tailsInter, mem_foldl_inter (fun c => unwrap x [c]), mem_unwrap]
  simp only [mem_unwrap, List.singleton_append]
  constructor
  · rintro ⟨_, hall⟩
    exact ⟨hall h ((he' h).mp List.mem_cons_self),
      fun c hc => hall c ((he' c).mp (List.mem_cons_of_mem _ hc))⟩
  · rintro ⟨h0, hall⟩
    refine ⟨⟨h, (he' h).mp List.mem_cons_self⟩, fun c hc => ?_⟩
    rcases List.mem_cons.mp ((he' c).mpr hc) with rfl | hc'
    · exact h0
    · exact hall c hc'

/-- line 175: one head. -/
theorem tailsInter_of_head_singleton {x : Space} {h : UInt8} (hh : head x = singleton [h]) :
    tailsInter x = unwrap x [h] := by
  rw [tailsInter_eq_foldl (rest := [])]
  · rfl
  · intro c; rw [hh, mem_singleton]; simp

/-- line 184 -/
theorem restriction_empty_left (y : Space) : restriction empty y = empty := ext fun p => by
  rw [mem_restriction]; exact ⟨fun h => h.1, fun h => absurd h (not_mem_empty p)⟩
/-- line 185 -/
theorem restriction_empty_right (x : Space) : restriction x empty = empty := ext fun p => by
  rw [mem_restriction]
  exact ⟨fun ⟨_, _, _, _, h⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 186 -/
theorem restriction_eps (x : Space) : restriction x (singleton []) = x := ext fun p => by
  rw [mem_restriction]
  exact ⟨fun h => h.1, fun h => ⟨h, [], p, rfl, mem_singleton.mpr rfl⟩⟩
/-- line 187 -/
theorem restriction_union (x p q : Space) :
    restriction x (union p q) = union (restriction x p) (restriction x q) := ext fun r => by
  simp only [mem_restriction, mem_union]
  constructor
  · rintro ⟨hx, a, b, rfl, ha | ha⟩
    · exact Or.inl ⟨hx, a, b, rfl, ha⟩
    · exact Or.inr ⟨hx, a, b, rfl, ha⟩
  · rintro (⟨hx, a, b, rfl, ha⟩ | ⟨hx, a, b, rfl, ha⟩)
    · exact ⟨hx, a, b, rfl, Or.inl ha⟩
    · exact ⟨hx, a, b, rfl, Or.inr ha⟩
/-- line 188 -/
theorem restriction_singleton (x : Space) (p : Path) :
    restriction x (singleton p) = wrap p (unwrap x p) := ext fun q => by
  simp only [mem_restriction, mem_wrap, mem_unwrap, mem_singleton]
  constructor
  · rintro ⟨hx, a, b, rfl, rfl⟩; exact ⟨b, rfl, hx⟩
  · rintro ⟨b, rfl, hx⟩; exact ⟨hx, p, b, rfl, rfl⟩
/-- line 197: every path of `x` has itself as a prefix. -/
theorem restriction_self (x : Space) : restriction x x = x := ext fun p => by
  rw [mem_restriction]; exact ⟨fun h => h.1, fun h => ⟨h, p, [], by simp, h⟩⟩

/-- line 190 -/
theorem head_empty : head empty = empty := ext fun p => by
  rw [mem_head]
  exact ⟨fun ⟨_, _, _, h⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 191 -/
theorem head_eps : head (singleton []) = empty := ext fun p => by
  rw [mem_head]
  simp only [mem_singleton, reduceCtorEq, and_false, exists_false, false_iff]
  exact not_mem_empty p
/-- line 192 -/
theorem head_union (x y : Space) : head (union x y) = union (head x) (head y) := ext fun p => by
  simp only [mem_head, mem_union]
  constructor
  · rintro ⟨b, r, rfl, h | h⟩
    · exact Or.inl ⟨b, r, rfl, h⟩
    · exact Or.inr ⟨b, r, rfl, h⟩
  · rintro (⟨b, r, rfl, h⟩ | ⟨b, r, rfl, h⟩)
    · exact ⟨b, r, rfl, Or.inl h⟩
    · exact ⟨b, r, rfl, Or.inr h⟩
/-- line 193 -/
theorem head_cons (h : UInt8) (t : Path) : head (singleton (h :: t)) = singleton [h] := ext fun p => by
  simp only [mem_head, mem_singleton, List.cons.injEq]
  exact ⟨fun ⟨_, _, e, rfl, _⟩ => e, fun e => ⟨h, t, e, rfl, rfl⟩⟩
/-- line 194 -/
theorem head_item (h : UInt8) : head (singleton [h]) = singleton [h] := head_cons h []

/-- line 198: raffination is *defined* as `x \ (x <| y)`. -/
theorem raffination_def (x y : Space) : raffination x y = subtr x (restriction x y) := rfl
/-- line 198's consequence. -/
theorem raffination_self (x : Space) : raffination x x = empty := by
  rw [raffination_def, restriction_self, subtr_self]

/-! ## 8. Iteration (lines 202–242)

`IterC` is `Iter` with a body that ignores its arguments, so its rules are
instances of `Iter`'s.  egg's comment on rule L2 makes a point worth keeping:
`IterH` distributes over a union of its *head set*, with the source held fixed;
`Iter` does **not** distribute over a union of its *source*, because a head
shared by the two operands merges their groups and the body sees the merge.
`iter_not_union_source` is that refutation (egg's N05). -/

/-- line 239 (L1) -/
theorem iter_def (src : Space) (body : UInt8 → Space → Space) :
    iter src body = iterH (head src) src body := rfl
/-- line 240 (L4) -/
theorem iterH_empty (src : Space) (body : UInt8 → Space → Space) : iterH empty src body = empty :=
  ext fun p => by
    rw [mem_iterH]
    exact ⟨fun ⟨_, h, _⟩ => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty p)⟩
/-- line 241 (L2) -/
theorem iterH_union (a c src : Space) (body : UInt8 → Space → Space) :
    iterH (union a c) src body = union (iterH a src body) (iterH c src body) := ext fun p => by
  simp only [mem_iterH, mem_union]
  constructor
  · rintro ⟨h, ha | ha, hp⟩
    · exact Or.inl ⟨h, ha, hp⟩
    · exact Or.inr ⟨h, ha, hp⟩
  · rintro (⟨h, ha, hp⟩ | ⟨h, ha, hp⟩)
    · exact ⟨h, Or.inl ha, hp⟩
    · exact ⟨h, Or.inr ha, hp⟩
/-- line 242 (L3) -/
theorem iterH_item (h : UInt8) (src : Space) (body : UInt8 → Space → Space) :
    iterH (singleton [h]) src body = body h (unwrap src [h]) := ext fun p => by
  simp only [mem_iterH, mem_singleton, List.cons.injEq, and_true]
  exact ⟨fun ⟨_, e, hp⟩ => e ▸ hp, fun hp => ⟨h, rfl, hp⟩⟩

/-- N05: iteration does not distribute over a union of its source.  `a` and `c`
share the head `1`; the body asks whether its group holds both `[0]` and `[1]`,
which only the merged group does. -/
theorem iter_not_union_source :
    ¬ ∀ (a c : Space) (body : UInt8 → Space → Space),
      iter (union a c) body = union (iter a body) (iter c body) := by
  intro hall
  let body : UInt8 → Space → Space := fun _ g => if [0] ∈ g ∧ [1] ∈ g then singleton [] else empty
  have e := hall (singleton [1, 0]) (singleton [1, 1]) body
  have hl : [] ∈ iter (union (singleton [1, 0]) (singleton [1, 1])) body := by
    rw [mem_iter]
    refine ⟨1, ⟨[0], mem_union.mpr (Or.inl (mem_singleton.mpr rfl))⟩, ?_⟩
    have h0 : [0] ∈ unwrap (union (singleton [1, 0]) (singleton [1, 1])) [1] :=
      mem_unwrap.mpr (mem_union.mpr (Or.inl (mem_singleton.mpr rfl)))
    have h1 : [1] ∈ unwrap (union (singleton [1, 0]) (singleton [1, 1])) [1] :=
      mem_unwrap.mpr (mem_union.mpr (Or.inr (mem_singleton.mpr rfl)))
    show [] ∈ (if _ then _ else _)
    rw [if_pos ⟨h0, h1⟩]; exact mem_singleton.mpr rfl
  have hr : [] ∉ union (iter (singleton [1, 0]) body) (iter (singleton [1, 1]) body) := by
    rw [mem_union, mem_iter, mem_iter]
    rintro (⟨h, _, hp⟩ | ⟨h, _, hp⟩)
    · show False
      revert hp; show [] ∈ (if _ then _ else _) → False
      rw [if_neg]
      · exact not_mem_empty _
      · rintro ⟨_, h1⟩
        have := mem_singleton.mp (mem_unwrap.mp h1); simp at this
    · show False
      revert hp; show [] ∈ (if _ then _ else _) → False
      rw [if_neg]
      · exact not_mem_empty _
      · rintro ⟨h0, _⟩
        have := mem_singleton.mp (mem_unwrap.mp h0); simp at this
  exact hr (e ▸ hl)

/-- line 204 -/
theorem iterC_empty (b : Space) : iterC empty b = empty := by
  rw [iterC, iter_def, head_empty, iterH_empty]
/-- line 205: a `{ε}` source has no heads (the case egg's prover caught). -/
theorem iterC_eps (b : Space) : iterC (singleton []) b = empty := by
  rw [iterC, iter_def, head_eps, iterH_empty]
/-- line 207 -/
theorem iterC_cons (h : UInt8) (t : Path) (b : Space) : iterC (singleton (h :: t)) b = b := by
  rw [iterC, iter_def, head_cons, iterH_item]
/-- line 206 -/
theorem iterC_item (h : UInt8) (b : Space) : iterC (singleton [h]) b = b := iterC_cons h [] b
/-- line 208: the source *does* distribute when the body cannot see its group. -/
theorem iterC_union (s t b : Space) : iterC (union s t) b = union (iterC s b) (iterC t b) :=
  ext fun p => by
    simp only [mem_iterC, mem_union]
    constructor
    · rintro ⟨⟨h, r, hr | hr⟩, hp⟩
      · exact Or.inl ⟨⟨h, r, hr⟩, hp⟩
      · exact Or.inr ⟨⟨h, r, hr⟩, hp⟩
    · rintro (⟨⟨h, r, hr⟩, hp⟩ | ⟨⟨h, r, hr⟩, hp⟩)
      · exact ⟨⟨h, r, Or.inl hr⟩, hp⟩
      · exact ⟨⟨h, r, Or.inr hr⟩, hp⟩

/-! ## 9. Least fixpoints (lines 244–292)

egg introduces `Fix i F` as a first-class term and *axiomatises* it with three
rules: it contains `i` (line 288), it contains `F` of itself (line 289), and it
is below every `c` that does both (Park induction, line 291).  Those rules are a
definition, so here they are the fields of a predicate, `IsLeastPostFix`, and
egg's `⊑` is its own encoding, `Union a c = c`.

What egg's comment argues and does not mechanise is that the executors compute
this: they iterate the *inflationary* operator `cur ↦ cur ∪ F cur` until it
stops changing, and when `F` is monotone the value it stops at is the least
post-fixpoint above `i`.  `kleene_isLeastPostFix` proves that.  Monotonicity is
used only for leastness, as egg's comment says. -/

/-- egg's `⊑`: `Union a b = b`. -/
theorem union_eq_right_iff {a b : Space} : union a b = b ↔ ∀ p, p ∈ a → p ∈ b := by
  constructor
  · intro h p hp; rw [← h]; exact mem_union.mpr (Or.inl hp)
  · intro h; exact ext fun p => by
      rw [mem_union]; exact ⟨fun h' => h'.elim (h p) id, Or.inr⟩

/-- `X` is the least post-fixpoint of `F` above `i`: egg's `Fix i F`. -/
structure IsLeastPostFix (i : Space) (F : Space → Space) (X : Space) : Prop where
  /-- line 288: `Fix ⊒ init` -/
  init : union i X = X
  /-- line 289: `Fix ⊒ F(Fix)` -/
  post : union (F X) X = X
  /-- line 291: Park induction -/
  park : ∀ c, union i c = c → union (F c) c = c → union X c = c

/-- The least post-fixpoint is unique, so `Fix i F` is well defined. -/
theorem IsLeastPostFix.unique {i X Y : Space} {F : Space → Space}
    (hX : IsLeastPostFix i F X) (hY : IsLeastPostFix i F Y) : X = Y := by
  have h1 := union_eq_right_iff.mp (hX.park Y hY.init hY.post)
  have h2 := union_eq_right_iff.mp (hY.park X hX.init hX.post)
  exact ext fun p => ⟨h1 p, h2 p⟩

/-- line 287 and the tour's line 436: with the identity step, `Fix i (λX.X) = i`. -/
theorem fix_self (i : Space) : IsLeastPostFix i id i where
  init := union_idem i
  post := union_idem i
  park _ h _ := h

/-- `F` preserves `⊑`. -/
def Monotone (F : Space → Space) : Prop := ∀ a b, union a b = b → union (F a) (F b) = F b

/-- The executors' loop: `cur := cur ∪ F(cur)`. -/
def kleene (i : Space) (F : Space → Space) : Nat → Space
  | 0 => i
  | n + 1 => union (kleene i F n) (F (kleene i F n))

theorem init_le_kleene (i : Space) (F : Space → Space) : ∀ n p, p ∈ i → p ∈ kleene i F n
  | 0, _, h => h
  | n + 1, p, h => mem_union.mpr (Or.inl (init_le_kleene i F n p h))

/-- **The loop computes `Fix`.**  When the inflationary iteration stops changing
and `F` is monotone, where it stopped is the least post-fixpoint above `i`. -/
theorem kleene_isLeastPostFix {i : Space} {F : Space → Space} (hF : Monotone F) {n : Nat}
    (hn : kleene i F (n + 1) = kleene i F n) : IsLeastPostFix i F (kleene i F n) where
  init := union_eq_right_iff.mpr (init_le_kleene i F n)
  post := by
    rw [union_comm]; exact hn
  park c hi hc := by
    have hi' := union_eq_right_iff.mp hi
    have hc' := union_eq_right_iff.mp hc
    have key : ∀ m p, p ∈ kleene i F m → p ∈ c := by
      intro m
      induction m with
      | zero => exact hi'
      | succ m ih =>
          intro p hp
          rcases mem_union.mp hp with h | h
          · exact ih p h
          · have hm := union_eq_right_iff.mp (hF _ _ (union_eq_right_iff.mpr ih))
            exact hc' p (hm p h)
    exact union_eq_right_iff.mpr (key n)

/-! ## 10. The raw zipper operations are the set operators

`Refine.lean` says exactly what each write operation puts at its focus.  Before
issue #104, `join_into`, `restrict`, `insert_prefix` and `join_k_path_into`
worked on the node below the focus and so missed the focus value, and
`meet_k_path_into` kept the focus value when its meet was empty.  On this branch
each carries the focus value with the subtrie, and each is its egg operator
outright. -/

/-- `join_into` is `Union`. -/
theorem joinInto_eq_union (a b : Space) : ((wz a).joinInto unitOps (wz b)).2.trie = union a b := by
  rw [PZip.joinInto_eq _ unitOps_lawful, PZip.withTrie_trie, wz_focus, replaceAt_nil, wz_makeMap,
    wz_makeMap, union_eq_join]

/-- `restrict` is `Restriction` — by definition (§1), and `mem_restriction` is the
membership law egg states for it. -/
theorem restrict_eq_restriction (x y : Space) :
    ((wz x).restrict unitOps (wz y)).2.trie = restriction x y := rfl

/-- `insert_prefix p` is `Wrap p`. -/
theorem insertPrefix_eq_wrap (pre : Path) (s : Space) : ((wz s).insertPrefix pre).2.trie = wrap pre s :=
  ext fun p => by
    rw [PZip.insertPrefix_eq, PZip.withTrie_trie, wz_focus, replaceAt_nil, wz_makeMap, mem_wrap,
      mem_def, valAt_prepend]
    cases hs : Path.stripPrefix pre p with
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
        intro r hr; exact absurd hr ((Path.stripPrefix_eq_none pre p).mp hs r)
    | some r =>
        have := (Path.stripPrefix_eq_some pre p r).mp hs; subst this
        constructor
        · intro h; exact ⟨r, rfl, h⟩
        · rintro ⟨r', hr', h⟩
          rw [List.append_cancel_left hr']; exact h

/-- The locations one byte down are the heads. -/
theorem mem_kPaths_one {s : Space} {q : Path} : q ∈ s.kPaths 1 ↔ ∃ b r, q = [b] ∧ b :: r ∈ s := by
  rw [kPaths, List.mem_filter, PrunedMap.paths, Path.mem_sortDedup]
  constructor
  · rintro ⟨hm, hl⟩
    have hl : q.length = 1 := by simpa using hl
    rcases List.mem_cons.mp hm with rfl | hm
    · cases hl
    · obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hm
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hq
      match k, n with
      | [], _ => simp at hl
      | _ :: _, 0 => simp at hl
      | b :: r, n + 1 =>
          refine ⟨b, r, ?_, mem_keys.mp hk⟩
          simp only [List.take_succ_cons, List.length_cons, Nat.add_eq_right,
            List.length_eq_zero_iff] at hl ⊢
          rw [hl]
  · rintro ⟨b, r, rfl, h⟩
    refine ⟨List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b :: r, mem_keys.mpr h, ?_⟩), rfl⟩
    exact List.mem_map.mpr ⟨1, List.mem_range.mpr (by simp), rfl⟩

/-- `join_k_path_into 1` is `TailsUnion`. -/
theorem joinKPathInto_one_eq_tailsUnion (s : Space) :
    ((wz s).joinKPathInto unitOps 1).2.trie = tailsUnion s := ext fun p => by
  rw [PZip.joinKPathInto_eq, if_neg (by decide), PZip.withTrie_trie, wz_focus, replaceAt_nil,
    wz_makeMap, mem_tailsUnion, dropHead, if_neg (by decide)]
  have hf : (fun acc q => join unitOps acc (s.subtrie q)) = (fun acc q => union acc (s.subtrie q)) := by
    funext acc q; rw [union_eq_join]
  rw [hf, mem_foldl_union (fun q => s.subtrie q), or_iff_right (show p ∉ (PrunedMap.empty : Space) from not_mem_empty p)]
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨b, r, rfl, _⟩ := mem_kPaths_one.mp hq
    refine ⟨b, ?_⟩
    rw [mem_def, valAt_subtrie] at hp; exact hp
  · rintro ⟨b, h⟩
    refine ⟨[b], mem_kPaths_one.mpr ⟨b, p, rfl, h⟩, ?_⟩
    rw [mem_def, valAt_subtrie]; exact h

theorem mem_meet {p : Path} {a b : Space} : p ∈ meet unitOps a b ↔ p ∈ a ∧ p ∈ b := by
  rw [mem_def, unit_meet_isSome, Bool.and_eq_true]; rfl

theorem foldl_meetStep_eq_none (s : Space) : ∀ (L : List Path) (acc : Option Space),
    L.foldl (PZip.meetStep unitOps s []) acc = none ↔ acc = none ∧ L = []
  | [], acc => by simp
  | q :: L, acc => by
      rw [List.foldl_cons, foldl_meetStep_eq_none s L]
      cases acc <;> simp [PZip.meetStep]

theorem mem_foldl_meetStep (s : Space) (p : Path) : ∀ (L : List Path) (acc : Option Space) (M : Space),
    L.foldl (PZip.meetStep unitOps s []) acc = some M →
      (p ∈ M ↔ (∀ a, acc = some a → p ∈ a) ∧ ∀ q ∈ L, q ++ p ∈ s)
  | [], acc, M, h => by
      simp only [List.foldl_nil] at h; subst h
      simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨fun hp a ha => by cases ha; exact hp, fun h => h M rfl⟩
  | q :: L, acc, M, h => by
      rw [List.foldl_cons] at h
      rw [mem_foldl_meetStep s p L _ M h, List.forall_mem_cons]
      have hq : p ∈ s.subtrie ([] ++ q) ↔ q ++ p ∈ s := by rw [mem_def, valAt_subtrie]; simp; rfl
      cases acc with
      | none =>
          simp only [PZip.meetStep, Option.some.injEq, forall_eq', reduceCtorEq, false_imp_iff,
            implies_true, true_and]
          rw [hq]
      | some a0 =>
          simp only [PZip.meetStep, Option.some.injEq, forall_eq']
          rw [mem_meet, hq, and_assoc]

/-- `meet_k_path_into 1` is `TailsIntersection`. -/
theorem meetKPathInto_one_eq_tailsInter (s : Space) :
    ((wz s).meetKPathInto unitOps 1).2.trie = tailsInter s := ext fun p => by
  rw [PZip.meetKPathInto_snd, PZip.graftMap_eq, PZip.withTrie_trie, wz_focus, replaceAt_nil,
    mem_tailsInter]
  simp only [wz_trie]
  rw [subtrie_nil]
  cases h : (s.kPaths 1).foldl (PZip.meetStep unitOps s []) none with
  | none =>
      have hL := ((foldl_meetStep_eq_none s _ _).mp h).2
      simp only [Option.getD_none]
      refine ⟨fun hp => absurd hp (not_mem_empty p), ?_⟩
      rintro ⟨⟨b, r, hb⟩, _⟩
      have := mem_kPaths_one.mpr ⟨b, r, rfl, hb⟩
      rw [hL] at this; cases this
  | some M =>
      simp only [Option.getD_some]
      rw [mem_foldl_meetStep s p _ _ M h]
      have hne : s.kPaths 1 ≠ [] := fun e => by
        rw [e] at h; cases h
      obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨b0, r0, -, hb0⟩ := mem_kPaths_one.mp hq0
      simp only [reduceCtorEq, false_imp_iff, implies_true, true_and]
      constructor
      · intro hall
        refine ⟨⟨b0, r0, hb0⟩, fun b ⟨r, hr⟩ => ?_⟩
        exact hall [b] (mem_kPaths_one.mpr ⟨b, r, rfl, hr⟩)
      · rintro ⟨_, hall⟩ q hq
        obtain ⟨b, r, rfl, hr⟩ := mem_kPaths_one.mp hq
        exact hall b ⟨r, hr⟩

/-! ## 11. The tour (lines 294–436)

Every `(check (= a b))` is a `#guard a == b`, every `(fail (check …))` a
`#guard … != …`.  Items are bytes; the letters are egg's `a..z = 10..35`. -/

section Tour

private def it (a : UInt8) : Space := singleton [a]
private def expr1 := union (it 10) (it 11)
private def expr2 := wrap [18] expr1
private def expr3 := union (singleton [18, 10]) (singleton [18, 11])
private def expr4 := unwrap expr3 [18]
private def expr_qi : Path := [26, 18]
private def expr_qi_unwrap := unwrap (wrap expr_qi expr1) expr_qi
private def expr_unwrap_prefix := unwrap (singleton [10, 11]) [10]
private def expr_unwrap_exact := unwrap (singleton [10, 11]) [10, 11]
private def expr_unwrap_miss := unwrap (singleton [10]) [11]
private def expr1_ := union (it 33) (it 34)
private def expr_prod := composition expr1_ expr1
private def expr_prod_expanded :=
  union (union (singleton [33, 10]) (singleton [33, 11])) (union (singleton [34, 10]) (singleton [34, 11]))
private def expr_tailsunion1 := tailsUnion expr_prod_expanded
private def expr_tailsintersection1 := tailsInter expr_prod_expanded
private def expr1_head := head expr1
private def expr3_head := head expr3
private def expr_prod_head := head expr_prod_expanded
private def expr_s0 := it 0
private def expr_restriction_keys :=
  union (union (composition expr1 (it 0)) (composition (union (it 10) (union (it 12) (it 13))) (it 1)))
    (composition (it 12) (it 2))
private def expr_restriction := restriction expr_restriction_keys expr1
private def expr_restriction_tailsintersection := tailsInter expr_restriction
private def expr_restriction_res1 :=
  union (union (singleton [10, 0]) (singleton [10, 1])) (singleton [11, 0])
private def expr_restriction_multi :=
  restriction (union (wrap [10] (it 0)) (wrap [11] (it 1))) (union (it 10) (it 11))
private def expr_restriction_multi_res := union (singleton [10, 0]) (singleton [11, 1])
private def expr_restriction_multi_only_a := singleton [10, 0]
private def expr_tailsintersection_duplicate_heads :=
  tailsInter (union (union (wrap [10] (it 0)) (wrap [10] (it 1))) (wrap [11] (it 0)))
private def restr_self := restriction expr1 expr1
private def raff_self := raffination expr1 expr1
private def unwrap_chain := unwrap (unwrap (singleton [10, 11, 12]) [10]) [11]
private def wrap_unwrap_miss := unwrap (wrap [32] expr1) [10]
private def tails_single := tailsUnion (singleton [10, 11])
private def iu_body := union (it 21) (it 27)
private def iu_orig_empty := iterC empty iu_body
private def iu_distr_empty := union (iterC empty (it 21)) (iterC empty (it 27))
private def iu_hoist_empty := union (it 21) (iterC empty (it 27))

#guard expr2 == expr3
#guard expr1 == expr4
#guard expr_qi_unwrap == expr1
#guard expr_unwrap_prefix == it 11
#guard expr_unwrap_exact == singleton []
#guard expr_unwrap_miss == empty
#guard expr_prod == expr_prod_expanded
#guard expr_tailsunion1 == expr1
#guard expr_tailsintersection1 == expr1
#guard expr_restriction == expr_restriction_res1
#guard expr_restriction_tailsintersection == expr_s0
#guard expr_restriction_multi == expr_restriction_multi_res
#guard expr_restriction_multi != expr_restriction_multi_only_a
#guard expr_tailsintersection_duplicate_heads == expr_s0
#guard expr_tailsintersection_duplicate_heads != empty
#guard restr_self == expr1
#guard raff_self == empty
#guard unwrap_chain == it 12
#guard wrap_unwrap_miss == empty
#guard tails_single == it 11
#guard expr1_head == expr1
#guard expr3_head == it 18
#guard expr_prod_head == expr1_
#guard iu_orig_empty == empty
#guard iu_orig_empty == iu_distr_empty
#guard iu_orig_empty != iu_hoist_empty

/-- The tour's step `F(X) = X ∪ {b}` (line 391). -/
private def step900 (x : Space) : Space := union x (it 11)

private theorem step900_mono : Monotone step900 := by
  intro a b h
  rw [union_eq_right_iff] at h ⊢
  intro p hp
  simp only [step900, mem_union] at hp ⊢
  exact hp.elim (fun h' => Or.inl (h p h')) Or.inr

/-- line 434: `Fix({a,b}, X ↦ X ∪ {b}) = {a,b}`, as the executors' loop reaches it. -/
theorem fix_ab : IsLeastPostFix expr1 step900 expr1 := by
  have h : kleene expr1 step900 1 = kleene expr1 step900 0 := by
    show union expr1 (union expr1 (it 11)) = expr1
    rw [← union_assoc, union_idem, union_comm, union_eq_right_iff]
    intro p hp; exact mem_union.mpr (Or.inr (mem_singleton.mp hp ▸ mem_singleton.mpr rfl))
  exact kleene_isLeastPostFix step900_mono h

/-- line 435: `{a}` is not it — Park must not fire there, because `{a}` is not
above the initial value. -/
theorem fix_not_too_small : ¬ IsLeastPostFix expr1 step900 (it 10) := by
  intro h
  have := fix_ab.unique h
  have hb : [11] ∈ expr1 := mem_union.mpr (Or.inr (mem_singleton.mpr rfl))
  rw [this] at hb
  exact absurd (mem_singleton.mp hb) (by decide)

end Tour

end Zippy
end PrunedModel
