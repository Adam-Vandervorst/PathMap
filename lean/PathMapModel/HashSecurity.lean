import Std.Tactic.BVDecide
import PathMapModel.Hash

/-!
# Soundness of the hashing scheme

`Hash.lean` defines the logical trie hash as a Merkle tree over an abstract primitive.  This
file proves that the *scheme* adds no weakness of its own: if two tries that differ as
logical tries hash alike, then two different **messages** were handed to the primitive and
came back with the same digest.  Any collision resistance the primitive has therefore
transfers to the trie hash.  Nothing here is about the primitive itself (the crate's gxhash
makes no collision-resistance claim, and the harness's FNV-1a certainly does not); the
primitive is a parameter `H`, and the theorems hold for every `H`.

The argument is the usual one for Merkle trees, and it rests on the messages being
**decodable**:

* a node message is `N`, the 32-byte mask bitmap, then 8 bytes per child, so the tag
  separates it from a value message, the bitmap determines the child set and hence how
  many digests follow, and each digest can be cut out by its fixed width;
* a value message is `V`, 8 bytes of the hash below, 8 bytes of the value hash;
* running out of fuel yields `H []`, and the empty message is neither of the above.

The exact statements:

* `hashWith_inj_imp_logicalEq`: for an injective `H` and an injective value hash, equal
  hashes at two positions mean the two subtries are observationally equal
  (`LogicalEq`: same value at the position, same `Entry` at every path strictly below).
* `collision_of_hash_eq`: the classical contrapositive, with no assumption on `H` -- equal
  hashes of unequal subtries exhibit a collision of `H` or of the value hash.
* `fnv_collision_of_hashU64_eq`: the instance for the harness's `hashU64`, where the value
  hash is itself `fnv` over the value's bytes, so a collision is always an `fnv` collision.

Two points the statements make explicit.  The hash at a position does not see whether the
position itself exists: a dangling endpoint and an absent one both hash as the empty node,
because a location's existence is recorded in its parent's mask.  At the root this is moot
(the root always exists), which is why the root corollary yields full equality.  And the
value type's encoding is assumed injective (`vh` injective, or for `hashU64`, `leBytes64`
injective); that is the crate's `Hash` impl, not the scheme.
-/

namespace PathMapModel
namespace Hash

open Function

/-! ## The scheme over an arbitrary primitive -/

/-- The message a logical node with mask `m` and child digests `children` is hashed from. -/
def nodeMsg (m : ByteMask) (children : List UInt64) : List UInt8 :=
  0x4E :: (maskBytes m ++ (children.map leBytes64).flatten)

/-- The message a value is layered on with. -/
def valMsg (vh below : UInt64) : List UInt8 :=
  0x56 :: (leBytes64 below ++ leBytes64 vh)

/-- `hashFuel` with an arbitrary primitive `H` in place of `fnv`. -/
def hashWith {V : Type} (H : List UInt8 → UInt64) (vh : V → UInt64) (t : PathMap V) :
    Nat → Path → UInt64
  | 0, _ => H []
  | fuel + 1, p =>
      let m := t.childMask p
      let below := H (nodeMsg m (m.map fun b => hashWith H vh t fuel (p ++ [b])))
      match t.valAt p with
      | some v => H (valMsg (vh v) below)
      | none => below

/-- The hash of what lies strictly below `p`, at `fuel + 1`. -/
def belowOf {V : Type} (H : List UInt8 → UInt64) (vh : V → UInt64) (t : PathMap V)
    (fuel : Nat) (p : Path) : UInt64 :=
  H (nodeMsg (t.childMask p) ((t.childMask p).map fun b => hashWith H vh t fuel (p ++ [b])))

theorem hashWith_succ {V : Type} (H : List UInt8 → UInt64) (vh : V → UInt64) (t : PathMap V)
    (fuel : Nat) (p : Path) :
    hashWith H vh t (fuel + 1) p =
      match t.valAt p with
      | some v => H (valMsg (vh v) (belowOf H vh t fuel p))
      | none => belowOf H vh t fuel p := rfl

/-! ## `hashFuel` is `hashWith fnv` -/

theorem absorbBytes_cons (h : UInt64) (b : UInt8) (bs : List UInt8) :
    absorbBytes h (b :: bs) = absorbBytes (absorb h b) bs := rfl

theorem absorbBytes_append (h : UInt64) (a b : List UInt8) :
    absorbBytes h (a ++ b) = absorbBytes (absorbBytes h a) b := by
  simp [absorbBytes, List.foldl_append]

theorem absorbBytes_flatten (h : UInt64) (cs : List UInt64) :
    absorbBytes h (cs.map leBytes64).flatten =
      cs.foldl (fun h c => absorbBytes h (leBytes64 c)) h := by
  induction cs generalizing h with
  | nil => rfl
  | cons c cs ih => simp [List.flatten_cons, absorbBytes_append, ih]

theorem node_eq_fnv (m : ByteMask) (cs : List UInt64) : node m cs = fnv (nodeMsg m cs) := by
  simp only [node, fnv, nodeMsg, absorbBytes_cons, absorbBytes_append, absorbBytes_flatten]

theorem withValue_eq_fnv (vh below : UInt64) : withValue vh below = fnv (valMsg vh below) := by
  simp only [withValue, fnv, valMsg, absorbBytes_cons, absorbBytes_append]

theorem hashFuel_eq_hashWith {V : Type} (vh : V → UInt64) (t : PathMap V) :
    ∀ (fuel : Nat) (p : Path), hashFuel vh t fuel p = hashWith fnv vh t fuel p
  | 0, _ => rfl
  | fuel + 1, p => by
      rw [hashWith_succ]
      have hk : (t.childMask p).map (fun b => hashFuel vh t fuel (p ++ [b])) =
          (t.childMask p).map (fun b => hashWith fnv vh t fuel (p ++ [b])) :=
        List.map_congr_left fun b _ => hashFuel_eq_hashWith vh t fuel (p ++ [b])
      simp only [hashFuel, belowOf, node_eq_fnv, withValue_eq_fnv, hk]
      cases t.valAt p <;> rfl

/-! ## Decodability of the messages -/

theorem length_leBytes64 (x : UInt64) : (leBytes64 x).length = 8 := rfl

theorem length_maskBytes (m : ByteMask) : (maskBytes m).length = 32 := by
  simp [maskBytes]

/-- Eight little-endian bytes determine the word. -/
theorem leBytes64_inj : Injective leBytes64 := by
  intro x y h
  simp only [leBytes64, List.cons.injEq, and_true] at h
  bv_decide

theorem digits_lt : ∀ (l : List Bool), digits l < 2 ^ l.length
  | [] => by simp [digits]
  | b :: l => by
      have := digits_lt l
      cases b <;> simp [digits, Nat.pow_succ] <;> omega

theorem digits_inj : ∀ (l₁ l₂ : List Bool), l₁.length = l₂.length → digits l₁ = digits l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | b₁ :: l₁, b₂ :: l₂, hl, hd => by
      simp only [digits] at hd
      have hl' : l₁.length = l₂.length := by simpa using hl
      have hb : b₁ = b₂ ∧ digits l₁ = digits l₂ := by
        cases b₁ <;> cases b₂ <;> simp at hd ⊢ <;> omega
      rw [hb.1, digits_inj l₁ l₂ hl' hb.2]

theorem ofNat_inj_of_lt {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h : UInt8.ofNat a = UInt8.ofNat b) : a = b := by
  have := congrArg UInt8.toNat h
  rwa [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The bitmap determines membership: bit `b % 8` of byte `b / 8`. -/
theorem maskBytes_inj_contains (m₁ m₂ : ByteMask) (h : maskBytes m₁ = maskBytes m₂) (b : UInt8) :
    m₁.contains b = m₂.contains b := by
  have hb : b.toNat < 256 := by have := UInt8.toNat_lt b; omega
  unfold maskBytes at h
  have hbyte := List.map_inj_left.mp h (b.toNat / 8) (List.mem_range.mpr (by omega))
  have hlen : ∀ (f : Nat → Bool), ((List.range 8).map f).length = 8 := fun f => by simp
  have hlt : ∀ (f : Nat → Bool), digits ((List.range 8).map f) < 256 := fun f => by
    have := digits_lt ((List.range 8).map f)
    rw [hlen] at this
    omega
  have hd := ofNat_inj_of_lt (hlt _) (hlt _) hbyte
  have hl := digits_inj _ _ (by rw [hlen, hlen]) hd
  have hj := List.map_inj_left.mp hl (b.toNat % 8) (List.mem_range.mpr (by omega))
  rw [Nat.div_add_mod, UInt8.ofNat_toNat] at hj
  exact hj

theorem mem_ofList (bs : List UInt8) (b : UInt8) : b ∈ ByteMask.ofList bs ↔ b ∈ bs := by
  simp only [ByteMask.ofList, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    split at hi
    · rename_i hc
      cases hi
      exact List.contains_iff_mem.mp hc
    · cases hi
  · intro hb
    refine ⟨b.toNat, by have := UInt8.toNat_lt b; omega, ?_⟩
    rw [UInt8.ofNat_toNat, if_pos (List.contains_iff_mem.mpr hb)]

theorem contains_ofList (bs : List UInt8) (b : UInt8) :
    (ByteMask.ofList bs).contains b = bs.contains b := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact mem_ofList bs b

theorem ofList_congr (bs₁ bs₂ : List UInt8) (h : ∀ b, bs₁.contains b = bs₂.contains b) :
    ByteMask.ofList bs₁ = ByteMask.ofList bs₂ := by
  simp only [ByteMask.ofList, h]

/-- Canonical masks (every `childMask`) with the same members are equal. -/
theorem childMask_eq_of_contains {V : Type} (t₁ t₂ : PathMap V) (p₁ p₂ : Path)
    (h : ∀ b, (t₁.childMask p₁).contains b = (t₂.childMask p₂).contains b) :
    t₁.childMask p₁ = t₂.childMask p₂ := by
  unfold PathMap.childMask at h ⊢
  exact ofList_congr _ _ fun b => by
    have := h b
    rwa [contains_ofList, contains_ofList] at this

theorem flatten_fixed_inj {α : Type} (w : Nat) :
    ∀ (l₁ l₂ : List (List α)), (∀ x ∈ l₁, x.length = w) → (∀ x ∈ l₂, x.length = w) →
      l₁.length = l₂.length → l₁.flatten = l₂.flatten → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | x :: l₁, y :: l₂, h₁, h₂, hl, hf => by
      simp only [List.flatten_cons] at hf
      have hx : x.length = w := h₁ x (by simp)
      have hy : y.length = w := h₂ y (by simp)
      obtain ⟨rfl, hrest⟩ := List.append_inj hf (hx.trans hy.symm)
      rw [flatten_fixed_inj w l₁ l₂ (fun z hz => h₁ z (by simp [hz])) (fun z hz => h₂ z (by simp [hz]))
        (by simpa using hl) hrest]

theorem nodeMsg_inj {m₁ m₂ : ByteMask} {c₁ c₂ : List UInt64} (h : nodeMsg m₁ c₁ = nodeMsg m₂ c₂) :
    maskBytes m₁ = maskBytes m₂ ∧ (c₁.map leBytes64).flatten = (c₂.map leBytes64).flatten := by
  simp only [nodeMsg, List.cons.injEq, true_and] at h
  exact List.append_inj h (by simp [length_maskBytes])

theorem children_inj {c₁ c₂ : List UInt64} (hlen : c₁.length = c₂.length)
    (h : (c₁.map leBytes64).flatten = (c₂.map leBytes64).flatten) : c₁ = c₂ := by
  have := flatten_fixed_inj 8 _ _ (by simp [length_leBytes64]) (by simp [length_leBytes64])
    (by simpa using hlen) h
  exact (List.map_inj_right fun _ _ hxy => leBytes64_inj hxy).mp this

/-- A node message and a value message never coincide, and neither is empty. -/
theorem nodeMsg_ne_valMsg (m : ByteMask) (c : List UInt64) (vh below : UInt64) :
    nodeMsg m c ≠ valMsg vh below := by
  intro h
  have := (List.cons.inj h).1
  exact absurd this (by decide)

theorem nodeMsg_ne_nil (m : ByteMask) (c : List UInt64) : nodeMsg m c ≠ [] := by
  simp [nodeMsg]

theorem valMsg_ne_nil (vh below : UInt64) : valMsg vh below ≠ [] := by
  simp [valMsg]

/-! ## Facts about the trie model -/

/-- Every trie the crate can build is prefix-closed; the model's constructors maintain it
(`PathMap.mk'`), and it is what puts "nothing below an absent path" on solid ground. -/
def PrefixClosed {V : Type} (t : PathMap V) : Prop :=
  ∀ (p : Path) (b : UInt8), t.pathExists (p ++ [b]) = true → t.pathExists p = true

theorem entry_ext' {V : Type} {e₁ e₂ : PathMap.Entry V} (hp : e₁.present = e₂.present)
    (hv : e₁.val = e₂.val) : e₁ = e₂ := by
  cases e₁ <;> cases e₂ <;> simp_all [PathMap.Entry.present, PathMap.Entry.val]

theorem entryAt_eq_absent_iff {V : Type} (t : PathMap V) (p : Path) :
    t.entryAt p = .absent ↔ t.pathExists p = false := by
  unfold PathMap.pathExists
  cases t.entryAt p <;> simp [PathMap.Entry.present]

theorem valAt_eq_none_of_absent {V : Type} {t : PathMap V} {p : Path}
    (h : t.pathExists p = false) : t.valAt p = none := by
  unfold PathMap.valAt
  rw [(entryAt_eq_absent_iff t p).mpr h]
  rfl

theorem lookup_isSome_iff {α β : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : List (α × β)), (l.lookup a).isSome = true ↔ a ∈ l.map (·.1)
  | [] => by simp
  | (k, v) :: l => by
      simp only [List.lookup_cons, List.map_cons, List.mem_cons]
      by_cases h : a = k
      · subst h; simp
      · have hk : (a == k) = false := beq_eq_false_iff_ne.mpr h
        simp [hk, h, lookup_isSome_iff a l]

theorem mem_paths_iff_present {V : Type} (t : PathMap V) (q : Path) :
    q ∈ t.paths ↔ t.pathExists q = true := by
  rw [PathMap.paths, ← lookup_isSome_iff]
  unfold PathMap.pathExists PathMap.entryAt
  cases t.entries.lookup q with
  | none => simp [PathMap.Entry.present]
  | some o => cases o <;> simp [PathMap.Entry.present]

theorem stripPrefix_eq_some : ∀ (p q r : Path), Path.stripPrefix p q = some r ↔ q = p ++ r
  | [], q, r => by simp [Path.stripPrefix]
  | _ :: _, [], r => by simp [Path.stripPrefix]
  | a :: p, c :: q, r => by
      simp only [Path.stripPrefix, List.cons_append, List.cons.injEq]
      by_cases hac : a = c
      · subst hac; simp [stripPrefix_eq_some p q r]
      · have : (a == c) = false := beq_eq_false_iff_ne.mpr hac
        simp [this, Ne.symm hac]

theorem mem_childMask_iff {V : Type} (t : PathMap V) (p : Path) (b : UInt8) :
    b ∈ t.childMask p ↔ t.pathExists (p ++ [b]) = true := by
  rw [← mem_paths_iff_present]
  unfold PathMap.childMask
  rw [← List.contains_iff_mem, contains_ofList, List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hb⟩
    split at hb
    · rename_i r hr
      cases hb
      rw [(stripPrefix_eq_some _ _ _).mp hr] at hq
      exact hq
    · cases hb
  · intro h
    refine ⟨p ++ [b], h, ?_⟩
    rw [show Path.stripPrefix p (p ++ [b]) = some [b] from (stripPrefix_eq_some _ _ _).mpr rfl]

theorem not_present_below {V : Type} {t : PathMap V} (pc : PrefixClosed t) {p : Path}
    (hp : t.pathExists p = false) : ∀ q, t.pathExists (p ++ q) = false := by
  intro q
  induction q generalizing p with
  | nil => simpa using hp
  | cons b q ih =>
      have hb : t.pathExists (p ++ [b]) = false := by
        cases h : t.pathExists (p ++ [b]) with
        | true => rw [pc p b h] at hp; cases hp
        | false => rfl
      rw [List.append_cons]
      exact ih hb

theorem le_foldl_max (l : List Path) (a : Nat) :
    a ≤ l.foldl (fun acc p => max acc p.length) a ∧
      ∀ q ∈ l, q.length ≤ l.foldl (fun acc p => max acc p.length) a := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldl_cons, List.mem_cons]
      obtain ⟨h1, h2⟩ := ih (max a p.length)
      refine ⟨by omega, ?_⟩
      rintro q (rfl | hq)
      · omega
      · exact h2 q hq

theorem absent_of_deep {V : Type} {t : PathMap V} {q : Path} (h : depth t < q.length) :
    t.pathExists q = false := by
  cases hq : t.pathExists q with
  | false => rfl
  | true =>
      have := (le_foldl_max t.paths 0).2 q ((mem_paths_iff_present t q).mpr hq)
      unfold depth at h
      omega

/-! ## The theorems -/

/-- The two subtries are observationally the same: the same value at the position, and the
same `Entry` at every path strictly below.  (Whether the position itself exists is its
parent's business, so it is not part of the hash; see the module docs.) -/
def LogicalEq {V : Type} (t₁ : PathMap V) (p₁ : Path) (t₂ : PathMap V) (p₂ : Path) : Prop :=
  t₁.valAt p₁ = t₂.valAt p₂ ∧ ∀ q, q ≠ [] → t₁.entryAt (p₁ ++ q) = t₂.entryAt (p₂ ++ q)

theorem logicalEq_of_deep {V : Type} {t₁ t₂ : PathMap V} {p₁ p₂ : Path}
    (h₁ : depth t₁ < p₁.length) (h₂ : depth t₂ < p₂.length) : LogicalEq t₁ p₁ t₂ p₂ := by
  refine ⟨?_, fun q _ => ?_⟩
  · rw [valAt_eq_none_of_absent (absent_of_deep h₁), valAt_eq_none_of_absent (absent_of_deep h₂)]
  · rw [(entryAt_eq_absent_iff _ _).mpr (absent_of_deep (by simp; omega)),
      (entryAt_eq_absent_iff _ _).mpr (absent_of_deep (by simp; omega))]

/-- Peeling the value layer: with `H` injective, the two positions agree on having a value,
on the value, and on the hash below. -/
theorem top_inj {V : Type} {H : List UInt8 → UInt64} (hH : Injective H) {vh : V → UInt64}
    (hvh : Injective vh) {o₁ o₂ : Option V} {m₁ m₂ : ByteMask} {c₁ c₂ : List UInt64}
    (h : (match o₁ with | some v => H (valMsg (vh v) (H (nodeMsg m₁ c₁))) | none => H (nodeMsg m₁ c₁)) =
         (match o₂ with | some v => H (valMsg (vh v) (H (nodeMsg m₂ c₂))) | none => H (nodeMsg m₂ c₂))) :
    o₁ = o₂ ∧ H (nodeMsg m₁ c₁) = H (nodeMsg m₂ c₂) := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none => exact ⟨rfl, h⟩
      | some v₂ => exact absurd (hH h) (nodeMsg_ne_valMsg _ _ _ _)
  | some v₁ =>
      cases o₂ with
      | none => exact absurd (hH h).symm (nodeMsg_ne_valMsg _ _ _ _)
      | some v₂ =>
          have hm := hH h
          simp only [valMsg, List.cons.injEq, true_and] at hm
          obtain ⟨hbelow, hval⟩ := List.append_inj hm (by simp [length_leBytes64])
          exact ⟨by rw [hvh (leBytes64_inj hval)], leBytes64_inj hbelow⟩

/-- Peeling the node layer: equal hashes below two positions, and the children's hashes
already known to determine their subtries, give equal subtries strictly below. -/
theorem below_inj {V : Type} {H : List UInt8 → UInt64} (hH : Injective H) (vh : V → UInt64)
    {t₁ t₂ : PathMap V} (pc₁ : PrefixClosed t₁) (pc₂ : PrefixClosed t₂) {f₁ f₂ : Nat} {p₁ p₂ : Path}
    (ih : ∀ b, hashWith H vh t₁ f₁ (p₁ ++ [b]) = hashWith H vh t₂ f₂ (p₂ ++ [b]) →
      LogicalEq t₁ (p₁ ++ [b]) t₂ (p₂ ++ [b]))
    (h : belowOf H vh t₁ f₁ p₁ = belowOf H vh t₂ f₂ p₂) :
    ∀ q, q ≠ [] → t₁.entryAt (p₁ ++ q) = t₂.entryAt (p₂ ++ q) := by
  obtain ⟨hmask, hflat⟩ := nodeMsg_inj (hH h)
  have hm : t₁.childMask p₁ = t₂.childMask p₂ :=
    childMask_eq_of_contains t₁ t₂ p₁ p₂ (maskBytes_inj_contains _ _ hmask)
  have hkids : ∀ b ∈ t₁.childMask p₁,
      hashWith H vh t₁ f₁ (p₁ ++ [b]) = hashWith H vh t₂ f₂ (p₂ ++ [b]) := by
    have hc := children_inj (by simp [hm]) hflat
    rw [← hm] at hc
    exact List.map_inj_left.mp hc
  intro q hq
  cases q with
  | nil => exact absurd rfl hq
  | cons b q' =>
      rw [List.append_cons p₁ b q', List.append_cons p₂ b q']
      by_cases hb : b ∈ t₁.childMask p₁
      · have hle := ih b (hkids b hb)
        cases q' with
        | nil =>
            simp only [List.append_nil]
            apply entry_ext'
            · have e₁ := (mem_childMask_iff t₁ p₁ b).mp hb
              have e₂ := (mem_childMask_iff t₂ p₂ b).mp (hm ▸ hb)
              exact e₁.trans e₂.symm
            · exact hle.1
        | cons c q'' => exact hle.2 (c :: q'') (by simp)
      · have a₁ : t₁.pathExists (p₁ ++ [b]) = false := by
          cases h₁ : t₁.pathExists (p₁ ++ [b]) with
          | false => rfl
          | true => exact absurd ((mem_childMask_iff t₁ p₁ b).mpr h₁) hb
        have a₂ : t₂.pathExists (p₂ ++ [b]) = false := by
          cases h₂ : t₂.pathExists (p₂ ++ [b]) with
          | false => rfl
          | true => exact absurd (hm ▸ (mem_childMask_iff t₂ p₂ b).mpr h₂) hb
        rw [(entryAt_eq_absent_iff _ _).mpr (not_present_below pc₁ a₁ q'),
          (entryAt_eq_absent_iff _ _).mpr (not_present_below pc₂ a₂ q')]

/-- **Soundness for an ideal primitive.**  With `H` and the value hash injective, equal
hashes at two positions (each computed with adequate fuel) mean the subtries are the same. -/
theorem hashWith_inj_imp_logicalEq {V : Type} (H : List UInt8 → UInt64) (hH : Injective H)
    (vh : V → UInt64) (hvh : Injective vh) (t₁ t₂ : PathMap V)
    (pc₁ : PrefixClosed t₁) (pc₂ : PrefixClosed t₂) :
    ∀ (f₁ f₂ : Nat) (p₁ p₂ : Path), depth t₁ < p₁.length + f₁ → depth t₂ < p₂.length + f₂ →
      hashWith H vh t₁ f₁ p₁ = hashWith H vh t₂ f₂ p₂ → LogicalEq t₁ p₁ t₂ p₂
  | 0, 0, p₁, p₂, d₁, d₂, _ => logicalEq_of_deep (by omega) (by omega)
  | 0, f₂ + 1, p₁, p₂, _, _, h => by
      exfalso
      rw [hashWith_succ] at h
      split at h
      · exact valMsg_ne_nil _ _ (hH h).symm
      · exact nodeMsg_ne_nil _ _ (hH h).symm
  | f₁ + 1, 0, p₁, p₂, _, _, h => by
      exfalso
      rw [hashWith_succ] at h
      split at h
      · exact valMsg_ne_nil _ _ (hH h)
      · exact nodeMsg_ne_nil _ _ (hH h)
  | f₁ + 1, f₂ + 1, p₁, p₂, d₁, d₂, h => by
      rw [hashWith_succ, hashWith_succ] at h
      obtain ⟨hval, hbelow⟩ := top_inj hH hvh h
      have ih : ∀ b, hashWith H vh t₁ f₁ (p₁ ++ [b]) = hashWith H vh t₂ f₂ (p₂ ++ [b]) →
          LogicalEq t₁ (p₁ ++ [b]) t₂ (p₂ ++ [b]) := fun b hb =>
        hashWith_inj_imp_logicalEq H hH vh hvh t₁ t₂ pc₁ pc₂ f₁ f₂ (p₁ ++ [b]) (p₂ ++ [b])
          (by rw [List.length_append, List.length_singleton]; omega)
          (by rw [List.length_append, List.length_singleton]; omega) hb
      exact ⟨hval, below_inj hH vh pc₁ pc₂ ih hbelow⟩

/-- **The collision reduction.**  No assumption on the primitive: if two subtries that are
not the same hash alike, then either `H` or the value hash has a collision, and the
colliding messages exist. -/
theorem collision_of_hash_eq {V : Type} (H : List UInt8 → UInt64) (vh : V → UInt64)
    (t₁ t₂ : PathMap V) (pc₁ : PrefixClosed t₁) (pc₂ : PrefixClosed t₂)
    (f₁ f₂ : Nat) (p₁ p₂ : Path) (d₁ : depth t₁ < p₁.length + f₁) (d₂ : depth t₂ < p₂.length + f₂)
    (h : hashWith H vh t₁ f₁ p₁ = hashWith H vh t₂ f₂ p₂) (hne : ¬ LogicalEq t₁ p₁ t₂ p₂) :
    (∃ a b, a ≠ b ∧ H a = H b) ∨ (∃ x y, x ≠ y ∧ vh x = vh y) := by
  refine Classical.byContradiction fun hno => hne ?_
  refine hashWith_inj_imp_logicalEq H ?_ vh ?_ t₁ t₂ pc₁ pc₂ f₁ f₂ p₁ p₂ d₁ d₂ h
  · intro a b hab
    exact Classical.byContradiction fun hne' => hno (Or.inl ⟨a, b, hne', hab⟩)
  · intro x y hxy
    exact Classical.byContradiction fun hne' => hno (Or.inr ⟨x, y, hne', hxy⟩)

/-! ## The harness's instance -/

/-- `hashU64` is `hashWith fnv` over `fnv ∘ leBytes64`, with adequate fuel. -/
theorem hashU64_eq (t : PathMap UInt64) (p : Path) :
    hashU64 t p = hashWith fnv value t (depth t + 1) p :=
  hashFuel_eq_hashWith value t (depth t + 1) p

/-- For the harness's `PathMap<u64>` maps: two maps whose root hashes agree but which differ
at some path exhibit an `fnv` collision.  (A value-hash collision is one too, since values
are hashed as `fnv` of their eight bytes and the bytes determine the value.) -/
theorem fnv_collision_of_hashU64_eq (t₁ t₂ : PathMap UInt64)
    (pc₁ : PrefixClosed t₁) (pc₂ : PrefixClosed t₂)
    (r₁ : t₁.pathExists [] = true) (r₂ : t₂.pathExists [] = true)
    (h : hashU64 t₁ [] = hashU64 t₂ []) (hne : ∃ q, t₁.entryAt q ≠ t₂.entryAt q) :
    ∃ a b, a ≠ b ∧ fnv a = fnv b := by
  rw [hashU64_eq, hashU64_eq] at h
  have hne' : ¬ LogicalEq t₁ [] t₂ [] := by
    rintro ⟨hv, hq⟩
    obtain ⟨q, hq'⟩ := hne
    apply hq'
    cases q with
    | nil =>
        apply entry_ext'
        · exact r₁.trans r₂.symm
        · exact hv
    | cons b q => simpa using hq (b :: q) (by simp)
  rcases collision_of_hash_eq fnv value t₁ t₂ pc₁ pc₂ _ _ [] [] (by simp) (by simp) h hne' with
    ⟨a, b, hab, he⟩ | ⟨x, y, hxy, he⟩
  · exact ⟨a, b, hab, he⟩
  · exact ⟨leBytes64 x, leBytes64 y, fun e => hxy (leBytes64_inj e), he⟩

end Hash
end PathMapModel
