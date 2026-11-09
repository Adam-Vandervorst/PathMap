import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 30–59: `ring.rs`

What `pathmap::ring` means, and the exact `AlgebraicResult` every impl must
return.  The Rust side is `differential/src/utilfuzz/lattice.rs`.

## `AlgebraicResult` and the identity mask

An operation on `n` arguments answers `None` (the arguments annihilate: the
result is the bottom / absent value), `Element(v)` (a new value), or
`Identity(mask)`: the result *is* argument `i` for every set bit `i`
(`SELF_IDENT` = bit 0, `COUNTER_IDENT` = bit 1).  The crate's doc
(`ring.rs` NOTE and NOTE 2) leaves two freedoms, and both are used:

* a mask bit asserts equality, but a clear bit asserts nothing: an
  implementation may name fewer arguments than are equal to the result;
* when the result is the bottom, both `None` and `Identity` are correct
  (`None` "should take precedence").

So a value type's lattice ops are given here as (1) a *meaning* — which value
the result is — and (2) the impl's *choice* within those freedoms, stated per
type.  Section "Laws" (end of file) checks (1) against the lattice
laws (and lists the ones that deliberately fail), and checks every mask the
model produces is truthful.

## Value types

`ltys` (the `Lattice` table) and `dtys` (the `DistributiveLattice` ones);
the same order as `lty!` / `dty!` in the Rust file.

| type | meaning | join / meet / subtract |
|---|---|---|
| `()` | the single present value | `Identity(3)`, `Identity(3)`, `None` |
| `bool` | the two-element Boolean algebra | `∨`, `∧`, equal values cancel; one identity bit, `SELF` preferred |
| `u8`…`usize` | an opaque token (documented "GOAT trash": not a lattice) | left projection, left projection, equal values cancel |
| `Option<V>` | `V` with a new bottom, *absent* | absent is the join identity and the meet annihilator |
| `Box<V>` | `V` | `V`'s |
| `HashSet<K>` | a finite set | `∪`, `∩`, `\`; identity bits maximal |
| `HashMap<K, V>` | a finite map into `V` | pointwise; a bit only when every key reports it |

## Op lines

`<i> <op> ret=<answer>`; every value op renders the type name and both
operands before the answer.  Ops (selector − 30, see `latticeOps`):

| op | calls | answer |
|---|---|---|
| `ring_pjoin` / `ring_pmeet` / `ring_psubtract` | `Lattice::pjoin`, `pmeet`, `DistributiveLattice::psubtract` | the result |
| `ring_join_into` | `Lattice::join_into` (Option's override, the default elsewhere) | status, then `self` |
| `ring_join_all` | `Lattice::join_all` over 0–4 `Box`ed arguments | the result |
| `ring_lref` / `ring_dref` | `LatticeRef` / `DistributiveLatticeRef` on `&V` and `Option<&V>` | the result |
| `ring_ar_*` | `AlgebraicResult<u64>` methods | see each op |
| `ring_ar_merge` / `ring_merge_fields` | `AlgebraicResult::merge`, raw / composing a pair's result | |
| `ring_status` | `AlgebraicStatus` methods, `Ord`, `merge` | |
| `ring_setlattice_*` | the `SetLattice` methods of `HashSet<u8>` / `HashMap<u8,u64>` | a log |
| `ring_consts` | `SELF_IDENT`, `COUNTER_IDENT`, `IDEMPOTENT`s, `Default`s | |

`ring_pmeet` reads a `full` byte first; unless it is 255, a map meet that the
`SetLattice` operand swap could change renders `skip:setlattice-meet-swap`
(`Ty.hazard`); with 255 the op is `ring_pmeet!` and has no skip (the bug, L1
in `lean/findings/u-lattice.md`).
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

/-! ## `AlgebraicResult` with a full mask -/

/-! The shared `AlgResult` (`UtilFuzz/Base.lean`) carries the whole mask as a
number, so `Identity(4)` (an n-ary result) or the invalid `Identity(0)` are
expressible. -/

def SELF : Nat := 1
def COUNTER : Nat := 2

/-- `u64::trailing_zeros`: the index of the lowest set bit, 64 for 0.  The
index of the argument an `Identity(mask)` is resolved to. -/
def tz (m : Nat) : Nat :=
  ((List.range 64).find? (fun i => (m >>> i) % 2 == 1)).getD 64

def AlgResult.map {V U : Type} (f : V → U) : AlgResult V → AlgResult U
  | .none => .none
  | .identity m => .identity m
  | .element v => .element (f v)

def AlgResult.hasBit {V : Type} (r : AlgResult V) (b : Nat) : Bool :=
  match r with
  | .identity m => m &&& b != 0
  | _ => false

def AlgResult.isIdentity {V : Type} : AlgResult V → Bool
  | .identity _ => true
  | _ => false

def AlgResult.beqWith {V : Type} (eq : V → V → Bool) : AlgResult V → AlgResult V → Bool
  | .none, .none => true
  | .identity m, .identity n => m == n
  | .element v, .element w => eq v w
  | _, _ => false

/-- The value an arity-2 result denotes: absent for `None`, else the argument
the lowest mask bit names (what `unwrap_or([a, b], ..)` gives).  For a mask
naming neither argument (never produced by a valid impl) nothing. -/
def AlgResult.resolve {V : Type} (r : AlgResult V) (a b : V) : Option V :=
  match r with
  | .none => Option.none
  | .element v => some v
  | .identity m => if m &&& SELF != 0 then some a else if m &&& COUNTER != 0 then some b else Option.none

/-! ## `AlgebraicStatus` -/

/-- `AlgebraicStatus`, in its documented order: `Element < Identity < None`
("higher values make stronger guarantees"). -/
inductive Status where
  | element
  | identity
  | none
  deriving BEq, Inhabited

def Status.show : Status → String
  | .element => "Element"
  | .identity => "Identity"
  | .none => "None"

def Status.rank : Status → Nat
  | .element => 0
  | .identity => 1
  | .none => 2

/-- `AlgebraicResult::status`: an identity is `Identity` only if it names
`self`; an identity of the other argument means `self` must change. -/
def AlgResult.status {V : Type} : AlgResult V → Status
  | .none => .none
  | .element _ => .element
  | .identity m => if m &&& SELF != 0 then .identity else .element

/-- `AlgebraicResult::from_status`: the in-place answer seen as a result on
`self` (`Identity` names `self`). -/
def AlgResult.fromStatus {V : Type} (s : Status) (v : V) : AlgResult V :=
  match s with
  | .none => .none
  | .identity => .identity SELF
  | .element => .element v

/-- `AlgebraicResult::invert_identity`: the same result for the operation
with its two arguments swapped, so bit 0 and bit 1 trade places; bits above
an arity-2 operation's are dropped (doc: "Removes identity mask bits higher
than 2", so `Identity(4)` becomes the invalid `Identity(0)`). -/
def AlgResult.invert {V : Type} : AlgResult V → AlgResult V
  | .identity m => .identity (((m &&& SELF) <<< 1) ||| ((m &&& COUNTER) >>> 1))
  | r => r

/-- `AlgebraicResult<Option<V>>::flatten`: `Element(None)` is annihilation. -/
def AlgResult.flatten {V : Type} : AlgResult (Option V) → AlgResult V
  | .element (some v) => .element v
  | .element Option.none => .none
  | .none => .none
  | .identity m => .identity m

/-- `AlgebraicStatus::merge`: the status of an in-place op on a pair, from
the statuses on its two fields.  `an` / `bn`: that field was already absent
before the op.  The whole is annihilated only if both fields are; changed if
either field changed, or a field was *made* absent; otherwise unchanged. -/
def Status.merge (a b : Status) (an bn : Bool) : Status :=
  if a == .none && b == .none then .none
  else if a == .element || b == .element then .element
  else if (a == .none && !an) || (b == .none && !bn) then .element
  else .identity

/-- The default `Lattice::join_into` (`in_place_default_impl`): an in-place
join is its `pjoin` applied to `self`.  `None` leaves `self` alone (a join
reaches the bottom only from the bottom, per the code comment); an identity
of `self` changes nothing; anything else replaces `self`. -/
def defaultJoinInto {V : Type} (join : V → V → AlgResult V) (a b : V) : Status × V :=
  match join a b with
  | .none => (.none, a)
  | .element v => (.element, v)
  | .identity m => if m &&& SELF != 0 then (.identity, a) else (.element, b)

/-! ## Value types -/

/-- A value type of the fuzzer's table: decoder, rendering, its lattice ops
and their documented choices, and two facts for laws / skips. -/
structure Ty where
  name : String
  V : Type
  dec : Dec → Option (V × Dec)
  render : V → String
  /-- Representational equality: what an identity bit asserts. -/
  beq : V → V → Bool
  /-- The canonical form, `none` for the bottom.  The laws compare meanings,
  and `SetLattice`'s doc lets an empty set stand for an absent one. -/
  norm : V → Option V
  join : V → V → AlgResult V
  meet : V → V → AlgResult V
  /-- `psubtract`, for the `DistributiveLattice` types (`dtys`). -/
  sub : V → V → AlgResult V
  joinInto : V → V → Status × V
  /-- `meet b a` is always `(meet a b).invert`. -/
  meetSym : Bool
  /-- `set_lattice!`'s meet swaps its operands somewhere in this meet (L1). -/
  hazard : V → V → Bool

/-- `()`: the single present value.  Both operands are the answer to a join
or a meet, so both bits; a subtraction removes it. -/
def unitTy : Ty where
  name := "unit"
  V := Unit
  dec d := some ((), d)
  render _ := "()"
  beq _ _ := true
  norm _ := some ()
  join _ _ := .identity 3
  meet _ _ := .identity 3
  sub _ _ := .none
  joinInto := defaultJoinInto (fun _ _ => .identity 3)
  meetSym := true
  hazard _ _ := false

instance : Inhabited Ty := ⟨unitTy⟩

/-- `bool ∨` / `∧` as the impl reports them: the answer is always one of the
operands (a chain), and exactly one bit is set: `SELF` whenever `self` is the
answer, else `COUNTER` — never both, even for equal operands (allowed: a
clear bit asserts nothing). -/
def boolJoin (a b : Bool) : AlgResult Bool := .identity (if (a || b) == a then SELF else COUNTER)
def boolMeet (a b : Bool) : AlgResult Bool := .identity (if (a && b) == a then SELF else COUNTER)

/-- `bool`: the Boolean algebra `{false < true}`, join `∨`, meet `∧`
(`boolJoin`, `boolMeet`).  It never answers `None`: `false` is an element
here, not an absence.

`psubtract` is the cancellation rule the crate shares with the integers
(`integer_subtract_is_self_identity` tests them together): equal operands
cancel (`None`), otherwise `self` is untouched.  In Boolean-algebra terms
that is `a ∧ ¬b` with `false` as the bottom: `T − F = T`, `F − T = F` (an
identity of a bottom, which NOTE allows), `x − x = ⊥` (`None`). -/
def boolTy : Ty where
  name := "bool"
  V := Bool
  dec d := d.u8.map fun (b, d) => (b.toNat % 2 == 1, d)
  render b := if b then "true" else "false"
  beq a b := a == b
  norm b := if b then some true else none
  join := boolJoin
  meet := boolMeet
  sub a b := if a == b then .none else .identity SELF
  joinInto := defaultJoinInto boolJoin
  meetSym := false
  hazard _ _ := false

/-- An integer operand byte: small (`b % 4`, so operands collide) below 224,
else a spread value.  `int_byte` in the Rust file. -/
def intOfByte (b : UInt8) : UInt64 :=
  if b < 224 then (b % 4).toUInt64 else b.toUInt64 * 0x9E3779B97F4A7C15

/-- Truncation to a `w`-bit integer (`as u8`, ...). -/
def truncW (w : Nat) (v : UInt64) : UInt64 :=
  if w ≥ 64 then v else v &&& ((1 <<< w.toUInt64) - 1)

/-- `left_biased_pjoin`: the join of two tokens is `self`; equal tokens are
also `other`'s identity. -/
def leftJoin (a b : UInt64) : AlgResult UInt64 := .identity (if a == b then 3 else SELF)

/-- `u8`, `u16`, `u32`, `u64`, `usize`: opaque tokens.  The crate marks these
impls "GOAT trash" and documents the choice at `left_biased_pjoin`: join and
meet are both the *left projection* (`self` wins), which is associative,
idempotent and absorptive but not commutative, so not a lattice (the laws
battery lists exactly which laws fail).  Join reports both bits for equal
operands; meet reports `SELF` only, even then.  `psubtract` (only `u16` and
`u64` have it) cancels equal tokens and otherwise leaves `self` alone. -/
def intTy (name : String) (w : Nat) : Ty where
  name := name
  V := UInt64
  dec d := d.u8.map fun (b, d) => (truncW w (intOfByte b), d)
  render v := toString v
  beq a b := a == b
  norm v := some v
  join := leftJoin
  meet _ _ := .identity SELF
  sub a b := if a == b then .none else .identity SELF
  joinInto := defaultJoinInto leftJoin
  meetSym := false
  hazard _ _ := false

/-- `Option<V>`: `V` with a new bottom, *absent*.  Absent is the identity of
join (the present operand is the answer, named by its bit; two absents are
`None`) and annihilates meet; subtracting from absent is absent, subtracting
absent changes nothing.  Two present values combine as in `V`.

`join_into` is overridden: the same lifting done in place (absent ← present
is `Element`, present ← absent `Identity`, two presents `V::join_into`). -/
def optTy (t : Ty) : Ty where
  name := s!"opt<{t.name}>"
  V := Option t.V
  dec d := do
    let (b, d) ← d.u8
    if b.toNat % 4 == 0 then some (none, d)
    else
      let (v, d) ← t.dec d
      some (some v, d)
  render
    | none => "None"
    | some v => s!"Some({t.render v})"
  beq
    | none, none => true
    | some a, some b => t.beq a b
    | _, _ => false
  norm o := (o.bind t.norm).map some
  join
    | none, none => .none
    | none, some _ => .identity COUNTER
    | some _, none => .identity SELF
    | some a, some b => (t.join a b).map some
  meet
    | some a, some b => (t.meet a b).map some
    | _, _ => .none
  sub
    | none, _ => .none
    | some _, none => .identity SELF
    | some a, some b => (t.sub a b).map some
  joinInto
    | none, none => (.none, none)
    | none, some b => (.element, some b)
    | some a, none => (.identity, some a)
    | some a, some b => let (s, v) := t.joinInto a b; (s, some v)
  meetSym := t.meetSym
  hazard
    | some a, some b => t.hazard a b
    | _, _ => false

/-- `Box<V>`: `V`, rendered the same. -/
def boxTy (t : Ty) : Ty := { t with name := s!"box<{t.name}>" }

/-! ### Finite sets and maps (`SetLattice`) -/

def setInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k < x then k :: x :: xs else if k == x then x :: xs else x :: setInsert k xs

def showNatSet (s : List Nat) : String := "{" ++ ",".intercalate (s.map toString) ++ "}"

/-- The answer `r` reported with *every* operand equal to it named
(`set_lattice!`'s flags on a set do: they track exactly "no member added or
removed relative to this operand").  `counter` false for subtraction, which
may only name `self`. -/
def maximalRes {V : Type} (eq : V → V → Bool) (r a b : V) (empty counter : Bool) : AlgResult V :=
  if empty then .none
  else
    let m := (if eq r a then SELF else 0) ||| (if counter && eq r b then COUNTER else 0)
    if m == 0 then .element r else .identity m

def setJoin (a b : List Nat) : AlgResult (List Nat) :=
  let r := b.foldl (fun s k => setInsert k s) a
  maximalRes (· == ·) r a b r.isEmpty true

/-- `HashSet<u8>`: a finite set.  Join `∪`, meet `∩`, subtract `\`; an empty
answer is `None`; otherwise the mask names every operand equal to the answer,
and a new set is `Element`.  Operands: `n := u8 % 6` members, each `u8 % 8`. -/
def setTy : Ty where
  name := "set"
  V := List Nat
  dec d := do
    let (n, d) ← d.mod 6
    let rec go : Nat → List Nat → Dec → Option (List Nat × Dec)
      | 0, s, d => some (s, d)
      | k + 1, s, d => do
          let (b, d) ← d.u8
          go k (setInsert (b.toNat % 8) s) d
    go n [] d
  render := showNatSet
  beq a b := a == b
  norm s := if s.isEmpty then none else some s
  join := setJoin
  meet a b :=
    let r := a.filter (b.contains ·)
    maximalRes (· == ·) r a b r.isEmpty true
  sub a b :=
    let r := a.filter (!b.contains ·)
    maximalRes (· == ·) r a b r.isEmpty false
  joinInto := defaultJoinInto setJoin
  meetSym := true
  hazard _ _ := false

def mapInsert {V : Type} (k : Nat) (v : V) : List (Nat × V) → List (Nat × V)
  | [] => [(k, v)]
  | (x, w) :: xs =>
      if k < x then (k, v) :: (x, w) :: xs
      else if k == x then (k, v) :: xs
      else (x, w) :: mapInsert k v xs

def mapLookup {V : Type} (k : Nat) : List (Nat × V) → Option V
  | [] => none
  | (x, w) :: xs => if k == x then some w else mapLookup k xs

def mapKeys {V : Type} (m : List (Nat × V)) : List Nat := m.map (·.1)

/-- `HashMap<u8, V>`'s join: a key in one operand keeps its value, a key in
both gets the value join (dropped if that annihilates).  `SELF` iff `other`
has no key `self` lacks and *every* shared key's value join names `self`
(a key-wise identity); `COUNTER` symmetrically.  `None` when nothing is
left; otherwise a new map. -/
def mapJoin (t : Ty) (a b : List (Nat × t.V)) : AlgResult (List (Nat × t.V)) :=
  let keys := (mapKeys b).foldl (fun s k => setInsert k s) (mapKeys a)
  let r := keys.filterMap fun k =>
    match mapLookup k a, mapLookup k b with
    | some x, none => some (k, x)
    | none, some y => some (k, y)
    | some x, some y => ((t.join x y).resolve x y).map (k, ·)
    | none, none => none
  let selfBit := b.all fun (k, y) => match mapLookup k a with
    | some x => (t.join x y).hasBit SELF
    | none => false
  let ctrBit := a.all fun (k, x) => match mapLookup k b with
    | some y => (t.join x y).hasBit COUNTER
    | none => false
  if r.isEmpty then .none
  else
    let m := (if selfBit then SELF else 0) ||| (if ctrBit then COUNTER else 0)
    if m == 0 then .element r else .identity m

/-- `HashMap<u8, V>`'s meet, **as specified**: the keys in both operands, each
with the value meet `V::pmeet(self's, other's)` (dropped if it annihilates).
`SELF` iff every key of `self` is shared and every shared value meet names
`self`; `COUNTER` symmetrically.  (The crate calls `pmeet(other's, self's)`
when `self` is not the smaller map: L1.) -/
def mapMeet (t : Ty) (a b : List (Nat × t.V)) : AlgResult (List (Nat × t.V)) :=
  let r := a.filterMap fun (k, x) => match mapLookup k b with
    | some y => ((t.meet x y).resolve x y).map (k, ·)
    | none => none
  let selfBit := a.all fun (k, x) => match mapLookup k b with
    | some y => (t.meet x y).hasBit SELF
    | none => false
  let ctrBit := b.all fun (k, y) => match mapLookup k a with
    | some x => (t.meet x y).hasBit COUNTER
    | none => false
  if r.isEmpty then .none
  else
    let m := (if selfBit then SELF else 0) ||| (if ctrBit then COUNTER else 0)
    if m == 0 then .element r else .identity m

/-- `HashMap<u8, V>`'s subtract: every key of `self`; a shared key's value is
`V::psubtract(self's, other's)`, dropped if that annihilates.  `SELF` iff
every shared key's subtraction is an identity; `None` if nothing is left. -/
def mapSub (t : Ty) (a b : List (Nat × t.V)) : AlgResult (List (Nat × t.V)) :=
  let r := a.filterMap fun (k, x) => match mapLookup k b with
    | none => some (k, x)
    | some y => match t.sub x y with
      | .none => none
      | .element v => some (k, v)
      | .identity _ => some (k, x)
  let ident := a.all fun (k, x) => match mapLookup k b with
    | none => true
    | some y => (t.sub x y).isIdentity
  if r.isEmpty then .none else if ident then .identity SELF else .element r

/-- `HashMap<u8, V>`: a finite map into `V`, stored as written (an entry with
an empty inner set is kept: `SetLattice`'s doc says empty sets "may or may not
be collapsed", so only `norm` identifies it with absence).  Operands: `n := u8
% 5` entries, key `u8 % 6`, then a value; a repeated key overwrites. -/
def mapTy (t : Ty) : Ty where
  name := s!"map<{t.name}>"
  V := List (Nat × t.V)
  dec d := do
    let (n, d) ← d.mod 5
    let rec go : Nat → List (Nat × t.V) → Dec → Option (List (Nat × t.V) × Dec)
      | 0, m, d => some (m, d)
      | k + 1, m, d => do
          let (b, d) ← d.u8
          let (v, d) ← t.dec d
          go k (mapInsert (b.toNat % 6) v m) d
    go n [] d
  render m := "{" ++ ",".intercalate (m.map fun (k, v) => s!"{k}:{t.render v}") ++ "}"
  beq a b := a.length == b.length && (a.zip b).all fun ((k, x), (j, y)) => k == j && t.beq x y
  norm m :=
    let r := m.filterMap fun (k, v) => (t.norm v).map (k, ·)
    if r.isEmpty then none else some r
  join := mapJoin t
  meet := mapMeet t
  sub := mapSub t
  joinInto := defaultJoinInto (mapJoin t)
  meetSym := t.meetSym
  hazard a b :=
    let shared := a.filter fun (k, _) => (mapLookup k b).isSome
    !t.meetSym && !shared.isEmpty &&
      (a.length ≥ b.length ||
        shared.any fun (k, x) => match mapLookup k b with
          | some y => t.hazard x y || t.hazard y x
          | none => false)

def u16Ty := intTy "u16" 16
def u64Ty := intTy "u64" 64

/-- The `Lattice` table (`lty!`). -/
def ltys : List Ty :=
  [ unitTy, boolTy, intTy "u8" 8, u16Ty, intTy "u32" 32, u64Ty, intTy "usize" 64,
    optTy unitTy, optTy boolTy, optTy u64Ty, optTy (optTy boolTy), optTy (optTy u64Ty),
    boxTy u64Ty, boxTy (optTy boolTy), setTy,
    mapTy unitTy, mapTy boolTy, mapTy u64Ty, mapTy setTy, mapTy (optTy u64Ty),
    optTy setTy, boxTy (mapTy u16Ty), mapTy (mapTy boolTy), mapTy (intTy "u8" 8) ]

/-- The `DistributiveLattice` table (`dty!`): `u8`, `u32`, `usize` have no
`DistributiveLattice` impl. -/
def dtys : List Ty :=
  [ unitTy, boolTy, u16Ty, u64Ty,
    optTy unitTy, optTy boolTy, optTy u64Ty, optTy (optTy boolTy), optTy (optTy u64Ty),
    boxTy u64Ty, boxTy (optTy boolTy), setTy,
    mapTy unitTy, mapTy boolTy, mapTy u64Ty, mapTy setTy, mapTy (optTy u64Ty),
    optTy setTy, boxTy (mapTy u16Ty), mapTy (mapTy boolTy) ]

/-! ## `join_all` -/

/-- `Lattice::join_all`: the join of all arguments, left to right; no
arguments is `None`.  Mask bit `i` names argument `i` when the step that
joined it reported it identical to the running result (an identity naming
the running result keeps the bits so far and adds `i` if `COUNTER` was also
set; one naming only argument `i` restarts the mask at bit `i`); a new
element or an annihilation clears the mask, and after an annihilation the
next argument is taken as is. -/
def joinAll (t : Ty) : List t.V → AlgResult t.V
  | [] => .none
  | x0 :: rest =>
      let step : (Nat × Option t.V) → (t.V × Nat) → (Nat × Option t.V)
        | (mask, none), (x, i) => (mask ||| (1 <<< i), some x)
        | (mask, some e), (x, i) =>
            match t.join e x with
            | .none => (0, none)
            | .element v => (0, some v)
            | .identity m =>
                if m &&& SELF != 0 then (mask ||| ((m &&& COUNTER) <<< (i - 1)), some e)
                else ((m &&& COUNTER) <<< (i - 1), some x)
      let (mask, e) := (rest.zipIdx 1).foldl step (SELF, some x0)
      if mask > 0 then .identity mask
      else match e with
        | some v => .element v
        | none => .none

/-! ## `AlgebraicResult::merge` -/

/-- `AlgebraicResult::merge`: the result of an op on a pair, from the results
`ra`, `rb` on its two fields.  `ia i` / `ib i` give argument `i`'s field
(`none` = that field is absent), `f` builds the pair from the two field
values.  Returns the result and the argument index each closure was asked
for (they are `FnOnce`: at most once each).

* Both fields annihilated: `None`.
* Both identities: the arguments both name (`sm ∧ bm`) if any, else the pair
  of the named arguments' fields.
* One field annihilated, the other an identity: the whole is still that
  identity if the annihilated field was absent to begin with.  The crate asks
  this of **argument 0** (`ia 0` / `ib 0`) whichever arguments the identity
  names — right for join (only absent ∨ absent is absent) and subtract
  (only `SELF` is ever named), not for meet: L2 in
  `lean/findings/u-lattice.md` (`mergeMeetUnsound` below).
* Anything else: `f` of the field values (an identity resolved to its lowest
  named argument). -/
def mergeRes {A B U : Type} (ra : AlgResult A) (rb : AlgResult B) (ia : Nat → Option A)
    (ib : Nat → Option B) (f : Option A → Option B → AlgResult U) :
    AlgResult U × Option Nat × Option Nat :=
  match ra, rb with
  | .none, .none => (.none, none, none)
  | .none, .element bv => (f none (some bv), none, none)
  | .none, .identity bm =>
      if (ia 0).isNone then (.identity bm, some 0, none)
      else (f none (ib (tz bm)), some 0, some (tz bm))
  | .identity sm, .none =>
      if (ib 0).isNone then (.identity sm, none, some 0)
      else (f (ia (tz sm)) none, some (tz sm), some 0)
  | .identity sm, .element bv => (f (ia (tz sm)) (some bv), some (tz sm), none)
  | .identity sm, .identity bm =>
      if sm &&& bm != 0 then (.identity (sm &&& bm), none, none)
      else (f (ia (tz sm)) (ib (tz bm)), some (tz sm), some (tz bm))
  | .element sv, .none => (f (some sv) none, none, none)
  | .element sv, .element bv => (f (some sv) (some bv), none, none)
  | .element sv, .identity bm => (f (some sv) (ib (tz bm)), none, some (tz bm))

/-! ## Op decoders and renderers -/

def showOptU64 : Option UInt64 → String
  | none => "None"
  | some v => s!"Some({v})"

def showOptBool : Option Bool → String
  | none => "None"
  | some b => s!"Some({if b then "true" else "false"})"

def showIdx : Option Nat → String
  | none => "-"
  | some i => toString i

def skipMeetSwap : String := "skip:setlattice-meet-swap"

/-- `skip:join-all-empty`, u-mask's token and rule (`skipJoinAllEmpty` in
`Mask.lean`, `lean/findings/u-mask.md` M1) applied to every type's default
`join_all`: when every argument is a bottom (its self-join is `None`) the
crate answers `None` or an identity by the parity of the argument count, and
the contract allows both, so either renders as the token.  `joinAll` above
reproduces the parity exactly; the skip only keeps the two models'
statements of `join_all` consistent. -/
def skipJoinAllEmptyL : String := "skip:join-all-empty"

/-- A mask operand: `b % 4` below 128, `b - 128` below 192, else one high bit. -/
def maskOfByte (b : UInt8) : Nat :=
  if b < 128 then b.toNat % 4
  else if b < 192 then b.toNat - 128
  else 1 <<< (b.toNat % 64)

def decAR (d : Dec) : Option (AlgResult UInt64 × Dec) := do
  let (tag, d) ← d.mod 3
  if tag == 0 then some (.none, d)
  else
    let (b, d) ← d.u8
    if tag == 1 then some (.identity (maskOfByte b), d) else some (.element (intOfByte b), d)

def decOptU64 (d : Dec) : Option (Option UInt64 × Dec) := do
  let (b, d) ← d.u8
  if b.toNat % 4 == 0 then some (none, d)
  else
    let (v, d) ← d.u8
    some (some (intOfByte v), d)

def decStatus (d : Dec) : Option (Status × Dec) := do
  let (s, d) ← d.mod 3
  some (if s == 0 then .element else if s == 1 then .identity else .none, d)

def decTable (d : Dec) : Option (List UInt64 × Dec) := do
  let (k, d) ← d.mod 4
  let rec go : Nat → Dec → Option (List UInt64 × Dec)
    | 0, d => some ([], d)
    | n + 1, d => do
        let (b, d) ← d.u8
        let (rest, d) ← go n d
        some (intOfByte b :: rest, d)
  go k d

def showTable (t : List UInt64) : String := "[" ++ ",".intercalate (t.map toString) ++ "]"

def show64 (v : UInt64) : String := toString v

def b01 (b : Bool) : String := if b then "1" else "0"

def two (t : Ty) (d : Dec) : Option ((t.V × t.V) × Dec) := do
  let (a, d) ← t.dec d
  let (b, d) ← t.dec d
  some ((a, b), d)

def opPjoin (t : Ty) (d : Dec) : Option (String × Dec) := do
  let ((a, b), d) ← two t d
  some (s!"{t.name} {t.render a} {t.render b} {showAlgResult t.render (t.join a b)}", d)

def opPmeet (t : Ty) (full : Bool) (d : Dec) : Option (String × Dec) := do
  let ((a, b), d) ← two t d
  let r := if !full && t.hazard a b then skipMeetSwap else showAlgResult t.render (t.meet a b)
  some (s!"{t.name} {t.render a} {t.render b} {r}", d)

def opPsub (t : Ty) (d : Dec) : Option (String × Dec) := do
  let ((a, b), d) ← two t d
  some (s!"{t.name} {t.render a} {t.render b} {showAlgResult t.render (t.sub a b)}", d)

def opJoinInto (t : Ty) (d : Dec) : Option (String × Dec) := do
  let ((a, b), d) ← two t d
  let (s, x) := t.joinInto a b
  some (s!"{t.name} {t.render a} {t.render b} {s.show} {t.render x}", d)

def decMany (t : Ty) : Nat → Dec → Option (List t.V × Dec)
  | 0, d => some ([], d)
  | k + 1, d => do
      let (x, d) ← t.dec d
      let (rest, d) ← decMany t k d
      some (x :: rest, d)

def opJoinAll (t : Ty) (d : Dec) : Option (String × Dec) := do
  let (n, d) ← d.mod 5
  let (xs, d) ← decMany t n d
  let r := joinAll t xs
  let allBot := !xs.isEmpty && xs.all fun x => match t.join x x with | .none => true | _ => false
  let allowed := match r with
    | .none => true
    | .identity m => m != 0 && m >>> xs.length == 0
    | .element _ => false
  let rs := if allBot && allowed then skipJoinAllEmptyL else showAlgResult t.render r
  some (s!"{t.name} [{",".intercalate (xs.map t.render)}] {rs}", d)

/-- `LatticeRef` for `&V` is `V`'s ops, for `Option<&V>` `Option<V>`'s. -/
def opLref (t : Ty) (mode : Nat) (d : Dec) : Option (String × Dec) :=
  let u := if mode < 2 then t else optTy t
  if mode % 2 == 0 then opPjoin u d else opPmeet u false d

/-- `DistributiveLatticeRef`: likewise. -/
def opDref (t : Ty) (opt : Bool) (d : Dec) : Option (String × Dec) :=
  opPsub (if opt then optTy t else t) d

/-- `IDEMPOTENT` is `true` for every impl (none overrides the default);
`SELF_IDENT` = 1, `COUNTER_IDENT` = 2; `AlgebraicResult::default()` is
`None`, `AlgebraicStatus::default()` is `Element`. -/
def opConsts (t : Ty) (d : Dec) : Option (String × Dec) := do
  let (di, d) ← d.mod dtys.length
  let dt := dtys.getD di unitTy
  some (s!"{t.name}:1 {dt.name}:1 self1 counter2 None Element", d)

def opArQuery (d : Dec) : Option (String × Dec) := do
  let (r, d) ← decAR d
  let (n, i, e) := match r with
    | .none => (true, false, false) | .identity _ => (false, true, false) | .element _ => (false, false, true)
  let m := match r with | .identity m => toString m | _ => "-"
  let s := showAlgResult show64 r
  some (s!"{s} n{b01 n}i{b01 i}e{b01 e} m{m} {r.status.show} {s} eq1", d)

def opArInvert (d : Dec) : Option (String × Dec) := do
  let (r, d) ← decAR d
  some (s!"{showAlgResult show64 r} {showAlgResult show64 r.invert}", d)

def opArMap (d : Dec) : Option (String × Dec) := do
  let (r, d) ← decAR d
  let m := r.map (fun v => v * 3 + 1)
  let a := r.map (fun v => v ^^^ 0xff)
  let s := r.map (fun v => s!"s{v}")
  some (s!"{showAlgResult show64 r} {showAlgResult show64 m} {showAlgResult show64 a} {showAlgResult id s}", d)

/-- `into_option`, `unwrap`, `unwrap_or`: an identity is the table entry at
`trailing_zeros(mask)` (indexing past the table panics, as slice indexing
does); `unwrap` of `None` panics (documented). -/
def opArUnwrap (d : Dec) : Option (String × Dec) := do
  let (r, d) ← decAR d
  let (t, d) ← decTable d
  let (nb, d) ← d.u8
  let nv := intOfByte nb
  let ident (m : Nat) (k : UInt64 → String) : String :=
    match t[tz m]? with
    | some v => k v
    | none => "panic"
  let io := match r with
    | .none => "None" | .element v => s!"Some({v})" | .identity m => ident m (fun v => s!"Some({v})")
  let uw := match r with
    | .none => "panic" | .element v => toString v | .identity m => ident m toString
  let uo := match r with
    | .none => toString nv | .element v => toString v | .identity m => ident m toString
  some (s!"{showAlgResult show64 r} {showTable t} {nv} io={io} uw={uw} uo={uo}", d)

/-- `map_into_option` / `unwrap_or_else`: an identity calls the closure with
`trailing_zeros(mask)`; `None` calls `none_f` (rendered `n`). -/
def opArClosures (d : Dec) : Option (String × Dec) := do
  let (r, d) ← decAR d
  let (t, d) ← decTable d
  let (mio, c1) : Option UInt64 × Option Nat := match r with
    | .none => (none, none) | .element v => (some v, none) | .identity m => (t[tz m]?, some (tz m))
  let (uoe, c2, n) : UInt64 × Option Nat × String := match r with
    | .none => (99, none, "n")
    | .element v => (v, none, "")
    | .identity m => ((t[tz m]?).getD 77, some (tz m), "")
  some (s!"{showAlgResult show64 r} {showTable t} mio={showOptU64 mio}@{showIdx c1} uoe={uoe}@{showIdx c2}{n}", d)

def decArOpt (d : Dec) : Option (AlgResult (Option UInt64) × Dec) := do
  let (tag, d) ← d.mod 3
  if tag == 0 then some (.none, d)
  else if tag == 1 then do
    let (b, d) ← d.u8
    some (.identity (maskOfByte b), d)
  else do
    let (o, d) ← decOptU64 d
    some (.element o, d)

def opArStatus (d : Dec) : Option (String × Dec) := do
  let (st, d) ← decStatus d
  let (vb, d) ← d.u8
  let v := intOfByte vb
  let (ro, d) ← decArOpt d
  some (s!"{st.show} {v} {showAlgResult show64 (AlgResult.fromStatus st v)} {showAlgResult showOptU64 ro} {showAlgResult show64 ro.flatten}", d)

def opArEq (d : Dec) : Option (String × Dec) := do
  let (a, d) ← decAR d
  let (b, d) ← decAR d
  let e := a.beqWith (· == ·) b
  some (s!"{showAlgResult show64 a} {showAlgResult show64 b} eq{b01 e} ne{b01 !e}", d)

def opArMerge (d : Dec) : Option (String × Dec) := do
  let (ra, d) ← decAR d
  let (rb, d) ← decAR d
  let (ta0, d) ← decOptU64 d
  let (ta1, d) ← decOptU64 d
  let (tb0, d) ← decOptU64 d
  let (tb1, d) ← decOptU64 d
  let (fmode, d) ← d.mod 2
  let ta := [ta0, ta1]
  let tb := [tb0, tb1]
  let f (x y : Option UInt64) : AlgResult (Option UInt64 × Option UInt64) :=
    if fmode == 1 && x.isNone && y.isNone then .none else .element (x, y)
  let (r, ca, cb) := mergeRes ra rb (fun i => (ta[i]?).join) (fun i => (tb[i]?).join) f
  let sp := fun (p : Option UInt64 × Option UInt64) => s!"({showOptU64 p.1},{showOptU64 p.2})"
  some (s!"{showAlgResult show64 ra} {showAlgResult show64 rb} {showOptU64 ta0},{showOptU64 ta1} {showOptU64 tb0},{showOptU64 tb1} f{fmode} {showAlgResult sp r} a@{showIdx ca} b@{showIdx cb}", d)

/-- The field ops `ring_merge_fields` composes: `Option<bool>` and
`Option<u64>`, flattened (an absent field is `None`). -/
def fieldOp (t : Ty) (op : Nat) : t.V → t.V → AlgResult t.V :=
  if op == 0 then t.join else if op == 1 then t.meet else t.sub

/-- `merge` composing a pair's result from per-field results, with the pair
built as `(field0, field1)` (`None` if both absent). -/
def mergeFields (op : Nat) (a1 b1 : Option Bool) (a2 b2 : Option UInt64) :
    AlgResult Bool × AlgResult UInt64 × AlgResult (Option Bool × Option UInt64) :=
  let f1 : AlgResult Bool := AlgResult.flatten (fieldOp (optTy boolTy) op a1 b1)
  let f2 : AlgResult UInt64 := AlgResult.flatten (fieldOp (optTy u64Ty) op a2 b2)
  let t1 := [a1, b1]
  let t2 := [a2, b2]
  let (m, _, _) := mergeRes f1 f2 (fun i => (t1[i]?).join) (fun i => (t2[i]?).join)
    (fun x y => if x.isNone && y.isNone then .none else .element (x, y))
  (f1, f2, m)

def opMergeFields (d : Dec) : Option (String × Dec) := do
  let (op, d) ← d.mod 3
  let (a1, d) ← (optTy boolTy).dec d
  let (a2, d) ← (optTy u64Ty).dec d
  let (b1, d) ← (optTy boolTy).dec d
  let (b2, d) ← (optTy u64Ty).dec d
  let (f1, f2, m) := mergeFields op a1 b1 a2 b2
  let sp := fun (p : Option Bool × Option UInt64) => s!"({showOptBool p.1},{showOptU64 p.2})"
  let opn := if op == 0 then "join" else if op == 1 then "meet" else "sub"
  some (s!"{opn} ({showOptBool a1},{showOptU64 a2}) ({showOptBool b1},{showOptU64 b2}) {showAlgResult boolTy.render f1} {showAlgResult show64 f2} {showAlgResult sp m}", d)

def opStatus (d : Dec) : Option (String × Dec) := do
  let (a, d) ← decStatus d
  let (b, d) ← decStatus d
  let (an, d) ← d.bool
  let (bn, d) ← d.bool
  let cmp := if a.rank < b.rank then "<" else if a.rank == b.rank then "=" else ">"
  let mx := if a.rank ≥ b.rank then a else b
  some (s!"{a.show} {b.show} {b01 an}{b01 bn} n{b01 (a == .none)}i{b01 (a == .identity)}e{b01 (a == .element)} {cmp} max{mx.show} {(Status.merge a b an bn).show}", d)

def setLatticeSetStep (s : List Nat) (sub x : Nat) : String × List Nat :=
  if sub == 0 then (s!"len{s.length}", s)
  else if sub == 1 then (s!"e{b01 s.isEmpty}", s)
  else if sub == 2 then (s!"c{x}{b01 (s.contains x)}", s)
  else if sub == 3 then (s!"i{x}", setInsert x s)
  else if sub == 4 then (s!"r{x}", s.filter (· != x))
  else if sub == 5 then (s!"g{x}{if s.contains x then "+" else "-"}", s)
  else if sub == 6 then (if s.contains x then s!"p{x}" else "p-", s)
  else if sub == 7 then (s!"it[{",".intercalate (s.map toString)}]", s)
  else (s!"sh{showNatSet s}", s)

def setLatticeSetLoop : Nat → List Nat → List String → Dec → Option (List String × List Nat × Dec)
  | 0, s, out, d => some (out, s, d)
  | k + 1, s, out, d => do
      let (sub, d) ← d.mod 9
      let (kb, d) ← d.u8
      let (line, s) := setLatticeSetStep s sub (kb.toNat % 8)
      setLatticeSetLoop k s (out ++ [line]) d

/-- The `SetLattice` methods on `HashSet<u8>`, as a set: `with_capacity` is
empty, `insert` adds, `remove` deletes, `get` is membership, `replace` (only
called on a member, its precondition) changes nothing, `iter` lists the
members (in an unspecified order: rendered sorted), `shrink_to_fit` changes
nothing. -/
def opSetLatticeSet (d : Dec) : Option (String × Dec) := do
  let (cap, d) ← d.bool
  let (s, d) ← if cap then (do let (_, d) ← d.mod 8; some (([] : List Nat), d)) else setTy.dec d
  let (n, d) ← d.mod 6
  let (out, s', d) ← setLatticeSetLoop n s [showNatSet s] d
  some (" ".intercalate (out ++ [showNatSet s']), d)

abbrev U64Map := List (Nat × UInt64)

def showU64Map (m : U64Map) : String := (mapTy u64Ty).render m

def setLatticeMapLoop : Nat → U64Map → List String → Dec → Option (List String × U64Map × Dec)
  | 0, s, out, d => some (out, s, d)
  | k + 1, s, out, d => do
      let (sub, d) ← d.mod 9
      let (kb, d) ← d.u8
      let x := kb.toNat % 6
      let present := (mapLookup x s).isSome
      let (line, s, d) ← (
        if sub == 0 then some (s!"len{s.length}", s, d)
        else if sub == 1 then some (s!"e{b01 s.isEmpty}", s, d)
        else if sub == 2 then some (s!"c{x}{b01 present}", s, d)
        else if sub == 3 then do
          let (vb, d) ← d.u8
          let v := intOfByte vb
          some (s!"i{x}={v}", mapInsert x v s, d)
        else if sub == 4 then some (s!"r{x}", s.filter (·.1 != x), d)
        else if sub == 5 then some (s!"g{x}{showOptU64 (mapLookup x s)}", s, d)
        else if sub == 6 then do
          let (vb, d) ← d.u8
          let v := intOfByte vb
          if present then some (s!"p{x}={v}", mapInsert x v s, d) else some ("p-", s, d)
        else if sub == 7 then
          some (s!"it[{",".intercalate (s.map fun (k, v) => s!"{k}:{v}")}]", s, d)
        else some (s!"sh{showU64Map s}", s, d) : Option (String × U64Map × Dec))
      setLatticeMapLoop k s (out ++ [line]) d

/-- The `SetLattice` methods on `HashMap<u8, u64>`, as a finite map;
`insert` overwrites, `replace` (members only) sets the value. -/
def opSetLatticeMap (d : Dec) : Option (String × Dec) := do
  let (cap, d) ← d.bool
  let (s, d) ← if cap then (do let (_, d) ← d.mod 8; some (([] : U64Map), d)) else (mapTy u64Ty).dec d
  let (n, d) ← d.mod 6
  let (out, s', d) ← setLatticeMapLoop n s [showU64Map s] d
  some (" ".intercalate (out ++ [showU64Map s']), d)

/-- Selector − 30 → op name (`OPS` in the Rust file). -/
def latticeOps : List String :=
  [ "ring_pjoin", "ring_pmeet", "ring_psubtract", "ring_join_into", "ring_join_all",
    "ring_lref", "ring_dref", "ring_pjoin", "ring_pmeet", "ring_psubtract",
    "ring_ar_query", "ring_ar_invert", "ring_ar_map", "ring_ar_unwrap", "ring_ar_closures",
    "ring_ar_status", "ring_ar_eq", "ring_ar_merge", "ring_merge_fields", "ring_status",
    "ring_setlattice_set", "ring_setlattice_map", "ring_consts", "ring_join_into", "ring_merge_fields",
    "ring_ar_merge", "ring_pjoin", "ring_pmeet", "ring_psubtract", "ring_join_all" ]

def withL (d : Dec) (k : Ty → Dec → Option (String × Dec)) : Option (String × Dec) := do
  let (i, d) ← d.mod ltys.length
  k (ltys.getD i unitTy) d

def withD (d : Dec) (k : Ty → Dec → Option (String × Dec)) : Option (String × Dec) := do
  let (i, d) ← d.mod dtys.length
  k (dtys.getD i unitTy) d

def stepLattice (op : Nat) (d : Dec) : Option ((String × String) × Dec) := do
  let name := latticeOps.getD (op - 30) "nop"
  if name == "ring_pmeet" then
    let (fb, d) ← d.u8
    let full := fb == 255
    let (r, d) ← withL d (fun t => opPmeet t full)
    return ((if full then "ring_pmeet!" else "ring_pmeet", r), d)
  let (r, d) ←
    if name == "ring_pjoin" then withL d opPjoin
    else if name == "ring_psubtract" then withD d opPsub
    else if name == "ring_join_into" then withL d opJoinInto
    else if name == "ring_join_all" then withL d opJoinAll
    else if name == "ring_lref" then do
      let (mode, d) ← d.mod 4
      withL d (fun t => opLref t mode)
    else if name == "ring_dref" then do
      let (opt, d) ← d.bool
      withD d (fun t => opDref t opt)
    else if name == "ring_ar_query" then opArQuery d
    else if name == "ring_ar_invert" then opArInvert d
    else if name == "ring_ar_map" then opArMap d
    else if name == "ring_ar_unwrap" then opArUnwrap d
    else if name == "ring_ar_closures" then opArClosures d
    else if name == "ring_ar_status" then opArStatus d
    else if name == "ring_ar_eq" then opArEq d
    else if name == "ring_ar_merge" then opArMerge d
    else if name == "ring_merge_fields" then opMergeFields d
    else if name == "ring_status" then opStatus d
    else if name == "ring_setlattice_set" then opSetLatticeSet d
    else if name == "ring_setlattice_map" then opSetLatticeMap d
    else withL d opConsts
  some ((name, r), d)

/-! ## Laws

Checked by `#guard` over small exhaustive universes, on the *values* the
results denote (`AlgResult.resolve`, with an absent result as the bottom) up to
`Ty.norm` (an empty set, an absent option, `false` are all the bottom).  The
lattice laws, the subtraction laws of a distributive lattice
(`a − a = ⊥`, `(a − b) ∧ b = ⊥`, `(a − b) ∨ (a ∧ b) = a`), the truthfulness of
every identity mask (a set bit names an operand *representationally* equal to
the answer; subtraction never names `other`), and the promise the
`IDEMPOTENT = true` default makes (`pjoin(a, a)` and `pmeet(a, a)` are
`Identity(SELF | COUNTER)`, `psubtract(a, a)` is `None`).

`lawFails` lists the laws a type breaks; each `#guard` pins that list, so the
deliberate failures are written down here:

* the integers (`intTy`) are not commutative (left projection), and
  `(a − b) ∧ b` is `a` for `a ≠ b`, not `⊥`;
* `bool`, the integers, and every container of them break the
  `IDEMPOTENT` promise (L3 in `lean/findings/u-lattice.md`).
-/

namespace Laws

def liftJ (t : Ty) : Option t.V → Option t.V → Option t.V
  | none, x => x
  | x, none => x
  | some a, some b => (t.join a b).resolve a b

def liftM (t : Ty) : Option t.V → Option t.V → Option t.V
  | some a, some b => (t.meet a b).resolve a b
  | _, _ => none

def liftS (t : Ty) : Option t.V → Option t.V → Option t.V
  | none, _ => none
  | some a, none => some a
  | some a, some b => (t.sub a b).resolve a b

/-- Equal meanings. -/
def eqv (t : Ty) (x y : Option t.V) : Bool :=
  match x.bind t.norm, y.bind t.norm with
  | none, none => true
  | some a, some b => t.beq a b
  | _, _ => false

/-- An identity mask is truthful: non-zero, arity-2 bits only, `COUNTER` only
when allowed and, with `SELF`, only for equal operands.  (A lone bit names the
operand the answer resolves to, so it is the answer by construction.) -/
def truthful (t : Ty) (r : AlgResult t.V) (a b : t.V) (counterOk : Bool) : Bool :=
  match r with
  | .identity m =>
      m != 0 && m >>> 2 == 0 && (m &&& COUNTER == 0 || counterOk) &&
        (m != 3 || t.beq a b)
  | _ => true

def isIdent3 {V : Type} : AlgResult V → Bool
  | .identity 3 => true
  | _ => false

def isNone {V : Type} : AlgResult V → Bool
  | .none => true
  | _ => false

def lawFails (t : Ty) (xs : List t.V) (dl : Bool) : List String :=
  let os := xs.map some
  let all1 (p : Option t.V → Bool) := os.all p
  let all2 (p : Option t.V → Option t.V → Bool) := os.all fun a => os.all fun b => p a b
  let all3 (p : Option t.V → Option t.V → Option t.V → Bool) :=
    os.all fun a => os.all fun b => os.all fun c => p a b c
  let J := liftJ t
  let M := liftM t
  let S := liftS t
  let e := eqv t
  let laws : List (String × Bool × Bool) := [
    ("join-idem", all1 (fun a => e (J a a) a), true),
    ("join-comm", all2 (fun a b => e (J a b) (J b a)), true),
    ("join-assoc", all3 (fun a b c => e (J (J a b) c) (J a (J b c))), true),
    ("meet-idem", all1 (fun a => e (M a a) a), true),
    ("meet-comm", all2 (fun a b => e (M a b) (M b a)), true),
    ("meet-assoc", all3 (fun a b c => e (M (M a b) c) (M a (M b c))), true),
    ("absorb", all2 (fun a b => e (J a (M a b)) a && e (M a (J a b)) a), true),
    ("distrib", all3 (fun a b c => e (M a (J b c)) (J (M a b) (M a c))), true),
    ("sub-self", all1 (fun a => e (S a a) none), dl),
    ("sub-disjoint", all2 (fun a b => e (M (S a b) b) none), dl),
    ("sub-recover", all2 (fun a b => e (J (S a b) (M a b)) a), dl),
    ("masks", xs.all fun a => xs.all fun b =>
        truthful t (t.join a b) a b true && truthful t (t.meet a b) a b true &&
        (!dl || truthful t (t.sub a b) a b false), true),
    ("idempotent-promise", xs.all fun a =>
        -- a bottom may answer `None` instead (NOTE: `None` takes precedence)
        let bot := (t.norm a).isNone
        let ok (r : AlgResult t.V) := isIdent3 r || (bot && isNone r)
        ok (t.join a a) && ok (t.meet a a) && (!dl || isNone (t.sub a a)), true) ]
  laws.filterMap fun (n, ok, applies) => if applies && !ok then some n else none

def setSamples : List (List Nat) := [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]
def nonEmptySets : List (List Nat) := [[0], [1], [0, 1]]

def maps {V : Type} (keys : List Nat) (vals : List V) : List (List (Nat × V)) :=
  keys.foldr (fun k acc => acc ++ (acc.flatMap fun m => vals.map fun v => mapInsert k v m)) [[]]

#guard lawFails unitTy [()] true == []
#guard lawFails boolTy [false, true] true == ["idempotent-promise"]
#guard lawFails u64Ty ([0, 1, 2] : List UInt64) true == ["join-comm", "meet-comm", "sub-disjoint", "idempotent-promise"]
#guard lawFails (intTy "u8" 8) ([0, 1, 255] : List UInt64) false ==
  ["join-comm", "meet-comm", "idempotent-promise"]
#guard lawFails (optTy unitTy) [none, some ()] true == []
#guard lawFails (optTy boolTy) [none, some false, some true] true == ["idempotent-promise"]
#guard lawFails (optTy u64Ty) ([none, some 0, some 1] : List (Option UInt64)) true == ["join-comm", "meet-comm", "sub-disjoint", "idempotent-promise"]
#guard lawFails (optTy (optTy boolTy)) [none, some none, some (some false), some (some true)] true ==
  ["idempotent-promise"]
#guard lawFails setTy setSamples true == []
#guard lawFails (optTy setTy) (none :: setSamples.map some) true == []
#guard lawFails (mapTy unitTy) (maps [0, 1, 2] [()]) true == []
#guard lawFails (mapTy boolTy) (maps [0, 1] [false, true]) true == ["idempotent-promise"]
#guard lawFails (mapTy u64Ty) (maps [0, 1] ([0, 1] : List UInt64)) true == ["join-comm", "meet-comm", "sub-disjoint", "idempotent-promise"]
#guard lawFails (mapTy setTy) (maps [0, 1] nonEmptySets) true == []
#guard lawFails (mapTy (mapTy boolTy)) (maps [0, 1] (maps [0] [false, true])) true == ["idempotent-promise"]
-- `Box<V>` is `V`.
#guard lawFails (boxTy (optTy boolTy)) [none, some false, some true] true == ["idempotent-promise"]

/- `Basic.u64Ops`, the value instance the trie model uses, agrees with
`u64Ty` on every answer's value and names a subset of its operands: it omits
`COUNTER` on equal operands of a join (allowed; left as is because the trie
model's statuses are built on it). -/
#guard ([0, 1, 2] : List UInt64).all fun a => ([0, 1, 2] : List UInt64).all fun b =>
  let sub (x y : AlgResult UInt64) : Bool := match x, y with
    | .identity m, .identity n => m &&& n == m
    | .none, .none => true
    | _, _ => false
  sub (AlgResult.ofValRes (u64Ops.pjoin a b)) (u64Ty.join a b) &&
  sub (AlgResult.ofValRes (u64Ops.pmeet a b)) (u64Ty.meet a b) &&
  sub (AlgResult.ofValRes (u64Ops.psub a b)) (u64Ty.sub a b)

-- The same for `Basic.unitOps` and `unitTy`, exactly.
#guard showAlgResult (fun _ => "()") (AlgResult.ofValRes (unitOps.pjoin () ())) ==
  showAlgResult unitTy.render (unitTy.join () ())

/-! ### `join_all` is the n-ary join -/

/-- On sets (identity bits maximal), `joinAll`'s answer denotes the union of
its arguments and names exactly the arguments equal to it, except that an
all-empty argument list may answer by an identity (M1, allowed). -/
def joinAllSound (xs : List (List Nat)) : Bool :=
  let u := xs.foldl (fun s x => x.foldl (fun s k => setInsert k s) s) []
  let named := (xs.zipIdx.filter fun (x, _) => x == u).foldl (fun acc (_, i) => acc ||| (1 <<< i)) 0
  match (joinAll setTy xs : AlgResult (List Nat)) with
  | .none => u.isEmpty
  | .element v => setTy.beq v u && named == 0
  | .identity m => m == named || (u.isEmpty && m != 0 && m &&& named == m)

#guard (setSamples.flatMap fun a => setSamples.flatMap fun b => [[a], [a, b]] ++
  ([[], [0], [0, 1]].map fun c => [a, b, c])).all joinAllSound

-- M1, reproduced by the fold: all-empty arguments answer by parity.
#guard showAlgResult showNatSet (joinAll setTy [[]]) == "Identity(1)"
#guard showAlgResult showNatSet (joinAll setTy [[], []]) == "None"
#guard showAlgResult showNatSet (joinAll setTy [[], [], []]) == "Identity(4)"

/-! ### `merge` -/

/-- The pair a composite answer denotes: the merged result resolved against the
two argument pairs. -/
def mergedValue (op : Nat) (a1 b1 : Option Bool) (a2 b2 : Option UInt64) :
    Option (Option Bool × Option UInt64) :=
  let (_, _, m) := mergeFields op a1 b1 a2 b2
  match m with
  | .none => some (none, none)
  | .element v => some v
  | .identity k => if k == 1 then some (a1, a2) else if k == 2 then some (b1, b2)
      else if k == 3 then (if a1 == b1 && a2 == b2 then some (a1, a2) else none) else none

/-- `merge` is sound for a composite op when the whole answer denotes the pair
of the field answers. -/
def mergeSound (op : Nat) : Bool :=
  let ob : List (Option Bool) := [none, some false, some true]
  let ou : List (Option UInt64) := [none, some 0, some 1]
  ob.all fun a1 => ob.all fun b1 => ou.all fun a2 => ou.all fun b2 =>
    let f1 := (fieldOp (optTy boolTy) op a1 b1).resolve a1 b1 |>.join
    let f2 := (fieldOp (optTy u64Ty) op a2 b2).resolve a2 b2 |>.join
    mergedValue op a1 b1 a2 b2 == some (f1, f2)

#guard mergeSound 0      -- join
#guard mergeSound 2      -- subtract
#guard !mergeSound 1     -- meet: L2

/-- L2's smallest case: field 0 `Some(true) ∧ Some(false)` is
`Identity(COUNTER)`, field 1 `None ∧ Some(5)` is `None`.  `merge` asks
argument 0's field 1 (`None`), so it answers `Identity(COUNTER)`, claiming the
whole is `(Some(false), Some(5))`; the meet is `(Some(false), None)`. -/
def mergeMeetUnsound : Bool :=
  let (f1, f2, m) := mergeFields 1 (some true) (some false) none (some 5)
  showAlgResult boolTy.render f1 == "Identity(2)" && showAlgResult show64 f2 == "None" &&
    (match m with | .identity 2 => true | _ => false)

#guard mergeMeetUnsound

/-! ### `AlgebraicStatus::merge` -/

/- The crate's truth table (`ring.rs`), row by row, against the semantic
definition `Status.merge`. -/
#guard
  let ss := [Status.element, .identity, .none]
  ss.all fun a => ss.all fun b => [false, true].all fun an => [false, true].all fun bn =>
    let crate := match a, b with
      | .none, .none => Status.none
      | .none, .element => .element
      | .none, .identity => if an then .identity else .element
      | .identity, .element => .element
      | .identity, .identity => .identity
      | .identity, .none => if bn then .identity else .element
      | .element, _ => .element
    Status.merge a b an bn == crate

end Laws

end UtilFuzz
end PathMapModel
