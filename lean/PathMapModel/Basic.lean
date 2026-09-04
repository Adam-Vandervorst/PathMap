/-!
# Basic types for the PathMap / zipper model

This module fixes the vocabulary the rest of the model is written in:

* `Path`   — a key in the trie: a finite sequence of bytes.
* `≼`      — the prefix order on paths.
* `Path.lt`— the *lexicographic* order on paths, in which a proper prefix sorts
             **before** its extensions.  This is exactly the order in which a
             depth-first traversal of a radix trie visits its paths, so every
             iteration primitive in the model (`to_next_val`, `to_next_step`,
             `descend_first_k_path`, ...) is specified as "the least path,
             w.r.t. `Path.lt`, satisfying ...".
* `ByteMask` — the 256-bit child mask, modelled as a sorted duplicate-free list
             of bytes.  `indexedBit`/`nextBit`/`prevBit` mirror
             `pathmap::utils::ByteMask`.
* `ValOps` — the fragment of the `Lattice` / `DistributiveLattice` traits that
             the trie operations actually consume.
-/

namespace PathMapModel

/-- A key/path in the trie.  Bytes, most-significant first. -/
abbrev Path := List UInt8

/-- `pathmap::ring::AlgebraicResult` at the *value* level: either a freshly
computed element, an assertion that the result is already one of the operands
(`Identity`, with the `SELF_IDENT` / `COUNTER_IDENT` mask spelled out as two
flags), or annihilation. -/
inductive ValRes (V : Type) where
  /-- `AlgebraicResult::Element` -/
  | elem : V → ValRes V
  /-- `AlgebraicResult::Identity(mask)`; the flags are `SELF_IDENT`, `COUNTER_IDENT`. -/
  | identity : Bool → Bool → ValRes V
  /-- `AlgebraicResult::None` -/
  | none : ValRes V

/-- A value type together with the algebraic operations `pathmap` requires of it.

These return `ValRes` rather than plain values because `pathmap` reports
`AlgebraicStatus` to the caller, and the status depends on *which constructor*
the value operation returned, not on whether the value changed.  `u64`'s
`psubtract`, for instance, returns `Element(*self)` — an `Element` status even
though the stored value is unchanged. -/
structure ValOps (V : Type) where
  /-- `Lattice::pjoin` -/
  pjoin : V → V → ValRes V
  /-- `Lattice::pmeet` -/
  pmeet : V → V → ValRes V
  /-- `DistributiveLattice::psubtract` -/
  psub : V → V → ValRes V
  /-- Decidable equality on values. -/
  beq : V → V → Bool

/-- Turn a `ValRes` into the value it denotes, given both operands. -/
def ValRes.resolve {V : Type} : ValRes V → V → V → Option V
  | .elem v, _, _ => some v
  | .identity s _, a, b => some (if s then a else b)
  | .none, _, _ => Option.none

/-- The instance `pathmap` provides for `u64` (see `impl Lattice for u64` in `src/ring.rs`).

Both `pjoin` and `pmeet` return `Identity(SELF_IDENT)`: they are *left-biased
projections* that ignore the counterpart value entirely.  `psubtract`
annihilates only when the two values are equal, and otherwise returns
`Element(*self)`.  This is the instance the differential fuzz target uses, so
the model reproduces it exactly rather than assuming a "real" lattice. -/
def u64Ops : ValOps UInt64 where
  pjoin _ _ := .identity true false
  pmeet _ _ := .identity true false
  psub a b := if a == b then .none else .elem a
  beq a b := a == b

/-! ## Prefix order -/

/-- `p ≼ q`: `p` is a prefix of `q`. -/
def Path.isPrefixOf : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && Path.isPrefixOf as bs

/-- Notation for `Path.isPrefixOf`. -/
infix:50 " ≼ " => fun p q => Path.isPrefixOf p q

/-- Every prefix of `p`, shortest first: `[] , p[..1], ..., p`. -/
def Path.prefixes (p : Path) : List Path :=
  (List.range (p.length + 1)).map (fun n => p.take n)

/-- Every *proper* prefix of `p`, shortest first: `[], p[..1], ..., p[..n-1]`.

Used to phrase "the nearest ancestor such that ..." as a filter over ancestors,
rather than as a loop that walks upward. -/
def Path.properPrefixes (p : Path) : List Path :=
  (List.range p.length).map (fun n => p.take n)

/-- Drop `p` from the front of `q`, if `p` is a prefix of `q`. -/
def Path.stripPrefix : Path → Path → Option Path
  | [], q => some q
  | _ :: _, [] => none
  | a :: as, b :: bs => if a == b then Path.stripPrefix as bs else none

/-! ## Lexicographic (depth-first) order

`[] < [0] < [0,0] < [0,255] < [1]`.  A proper prefix always precedes its
extensions, which is what makes this coincide with depth-first traversal order. -/

/-- Strict lexicographic order on paths. -/
def Path.lt : Path → Path → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true
      else if b < a then false
      else Path.lt as bs

/-- Non-strict lexicographic order. -/
def Path.le (p q : Path) : Bool := Path.lt p q || p == q

instance : LT Path := ⟨fun p q => Path.lt p q = true⟩
instance : LE Path := ⟨fun p q => Path.le p q = true⟩

/-- Insertion into a `Path.lt`-sorted list, dropping duplicates. -/
def Path.insertSorted (p : Path) : List Path → List Path
  | [] => [p]
  | q :: qs =>
      if p == q then q :: qs
      else if Path.lt p q then p :: q :: qs
      else q :: Path.insertSorted p qs

/-- Sort and deduplicate a list of paths. -/
def Path.sortDedup (ps : List Path) : List Path :=
  ps.foldl (fun acc p => Path.insertSorted p acc) []

/-! ## Byte masks

`ByteMask` is `pathmap`'s 256-bit child mask.  We model it as the sorted,
duplicate-free list of set bytes; that is the only thing the API observes. -/

/-- A 256-bit child mask, as the ascending list of its set bytes. -/
abbrev ByteMask := List UInt8

/-- Sort/dedup a byte list into canonical `ByteMask` form. -/
def ByteMask.ofList (bs : List UInt8) : ByteMask :=
  (List.range 256).filterMap fun i =>
    let b := UInt8.ofNat i
    if bs.contains b then some b else none

/-- `ByteMask::count_bits`. -/
def ByteMask.countBits (m : ByteMask) : Nat := m.length

/-- `ByteMask::indexed_bit::<true>` — the `idx`-th set byte in ascending order. -/
def ByteMask.indexedBit (m : ByteMask) (idx : Nat) : Option UInt8 := m[idx]?

/-- `ByteMask::next_bit` — the least set byte strictly greater than `b`. -/
def ByteMask.nextBit (m : ByteMask) (b : UInt8) : Option UInt8 :=
  (m.filter (fun x => b < x)).head?

/-- `ByteMask::prev_bit` — the greatest set byte strictly less than `b`. -/
def ByteMask.prevBit (m : ByteMask) (b : UInt8) : Option UInt8 :=
  (m.filter (fun x => x < b)).getLast?

/-! ## Algebraic status

Mirrors `pathmap::ring::AlgebraicStatus`. -/

/-- `pathmap::ring::AlgebraicStatus`. -/
inductive AlgStatus where
  /-- `self` holds the operation's output. -/
  | element
  /-- `self` was not modified by the operation. -/
  | identity
  /-- `self` was annihilated and is now empty. -/
  | none
deriving DecidableEq, Repr, Inhabited

namespace AlgStatus

def toString : AlgStatus → String
  | .element => "Element"
  | .identity => "Identity"
  | .none => "None"

instance : ToString AlgStatus := ⟨toString⟩

/-- `AlgebraicStatus::merge`, transcribed from `src/ring.rs`. -/
def merge : AlgStatus → AlgStatus → Bool → Bool → AlgStatus
  | .none, .none, _, _ => .none
  | .none, .element, _, _ => .element
  | .none, .identity, selfNone, _ => if selfNone then .identity else .element
  | .identity, .element, _, _ => .element
  | .identity, .identity, _, _ => .identity
  | .identity, .none, _, bNone => if bNone then .identity else .element
  | .element, _, _, _ => .element

/-- The `AlgebraicStatus` a `ValRes` induces. -/
def ofValRes {V : Type} : ValRes V → AlgStatus
  | .elem _ => .element
  | .identity _ _ => .identity
  | .none => .none

end AlgStatus

end PathMapModel
