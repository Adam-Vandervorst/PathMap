import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 0–29: `ByteMask`, `BitMask`, the rest of `utils/mod.rs`

Mirrors `differential/src/utilfuzz/mask.rs`.

## What a mask means

A `ByteMask` (and a `[u64; 4]` used as a `BitMask`) **is a set of bytes**.  The
model is `Basic.lean`'s `ByteMask`, the ascending duplicate-free list of
members, extended here (in the same namespace) with the set algebra.  Every op
below is stated on that set; the representation as four words appears only in
`words`/`ofWords`, which state the layout `from_range`'s doc fixes ("four `u64`
words in little-endian order: lower indices correspond to lower words and lower
bit positions").

Rendering: a mask is `{` + its members ascending, two hex digits each, + `}`;
raw words are `w0.w1.w2.w3` in lowercase hex.  The Rust side renders from the
raw words with its own arithmetic, so a rendering cannot share a crate bug.

## Ops

| op | name | crate items | operands | ret |
|---|---|---|---|---|
| 0 | `bm_from_iter` | `FromIterator<u8>` | `maskBytes` | the set of the bytes |
| 1 | `bm_from_u8` | `From<u8>`, `subset` | `b` | `{b}`, `{j \| j & b = j}` |
| 2 | `bm_from_range` | `from_range` at 9 `RangeBounds` shapes, `From<Range>`, `From<RangeInclusive>`, and both on an exhausted `a..=b` | `k%13 a b` | `{x \| lo ≤ x < hi}` |
| 3 | `bm_words` | `into_inner`, `From<ByteMask> for [u64;4]`, `AsRef`, `Borrow`, `From<[u64;4]>`, `==` (3 impls), `clone`, `Default` | mask, bool, [mask] | words ×4, mask, 4 equalities, default |
| 4 | `bm_count` | `count_bits`, `is_empty_mask` (both impls) | mask | `\|m\|`, `m = ∅` |
| 5 | `bm_test_bit` | `test_bit` (both) | mask, `k` | `k ∈ m` |
| 6–8 | `bm_set_bit` / `bm_clear_bit` / `bm_toggle_bit` | (both) | mask, `k` | `m ∪ {k}`, `m \ {k}`, `m △ {k}` |
| 9 | `bm_make_empty` | (both) | mask | `∅` |
| 10 | `bm_or` | `or` (both), `\|` owned and by ref, `\|=` | pair | `a ∪ b` ×5 |
| 11 | `bm_and` | `and` (both), `&` owned and by ref, `&=` | pair | `a ∩ b` ×5 |
| 12 | `bm_xor` | `xor` (both), `^`, `^=` | pair | `a △ b` ×4 |
| 13 | `bm_andn` | `andn` (both) | pair | `a \ b` ×2 |
| 14 | `bm_not` | `BitMask::not` (both), `!` | mask | complement ×3 |
| 15 | `bm_index_of` | `index_of` | mask, `b` | `\|{x ∈ m \| x < b}\|` |
| 16 | `bm_indexed_bit` | `indexed_bit::<true>`, `::<false>` | mask, `u8` (`i % 16` below 128, else `2(i-128)`) | `i`-th member ascending, descending |
| 17 | `bm_next_prev` | `next_bit`, `prev_bit` | mask, `b` | least member `> b`, greatest `< b` |
| 18 | `bm_iter` | `iter`, `ByteMaskIter::new`, `From` ×2, `byte_mask_iter` ×3 | mask, `k%7` | members ascending; then `None` again |
| 19 | `bm_range_iter` | `range_iter`, `ByteMaskRangeIter::new`, `From` ×2 | mask, `k%4` | maximal runs ascending; then `None` |
| 20 | `bm_incl_range` | `set_`/`clear_`/`toggle_inclusive_bit_range` | mask, `k%9 a b`: `m ∪ R`, `m \ R`, `m △ R` by `k % 3`; `R` by `k / 3`: `[min a b, max a b]`, `a..=b` as given (empty if `a > b`), `a..=b` exhausted by iteration (empty) | shape tag `o`/`g`/`x`, the mask |
| 21 | `bm_debug` | `Debug for ByteMask` (`{:?}`, `{:#?}`) | mask, bool | `f.debug_set()` of the members, decimal |
| 22 | `bm_binary` | `fmt_binary`, `Debug`/`Display for ByteMaskBinaryFmt` | mask | bits 255..0; again with a space every 8 |
| 23 | `bm_lattice` | `pjoin`, `pmeet`, `psubtract` on `ByteMask` and `[u64; 4]` | pair | `binResult` of `∪`, `∩`, `\` |
| 24 | `bm_join_into` | `Lattice::join_into` (default) on both | pair | status, new self ×2 |
| 25 | `bm_join_all` | `Lattice::join_all` (default) on both | list | `joinAllResult` ×2 |
| 26 | `bm_consts` | `EMPTY`, `FULL`, `new`, `Default`, `empty_mask`, `Debug` of both iterators | — | constants |
| 27 | `prefix_overlap` | `utils::find_prefix_overlap` (deprecated re-export) | two byte strings | longest common prefix length |
| 28 | `bm_program` | in-place edits in sequence | mask, steps | final set, its size |
| 29 | `nop` | | | |

Operand decoders: `maskOperand` (one mask, four shapes: listed bytes, unions of
ranges, complements, whole words) and `maskPair` (a second mask that is half
the time equal to, a superset of, a subset of the first, or empty, so the
`Identity` results come up).

## Semantic decisions

* **Lattice results** (`binResult`).  `AlgebraicResult`'s contract (`ring.rs`):
  `None` is an empty result and takes precedence over `Identity`; `Identity(mask)`
  sets bit 0 (`SELF_IDENT`) when the result is `self` and bit 1 (`COUNTER_IDENT`)
  when it is `other`, never bits beyond the arity, and two bits only if the
  operands are equal; `psubtract` never sets `COUNTER_IDENT`.  The contract
  lets an implementation report *fewer* identities than hold; the model asks
  for the strongest answer it allows (every identity that holds), which is what
  a bit set can always know.  `#guard`s below check `binResult` itself honours
  the contract (in particular `a \ b = b ≠ ∅` is impossible, so `psubtract`
  never names `other`).
* **`join_into`**: `self := self ∪ other`; status `None` when the union is
  empty, `Identity` when `self` did not change, `Element` otherwise
  (`AlgebraicStatus`'s doc).
* **`join_all`**: the n-ary `binResult` of `⋃ xs`: `None` for no arguments or
  an empty union (the precedence rule), else `Identity` with bit `i` for every
  `xs[i]` equal to the union, else `Element`.  With one or more arguments all
  empty the answer is `skip:join-all-empty` (see `skipJoinAllEmpty`).
* **Inclusive ranges** denote the set of bytes the `RangeInclusive` contains:
  `a..=b` with `a > b` is empty (std's `RangeInclusive::is_empty`, and what
  `from_range` documents for `start >= end`), and so is a range that has been
  iterated to its end (std: its `start()`/`end()` are then unspecified; its
  `RangeBounds` say empty).  Release builds are checked on `a > b`;
  `BlockRange::new` `debug_assert`s `start <= end`, so a debug build panics
  there (findings M3).  `bm_program` (op 28) only uses ordered ranges.
* **`Debug`** is `f.debug_set()` over the members (std's documented
  `{a, b}` / pretty `{\n    a,\n}` format), newlines rendered as `\n`.  The
  iterators' `Debug` prints `core::any::type_name`, whose text std does not
  promise; the model pins today's `pathmap::utils::ByteMaskIter`.
* **`fmt_binary`**: `Debug` is the 256 bits, bit 255 first; `Display` the same
  with a space after every 8th bit but the last (the crate's unit test pins the
  lengths 256 and 287).
-/

namespace PathMapModel

/-! ## The set algebra on `ByteMask` -/

namespace ByteMask

/-- Every byte, ascending. -/
def allBytes : List UInt8 := (List.range 256).map UInt8.ofNat

/-- Membership table, for linear-time set operations. -/
def bits (m : ByteMask) : Array Bool :=
  m.foldl (fun a b => a.set! b.toNat true) (Array.replicate 256 false)

/-- The set of bytes satisfying `p`, in canonical (ascending) form. -/
def filterAll (p : UInt8 → Bool) : ByteMask := allBytes.filter p

def mem (m : ByteMask) (b : UInt8) : Bool := m.contains b

def full : ByteMask := allBytes

def union (a b : ByteMask) : ByteMask :=
  let x := a.bits; let y := b.bits
  filterAll fun i => x[i.toNat]! || y[i.toNat]!

def inter (a b : ByteMask) : ByteMask :=
  let y := b.bits
  a.filter fun i => y[i.toNat]!

def diff (a b : ByteMask) : ByteMask :=
  let y := b.bits
  a.filter fun i => !y[i.toNat]!

def symm (a b : ByteMask) : ByteMask :=
  let x := a.bits; let y := b.bits
  filterAll fun i => x[i.toNat]! != y[i.toNat]!

def compl (a : ByteMask) : ByteMask :=
  let x := a.bits
  filterAll fun i => !x[i.toNat]!

/-- `{x | lo ≤ x < hi}` over the naturals (so `hi = 256` reaches 255). -/
def ofNatRange (lo hi : Nat) : ByteMask := filterAll fun x => lo ≤ x.toNat && x.toNat < hi

/-- The inclusive range `[a, b]` with its ends put in order. -/
def inclRange (a b : UInt8) : ByteMask :=
  ofNatRange (min a.toNat b.toNat) (max a.toNat b.toNat + 1)

/-- `{j | j & b = j}`: the bytes whose bits are a subset of `b`'s. -/
def subsetOf (b : UInt8) : ByteMask := filterAll fun j => (j &&& b) == j

/-- Word `i` of the documented layout: bit `x % 64` of word `x / 64`. -/
def word (m : ByteMask) (i : Nat) : Nat :=
  (m.filter (fun x => x.toNat / 64 == i)).foldl (fun acc x => acc + 2 ^ (x.toNat % 64)) 0

def words (m : ByteMask) : List Nat := [m.word 0, m.word 1, m.word 2, m.word 3]

/-- The set four words denote. -/
def ofWords (ws : List UInt64) : ByteMask :=
  filterAll fun x => ((ws.getD (x.toNat / 64) 0 >>> (UInt64.ofNat (x.toNat % 64))) &&& 1) == 1

/-- `index_of`: how many members precede `b`. -/
def indexOf (m : ByteMask) (b : UInt8) : Nat := (m.filter (· < b)).length

/-- `indexed_bit::<false>`: the `i`-th member counting down from the top. -/
def indexedBitRev (m : ByteMask) (i : Nat) : Option UInt8 := m.reverse[i]?

/-- The maximal runs of consecutive members, ascending. -/
def runs (m : ByteMask) : List (UInt8 × UInt8) :=
  (m.foldl (fun (acc : List (UInt8 × UInt8)) x =>
    match acc with
    | (lo, hi) :: rest => if hi.toNat + 1 == x.toNat then (lo, x) :: rest else (x, x) :: acc
    | [] => [(x, x)]) []).reverse

end ByteMask

namespace UtilFuzz

open Fuzz (Dec hexByte showByteOpt showBool)
open ByteMask

/-! ## Rendering -/

def showMask (m : ByteMask) : String := "{" ++ String.join (m.map hexByte) ++ "}"

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def showWords (m : ByteMask) : String := ".".intercalate (m.words.map hexNat)

/-- `Debug for ByteMask`: `f.debug_set()` over the members, decimal; the
alternate form one member per line, indented four, trailing comma. -/
def debugMask (m : ByteMask) (alt : Bool) : String :=
  let items := m.map (fun x => toString x.toNat)
  if alt then
    if items.isEmpty then "{}" else "{\\n" ++ String.join (items.map (fun s => "    " ++ s ++ ",\\n")) ++ "}"
  else "{" ++ ", ".intercalate items ++ "}"

/-- `ByteMaskBinaryFmt`: bit 255 first; `Display` puts a space after every 8th
bit except the last. -/
def binaryDebug (m : ByteMask) : String :=
  let x := m.bits
  String.ofList ((List.range 256).reverse.map fun i => if x[i]! then '1' else '0')

def binaryDisplay (m : ByteMask) : String :=
  let s := (binaryDebug m).toList
  " ".intercalate ((List.range 32).map fun k => String.ofList ((s.drop (8 * k)).take 8))

/-! ## The lattice results -/

/-- The strongest `AlgebraicResult` the contract allows for result `r` of a
binary operation on `a` (`self`) and `b` (`other`). -/
def binResult (r a b : ByteMask) : AlgResult ByteMask :=
  if r.isEmpty then .none
  else
    let mask := (if r == a then 1 else 0) + (if r == b then 2 else 0)
    if mask == 0 then .element r else .identity mask

/-- `join_into`: the status and the new `self`. -/
def joinInto (a b : ByteMask) : AlgStatus × ByteMask :=
  let u := union a b
  if u.isEmpty then (.none, a) else if u == a then (.identity, a) else (.element, u)

/-- `join_all`: the n-ary `binResult` of the union. -/
def joinAllResult (xs : List ByteMask) : AlgResult ByteMask :=
  let u := xs.foldl union []
  if u.isEmpty then .none
  else
    let mask := (xs.zipIdx.filter (fun (x, _) => x == u)).foldl (fun acc (_, i) => acc + 2 ^ i) 0
    if mask == 0 then .element u else .identity mask

/-- Op 25 when every `join_all` operand is empty (and there is at least one).
The contract (`ring.rs`, `AlgebraicResult`) allows `None` ("should take
precedence") or an `Identity` naming any of the equal, empty arguments; the
model's `joinAllResult` says `None`, but the crate answers by the parity of the
argument count (`[∅]` → `Identity(1)`, `[∅, ∅]` → `None`, `[∅, ∅, ∅]` →
`Identity(4)`; `lean/findings/u-mask.md`, M1).  The harness renders the skip
token for either allowed answer and the real answer otherwise, so a disallowed
`Element` or out-of-range bit still diverges. -/
def skipJoinAllEmpty : String := "skip:join-all-empty"

/-! ## Operand decoders -/

def decBytes (d : Dec) : Nat → Option (List UInt8 × Dec)
  | 0 => some ([], d)
  | k + 1 => do
      let (b, d) ← d.u8
      let (rest, d) ← decBytes d k
      some (b :: rest, d)

def decRanges (d : Dec) : Nat → Option (ByteMask × Dec)
  | 0 => some ([], d)
  | k + 1 => do
      let (a, d) ← d.u8
      let (b, d) ← d.u8
      let (rest, d) ← decRanges d k
      some (union (inclRange a b) rest, d)

def decWords (d : Dec) : Nat → Option (List UInt64 × Dec)
  | 0 => some ([], d)
  | k + 1 => do
      let (s, d) ← d.mod 4
      let (w, d) ← match s with
        | 0 => some ((0 : UInt64), d)
        | 1 => some (~~~(0 : UInt64), d)
        | 2 => d.u8.map fun (b, d) => (b.toUInt64 * 0x0101010101010101, d)
        | _ => d.u8.map fun (b, d) => (~~~(0 : UInt64) <<< (b.toUInt64 % 64), d)
      let (rest, d) ← decWords d k
      some (w :: rest, d)

/-- A mask operand; see `dec_mask` in `mask.rs`. -/
def maskOperand (d : Dec) : Option (ByteMask × Dec) := do
  let (k, d) ← d.mod 4
  match k with
  | 0 => let (bs, d) ← maskBytes d; some (ByteMask.ofList bs, d)
  | 1 => let (n, d) ← d.mod 4; decRanges d n
  | 2 => let (bs, d) ← maskBytes d; some (compl (ByteMask.ofList bs), d)
  | _ => let (ws, d) ← decWords d 4; some (ofWords ws, d)

/-- Two related masks; see `dec_pair` in `mask.rs`. -/
def maskPair (d : Dec) : Option ((ByteMask × ByteMask) × Dec) := do
  let (a, d) ← maskOperand d
  let (s, d) ← d.mod 5
  match s with
  | 0 => some ((a, a), d)
  | 1 => let (c, d) ← maskOperand d; some ((a, c), d)
  | 2 => let (c, d) ← maskOperand d; some ((a, union a c), d)
  | 3 => let (c, d) ← maskOperand d; some ((a, inter a c), d)
  | _ => some ((a, []), d)

/-- `join_all`'s operand list; see op 25 in `mask.rs`. -/
def decJoinList (d : Dec) : Nat → ByteMask → Option (List ByteMask × Dec)
  | 0, _ => some ([], d)
  | k + 1, prev => do
      let (s, d) ← d.mod 5
      let (x, d) ← match s with
        | 0 => some (prev, d)
        | 1 => maskOperand d
        | 2 => (maskOperand d).map fun (c, d) => (union prev c, d)
        | 3 => some ([], d)
        | _ => (maskOperand d).map fun (c, d) => (inter prev c, d)
      let (rest, d) ← decJoinList d k x
      some (x :: rest, d)

/-- One `bm_program` step. -/
def progStep (m : ByteMask) (d : Dec) : Option (ByteMask × Dec) := do
  let (t, d) ← d.mod 10
  match t with
  | 0 => let (k, d) ← d.u8; some (union m [k], d)
  | 1 => let (k, d) ← d.u8; some (diff m [k], d)
  | 2 => let (k, d) ← d.u8; some (symm m [k], d)
  | 3 | 4 | 5 =>
      let (a, d) ← d.u8
      let (b, d) ← d.u8
      let r := inclRange a b
      some (if t == 3 then union m r else if t == 4 then diff m r else symm m r, d)
  | 6 => let (c, d) ← maskOperand d; some (union m c, d)
  | 7 => let (c, d) ← maskOperand d; some (inter m c, d)
  | 8 => let (c, d) ← maskOperand d; some (symm m c, d)
  | _ => some (compl m, d)

def progRun (m : ByteMask) (d : Dec) : Nat → Option (ByteMask × Dec)
  | 0 => some (m, d)
  | k + 1 => do let (m, d) ← progStep m d; progRun m d k

/-- Longest common prefix length. -/
def prefixOverlap : List UInt8 → List UInt8 → Nat
  | a :: as, b :: bs => if a == b then 1 + prefixOverlap as bs else 0
  | _, _ => 0

/-- `from_range`'s half-open `[lo, hi)` (naturals) for each operand shape. -/
def fromRangeBounds (k : Nat) (a b : UInt8) : Nat × Nat :=
  let a := a.toNat; let b := b.toNat
  match k with
  | 0 => (a, b)           -- a..b
  | 1 => (a, b + 1)       -- a..=b
  | 2 => (a, 256)         -- a..
  | 3 => (0, b)           -- ..b
  | 4 => (0, b + 1)       -- ..=b
  | 5 => (0, 256)         -- ..
  | 6 => (a + 1, b + 1)   -- (Excluded a, Included b)
  | 7 => (a + 1, b)       -- (Excluded a, Excluded b)
  | 8 => (a + 1, 256)     -- (Excluded a, Unbounded)
  | 9 => (a, b)           -- From<Range<u8>>
  | 10 => (a, b + 1)      -- From<RangeInclusive<u8>>
  | _ => (0, 0)           -- 11, 12: from_range / From of `a..=b` iterated to its end

def showIter (m : ByteMask) : String := ",".intercalate (m.map hexByte) ++ ";-"

def showRuns (m : ByteMask) : String :=
  ",".intercalate (m.runs.map fun (lo, hi) => hexByte lo ++ "-" ++ hexByte hi) ++ ";-"

def showRes (r : AlgResult ByteMask) : String := showAlgResult showMask r

/-! ## The step function -/

def stepMask (op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  match op with
  | 0 => do
      let (bs, d) ← maskBytes d
      some (("bm_from_iter", showMask (ByteMask.ofList bs)), d)
  | 1 => do
      let (b, d) ← d.u8
      some (("bm_from_u8", showMask [b] ++ " " ++ showMask (subsetOf b)), d)
  | 2 => do
      let (k, d) ← d.mod 13
      let (a, d) ← d.u8
      let (b, d) ← d.u8
      let (lo, hi) := fromRangeBounds k a b
      some (("bm_from_range", showMask (ofNatRange lo hi)), d)
  | 3 => do
      let (a, d) ← maskOperand d
      let (same, d) ← d.bool
      let (b, d) ← if same then some (a, d) else maskOperand d
      let w := showWords a
      let e := showBool (a == b)
      some (("bm_words", s!"{w} {w} {w} {w} {showMask b} eq={e}{e}{e}1 d=\{}"), d)
  | 4 => do
      let (m, d) ← maskOperand d
      let c := toString m.length
      let e := showBool m.isEmpty
      some (("bm_count", s!"{c} {e} {c} {e}"), d)
  | 5 => do
      let (m, d) ← maskOperand d
      let (k, d) ← d.u8
      let t := showBool (m.mem k)
      some (("bm_test_bit", t ++ t), d)
  | 6 | 7 | 8 => do
      let (m, d) ← maskOperand d
      let (k, d) ← d.u8
      let (name, r) :=
        if op == 6 then ("bm_set_bit", union m [k])
        else if op == 7 then ("bm_clear_bit", diff m [k])
        else ("bm_toggle_bit", symm m [k])
      some ((name, showMask r ++ " " ++ showMask r), d)
  | 9 => do
      let (_, d) ← maskOperand d
      some (("bm_make_empty", "{} {}"), d)
  | 10 => do
      let ((a, b), d) ← maskPair d
      let r := showMask (union a b)
      some (("bm_or", " ".intercalate [r, r, r, r, r]), d)
  | 11 => do
      let ((a, b), d) ← maskPair d
      let r := showMask (inter a b)
      some (("bm_and", " ".intercalate [r, r, r, r, r]), d)
  | 12 => do
      let ((a, b), d) ← maskPair d
      let r := showMask (symm a b)
      some (("bm_xor", " ".intercalate [r, r, r, r]), d)
  | 13 => do
      let ((a, b), d) ← maskPair d
      let r := showMask (diff a b)
      some (("bm_andn", r ++ " " ++ r), d)
  | 14 => do
      let (m, d) ← maskOperand d
      let r := showMask (compl m)
      some (("bm_not", " ".intercalate [r, r, r]), d)
  | 15 => do
      let (m, d) ← maskOperand d
      let (b, d) ← d.u8
      some (("bm_index_of", toString (m.indexOf b)), d)
  | 16 => do
      let (m, d) ← maskOperand d
      let (i, d) ← d.u8
      let i := if i.toNat < 128 then i.toNat % 16 else 2 * (i.toNat - 128)
      some (("bm_indexed_bit", showByteOpt (m.indexedBit i) ++ " " ++ showByteOpt (m.indexedBitRev i)), d)
  | 17 => do
      let (m, d) ← maskOperand d
      let (b, d) ← d.u8
      some (("bm_next_prev", showByteOpt (m.nextBit b) ++ " " ++ showByteOpt (m.prevBit b)), d)
  | 18 => do
      let (m, d) ← maskOperand d
      let (_, d) ← d.mod 7
      some (("bm_iter", showIter m), d)
  | 19 => do
      let (m, d) ← maskOperand d
      let (_, d) ← d.mod 4
      some (("bm_range_iter", showRuns m), d)
  | 20 => do
      let (m, d) ← maskOperand d
      let (k, d) ← d.mod 9
      let (a, d) ← d.u8
      let (b, d) ← d.u8
      let r := match k / 3 with
        | 0 => inclRange a b
        | 1 => ofNatRange a.toNat (b.toNat + 1)
        | _ => []
      let m' := if k % 3 == 0 then union m r else if k % 3 == 1 then diff m r else symm m r
      let tag := if k / 3 == 0 then "o" else if k / 3 == 1 then "g" else "x"
      some (("bm_incl_range", tag ++ " " ++ showMask m'), d)
  | 21 => do
      let (m, d) ← maskOperand d
      let (alt, d) ← d.bool
      some (("bm_debug", debugMask m alt), d)
  | 22 => do
      let (m, d) ← maskOperand d
      some (("bm_binary", binaryDebug m ++ "|" ++ binaryDisplay m), d)
  | 23 => do
      let ((a, b), d) ← maskPair d
      let j := showRes (binResult (union a b) a b)
      let m := showRes (binResult (inter a b) a b)
      let s := showRes (binResult (diff a b) a b)
      some (("bm_lattice", s!"j={j} m={m} s={s} J={j} M={m} S={s}"), d)
  | 24 => do
      let ((a, b), d) ← maskPair d
      let (st, r) := joinInto a b
      some (("bm_join_into", s!"{st} {showMask r} {st} {showMask r}"), d)
  | 25 => do
      let (n, d) ← d.mod 5
      let (xs, d) ← decJoinList d n []
      let r := if !xs.isEmpty && xs.all List.isEmpty then skipJoinAllEmpty else showRes (joinAllResult xs)
      some (("bm_join_all", r ++ " " ++ r), d)
  | 26 =>
      some (("bm_consts", s!"E=\{} F={showMask full} n=\{} d=\{} e=0.0.0.0 " ++
        "i=pathmap::utils::ByteMaskIter r=pathmap::utils::ByteMaskRangeIter"), d)
  | 27 => do
      let (la, d) ← d.mod 72
      let (a, d) ← d.pathN la
      let (k, d) ← d.mod (la + 1)
      let (lt, d) ← d.mod 40
      let (t, d) ← d.pathN lt
      some (("prefix_overlap", toString (prefixOverlap a (a.take k ++ t))), d)
  | 28 => do
      let (m, d) ← maskOperand d
      let (n, d) ← d.mod 8
      let (m, d) ← progRun m d n
      some (("bm_program", showMask m ++ " " ++ toString m.length), d)
  | _ => some (("nop", "-"), d)

/-! ## Fixtures

Laws the set reading promises, on a battery of masks that hit word
boundaries, plus the crate's own unit-test expectations. -/

def samples : List ByteMask :=
  [[], full, [0], [255], [63, 64], [0, 64, 128, 192], ofNatRange 10 70, ofNatRange 62 131,
   ByteMask.ofList [0, 2, 63, 64, 130, 255], compl [7, 200], ofNatRange 192 256, subsetOf 0xa6]

-- The model's canonical form is preserved by every operation.
#guard samples.all fun a => samples.all fun b =>
  [union a b, inter a b, diff a b, symm a b, compl a].all fun r => r == ByteMask.ofList r

-- Boolean-algebra laws.
#guard samples.all fun a => samples.all fun b =>
  union a b == union b a && inter a b == inter b a && symm a b == symm b a &&
  union a (inter a b) == a && inter a (union a b) == a &&
  compl (union a b) == inter (compl a) (compl b) &&
  diff a b == inter a (compl b) && symm a b == union (diff a b) (diff b a) &&
  compl (compl a) == a
#guard samples.all fun a => samples.all fun b => samples.all fun c =>
  inter a (union b c) == union (inter a b) (inter a c) &&
  union a (union b c) == union (union a b) c

-- Words round-trip, and `ofWords` reads the documented layout.
#guard samples.all fun m => ofWords (m.words.map UInt64.ofNat) == m
#guard (ByteMask.ofList [0, 64, 255]).words == [1, 1, 0, 2 ^ 63]
#guard (ofNatRange 10 70).words == [0xfffffffffffffc00, 0x3f, 0, 0]

-- Queries agree with each other.
#guard samples.all fun m => (allBytes.all fun b =>
  m.indexOf b == (m.filter (· < b)).length &&
  (if m.mem b then m.indexedBit (m.indexOf b) == some b else true) &&
  m.nextBit b == (allBytes.filter (fun x => b < x && m.mem x)).head? &&
  m.prevBit b == (allBytes.filter (fun x => x < b && m.mem x)).getLast?)
#guard samples.all fun m => (List.range 257).all fun i =>
  m.indexedBitRev i == (if i < m.length then m.indexedBit (m.length - 1 - i) else none)
#guard samples.all fun m =>
  (m.runs.foldl (fun acc (lo, hi) => union acc (inclRange lo hi)) []) == m &&
  (m.runs.zip m.runs.tail).all fun ((_, hi), (lo, _)) => hi.toNat + 1 < lo.toNat

-- `subset` is the n-th row of the Sierpinski triangle (crate unit test).
#guard allBytes.all fun x => (subsetOf 0xa6).mem x == ((x &&& 0xa6) == x)

-- `from_range` (crate unit test).
#guard ofNatRange 0 0 == [] && ofNatRange 255 255 == [] && ofNatRange 255 256 == [255]
#guard (fromRangeBounds 8 255 0).1 == 256 && ofNatRange 256 256 == []

-- Formatting (crate unit test: `{0, 64, 255}`, lengths 256 and 287).
#guard debugMask (ByteMask.ofList [0, 64, 255]) false == "{0, 64, 255}"
#guard (binaryDebug (ByteMask.ofList [0, 64, 255])).length == 256
#guard (binaryDisplay (ByteMask.ofList [0, 64, 255])).length == 287
#guard (binaryDebug [0]).back == '1' && (binaryDebug [255]).front == '1'

-- `binResult` honours `AlgebraicResult`'s contract: a non-zero mask within the
-- arity, two bits only for equal operands, `psubtract` never `COUNTER_IDENT`,
-- `None` exactly for an empty result.
def contractOk (r a b : ByteMask) (commutative : Bool) : Bool :=
  match binResult r a b with
  | .none => r.isEmpty
  | .element v => v == r && !r.isEmpty
  | .identity m => 0 < m && m ≤ 3 && (m != 3 || a == b) && (commutative || m == 1) &&
      (m % 2 == 0 || r == a) && (m < 2 || r == b)
#guard samples.all fun a => samples.all fun b =>
  contractOk (union a b) a b true && contractOk (inter a b) a b true && contractOk (diff a b) a b false

-- Idempotence as `Lattice::IDEMPOTENT` promises it: `pjoin(x, x)` and
-- `pmeet(x, x)` are `Identity(SELF_IDENT | COUNTER_IDENT)`, `psubtract(x, x)` is
-- `None` (for a non-empty `x`; an empty one gives `None` by precedence).
#guard samples.all fun a => a.isEmpty ||
  (binResult (union a a) a a == .identity 3 && binResult (inter a a) a a == .identity 3 &&
   binResult (diff a a) a a == .none)

-- Crate unit test `byte_mask_lattice_operations`.
#guard binResult (union [1, 2] [2, 3]) [1, 2] [2, 3] == .element [1, 2, 3]
#guard binResult (inter [1, 2] [2, 3]) [1, 2] [2, 3] == .element [2]
#guard binResult (diff [1, 2] [2, 3]) [1, 2] [2, 3] == .element [1]

-- `join_into` is `pjoin` applied in place (`in_place_default_impl`).
#guard samples.all fun a => samples.all fun b =>
  let (st, r) := joinInto a b
  r == union a b && match binResult (union a b) a b with
    | .none => st == .none
    | .element _ => st == .element
    | .identity m => st == (if m % 2 == 1 then .identity else .element)

-- `join_all` of two agrees with `pjoin`.
#guard samples.all fun a => samples.all fun b =>
  joinAllResult [a, b] == binResult (union a b) a b

end UtilFuzz
end PathMapModel
