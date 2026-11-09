import PathMapModel.UtilFuzz.Base

/-!
# Util fuzzer, ops 60–79: `utils/ints.rs` (`PathInteger`)

`PathInteger<N>` is a marker trait on the unsigned integer types that may be
encoded into paths: `u8`, `u16`, `u32`, `u64`, `usize` (64-bit targets) and
`u128`, with `N` the byte width.  Everything below is a statement about natural
numbers below `2^(8N)`; every op is instantiated for all six types.

## The encodings

* **Bits of Byte** (`indices_to_bob` / `bob_to_indices`): up to 8 integers are
  transposed bitwise.  With `steps` the largest bit length among them, byte `j`
  of the encoding (`j < steps`) holds, in bit `i`, bit `steps-1-j` of integer
  `i`.  Most significant bit first, no padding to the type's width ("does not
  pad to number bit length").  (The doc comment's example lists the bytes in
  the opposite order; see the fixtures below.)  The encoder *appends* to the caller's vector and
  returns `steps`.  The decoder reads any byte string of length at most `8N`
  (it asserts that) into zeroed integers: integer `k` is the number whose
  binary digits, most significant first, are bit `k` of each byte.
  `#guard`: `unbob (bob xs) = xs`.
* **Weave** (`indices_to_weave` / `weave_to_indices`): integers interleaved
  byte by byte, big-endian, round robin: for byte position `c` from `N-1` down
  to `0`, byte `c` of each integer in turn.  The encoder takes `usize`s (the
  `R` type only fixes `N`), so each integer is reduced to its low `N` bytes,
  and for `N = 16` its upper 8 bytes are zero.  The decoder splits a string of
  length `n * steps` into `steps` rounds of `n` bytes and reads each column
  big-endian.  `#guard`: `unweave (weave xs) = xs mod 2^(8N)`.

  **Semantic decision (open question W1 in `lean/findings/u-ints.md`).**  The
  doc comment says the weave "does not pad to number byte length", and the
  `bob_and_weave_simple` test comments print unpadded weaves; the code always
  writes exactly `N` bytes per integer (the unpadded `steps` computation is
  commented out above it).  The model follows the code: fixed width is a
  deliberate change (the commented-out line), it is what makes the weaves of
  equal-arity tuples equal-length and so prefix-free as trie paths, and the
  decoder accepts both.  The stale doc comment is reported, not fuzzed.

## The range generator

`gen_int_range(start, stop, step, v)` (and `gen_int_range_in` with an
allocator) is the map holding `v` at the `N`-byte big-endian encoding of every
`start + k*step < stop`, and nothing else: no other values and no dangling
paths.  `step` must be positive (0 hangs `u8` and divides by zero otherwise;
the fuzzer never generates it).  `start >= stop` is the empty map.

`gen_value_level_in` and `get_from_cache` are private and `gen_child_level_in`
is `pub(crate)`: they are reached only through `gen_int_range`.

See `differential/src/utilfuzz/ints.rs` for the op table and operand formats.
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec hexPath)

namespace Ints

/-- The six `PathInteger` impls (type index order) and their widths `N`. -/
def types : List (String × Nat) :=
  [("u8", 1), ("u16", 2), ("u32", 4), ("u64", 8), ("usize", 8), ("u128", 16)]

def tyName (t : Nat) : String := (types.getD t ("u128", 16)).1
def width (t : Nat) : Nat := (types.getD t ("u128", 16)).2

/-- The largest value of an `N`-byte type. -/
def maxOf (n : Nat) : Nat := 2 ^ (8 * n) - 1

/-! ### Semantics -/

/-- Bit `c` of `x`. -/
def bit (x c : Nat) : Nat := x / 2 ^ c % 2

/-- Byte `c` of `x` (byte 0 least significant). -/
def byte (x c : Nat) : Nat := x / 256 ^ c % 256

/-- The number of binary digits of `x` (0 for 0). -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `Σ i, f xs[i] i` -/
def sumIdx (xs : List Nat) (f : Nat → Nat → Nat) : Nat :=
  (xs.foldl (fun (acc, i) x => (acc + f x i, i + 1)) (0, 0)).1

/-- Bits of Byte: byte `j` holds bit `steps-1-j` of integer `i` in bit `i`. -/
def bob (xs : List Nat) : List UInt8 :=
  let steps := xs.foldl (fun m x => max m (bitLen x)) 0
  (List.range steps).reverse.map fun c => UInt8.ofNat (sumIdx xs fun x i => bit x c * 2 ^ i)

/-- The `bob` decoder into `cnt` integers: integer `k` reads bit `k` of each
byte, most significant first. -/
def unbob (bs : List UInt8) (cnt : Nat) : List Nat :=
  (List.range cnt).map fun k => bs.foldl (fun acc b => acc * 2 + bit b.toNat k) 0

/-- Weave: byte positions `N-1` down to `0`, each integer in turn. -/
def weave (n : Nat) (xs : List Nat) : List UInt8 :=
  (List.range n).reverse.flatMap fun c => xs.map fun x => UInt8.ofNat (byte x c)

/-- The weave decoder into `cnt ≥ 1` integers: column `i` of the
`(len / cnt) × cnt` byte matrix, read big-endian. -/
def unweave (bs : List UInt8) (cnt : Nat) : List Nat :=
  let steps := bs.length / cnt
  (List.range cnt).map fun i =>
    (List.range steps).foldl (fun acc c => acc * 256 + (bs.getD (cnt * c + i) 0).toNat) 0

/-- The `N`-byte big-endian encoding of `x`. -/
def be (n x : Nat) : List UInt8 := (List.range n).reverse.map fun c => UInt8.ofNat (byte x c)

/-- The number of elements of `start..stop` by `step ≥ 1`. -/
def rangeCount (start stop step : Nat) : Nat :=
  if start < stop then (stop - start - 1) / step + 1 else 0

/-- The integers `gen_int_range(start, stop, step, _)` holds, ascending. -/
def rangeElems (start stop step : Nat) : List Nat :=
  (List.range (rangeCount start stop step)).map fun k => start + k * step

def inRange (start stop step q : Nat) : Bool :=
  start ≤ q && q < stop && (q - start) % step == 0

/-- Non-root locations of a trie holding exactly the `N`-byte encodings of
`xs`: its distinct non-empty prefixes. -/
def locations (n : Nat) (xs : List Nat) : Nat :=
  ((List.range n).map fun l => (xs.map fun x => x / 256 ^ (n - (l + 1))).eraseDups.length).foldl (· + ·) 0

/-! ### Laws -/

-- The doc comment's and `bob_and_weave_simple`'s printed examples, **reversed**:
-- they list the bytes least significant bit first, but the encoder emits the
-- most significant first (`for c in (0..steps).rev()`), and only that order is
-- inverted by the documented decoder `bob_to_indices` (`<< (len - 1 - i)`).
-- Stale examples, finding W1 in `lean/findings/u-ints.md`.
#guard bob [10, 30, 100] == [0b0, 0b11, 0b110, 0b11, 0b10, 0b100, 0b100].reverse
#guard bob [3333, 30, 1000] ==
  [0b1, 0b10, 0b11, 0b110, 0b10, 0b100, 0b100, 0b100, 0b101, 0b100, 0b1, 0b1].reverse
#guard bob [] == [] && bob [0, 0] == []
#guard (List.range 40).all fun s =>
  let xs := [s * 7919 % 1000, s * 31, s % 3, s * s]
  unbob (bob xs) xs.length == xs
#guard weave 2 [3333, 30, 1000] == [13, 0, 3, 5, 30, 232]
#guard weave 16 [1] == List.replicate 15 0 ++ [1]
#guard (List.range 40).all fun s =>
  let xs := [s * 7919 % 100000, s * 31, s % 3, s * s * s * s * s]
  [1, 2, 4, 8, 16].all fun n => unweave (weave n xs) xs.length == xs.map (· % 2 ^ (8 * n))
#guard rangeElems 2 16 3 == [2, 5, 8, 11, 14]
#guard rangeElems 175 750 25 == (List.range 23).map (175 + 25 * ·)
#guard rangeElems 5 5 1 == [] && rangeElems 6 5 1 == []
#guard locations 2 [0x0102, 0x0103, 0x0201] == 2 + 3

/-! ### Decoding -/

/-- `int(N)`: `k := u8 % (N + 1)`, then `k` big-endian bytes. -/
def intN (d : Dec) (n : Nat) : Option (Nat × Dec) := do
  let (k, d) ← d.mod (n + 1)
  go k 0 d
where
  go : Nat → Nat → Dec → Option (Nat × Dec)
    | 0, x, d => some (x, d)
    | k + 1, x, d => do let (b, d) ← d.u8; go k (x * 256 + b.toNat) d

/-- `cnt` operands read with `rd`. -/
def many (rd : Dec → Option (α × Dec)) : Nat → Dec → Option (List α × Dec)
  | 0, d => some ([], d)
  | k + 1, d => do
      let (x, d) ← rd d
      let (rest, d) ← many rd k d
      some (x :: rest, d)

def rawBytes (n : Nat) (d : Dec) : Option (List UInt8 × Dec) := many Dec.u8 n d

def showInts (xs : List Nat) : String := "[" ++ ",".intercalate (xs.map toString) ++ "]"

def bobOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let (pre, d) ← d.path 3
  let (cnt, d) ← d.mod 9
  let (xs, d) ← many (intN · n) cnt d
  let enc := bob xs
  some (toString enc.length ++ ";" ++ hexPath (pre ++ enc) ++ ";" ++ showInts (unbob enc cnt), d)

def weaveOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let (pre, d) ← d.path 3
  let (cnt, d) ← d.mod 9
  let (xs, d) ← many (intN · 8) cnt d
  let enc := weave n xs
  let back := if cnt == 0 then [] else unweave enc cnt
  if n == 16 then
    -- `skip:weave-u128-shift`: the crate's upper 8 byte positions are garbage
    -- (finding `weave_u128_shift_overflow`); only the lower 8 (= `weave 8`)
    -- are compared, so one `weave_u128` does not end the input's comparison.
    some (hexPath pre ++ "|" ++ hexPath (weave 8 xs) ++ ";skip:weave-u128-shift", d)
  else
    some (hexPath (pre ++ enc) ++ ";" ++ showInts back, d)

def unbobOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let (cnt, d) ← d.mod 9
  let (len, d) ← d.mod (8 * n + 1)
  let (bs, d) ← rawBytes len d
  some (showInts (unbob bs cnt), d)

def unweaveOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let (c, d) ← d.mod 8
  let cnt := c + 1
  let (steps, d) ← d.mod (n + 1)
  let (bs, d) ← rawBytes (cnt * steps) d
  some (showInts (unweave bs cnt), d)

def showEntry (n v x : Nat) : String := hexPath (be n x) ++ ":" ++ toString v

def rangeOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let mx := maxOf n
  let (start, d) ← intN d n
  let (st, d) ← intN d n
  let step := max st 1
  let (k, d) ← d.mod 40
  let (r, d) ← d.u8
  let stop := min (start + k * step + r.toNat % step) mx
  let (e, d) ← d.u8
  let stop := if e.toNat % 8 == 0 then start - (e.toNat / 8 % 3) else stop
  let (_alloc, d) ← d.bool
  let (v, d) ← d.u8
  let xs := rangeElems start stop step
  let body := ",".intercalate (xs.map (showEntry n v.toNat))
  some ("[" ++ body ++ "];n=" ++ toString (locations n xs), d)

def rangeBigOp (n : Nat) (d : Dec) : Option (String × Dec) := do
  let mx := maxOf n
  let (start, d) ← intN d n
  let (mode, d) ← d.mod 2
  let (step, cnt, d) ← if mode == 0 then do
      let (b, d) ← d.mod (8 * n)
      let (cnt, d) ← intN d n
      pure (2 ^ b, cnt, d)
    else do
      let (st, d) ← intN d n
      let (cnt, d) ← intN d 2
      pure (max st 1, cnt % 4097, d)
  let (r, d) ← intN d n
  let stop := min (start + cnt * step + r % step) mx
  let (v, d) ← d.u8
  let count := rangeCount start stop step
  let probe (d : Dec) : Option (Nat × Dec) := do
    let (m, d) ← intN d n
    -- `count.saturating_add(2)` in u128.
    let q := start + m % (min (count + 2) (2 ^ 128 - 1)) * step
    let (δ, d) ← d.mod 3
    pure (if δ == 0 then q else if δ == 1 then q + 1 else q - 1, d)
  let (probes, d) ← many probe 3 d
  let c := if count < 2 ^ 63 then toString count else "-"
  let first := (List.range (min 4 count)).map fun k => showEntry n v.toNat (start + k * step)
  let last := if count > 0 then start + (count - 1) * step else start
  let qs := [start, start + step, last, last + step, stop - 1, stop] ++ probes
  let hits := qs.map fun q =>
    if inRange start stop step (min q mx) then toString v.toNat else "-"
  some ("c=" ++ c ++ ";f=[" ++ ",".intercalate first ++ "];p=" ++ ",".intercalate hits, d)

end Ints

open Ints in
def stepInts (op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  if op < 66 then do
    let t := op - 60
    let (r, d) ← bobOp (width t) d
    some (("bob_" ++ tyName t, r), d)
  else if op < 72 then do
    let t := op - 66
    let (r, d) ← weaveOp (width t) d
    some (("weave_" ++ tyName t, r), d)
  else if op < 78 then do
    let t := op - 72
    let (w, d) ← d.bool
    if w then do
      let (r, d) ← unweaveOp (width t) d
      some (("unweave_" ++ tyName t, r), d)
    else do
      let (r, d) ← unbobOp (width t) d
      some (("unbob_" ++ tyName t, r), d)
  else if op == 78 then do
    let (t, d) ← d.mod 6
    let (r, d) ← rangeOp (width t) d
    some (("range_" ++ tyName t, r), d)
  else do
    let (t, d) ← d.mod 6
    let (r, d) ← rangeBigOp (width t) d
    some (("range_big_" ++ tyName t, r), d)

end UtilFuzz
end PathMapModel
