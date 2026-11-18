import PathMapModel.PathMap

/-!
# The logical trie hash

`pathmap` hashes a trie (`CatamorphismCached::hash`, and the identity of subtries in
`PathMap::merkleize`) as a Merkle tree over the **logical** trie: the byte-radix tree of its
paths, with no notion of the nodes the crate stores it in.  For a position `p`:

* `below p` hashes the child mask of `p` and, in ascending byte order, the hash of every child
  `p ++ [b]`.  A byte inside a non-branching run is a mask with one bit; an endpoint with no
  children has the empty mask, whose hash is `leaf`.
* `hash p` is `below p` with the value at `p` layered on top, if `p` holds one.

This file is that definition over the model's `PathMap`, which knows nothing about node
layout, so any dependence of the crate's hash on layout shows up as a divergence in the
differential harness (`Fuzz.lean`, ops `hash`, `hash_iter`, `map_hash`, `merkleize`).

The crate's production primitive is gxhash, which is not worth transcribing.  The harness
instead runs the crate with `pathmap::morphisms::trie_hash::Fnv1a64Scheme`, whose primitives
are the few lines of FNV-1a below.  Every constant here mirrors that scheme:

* `value v`               = FNV-1a over the 8 little-endian bytes of `v : UInt64`
* `node mask children`    = FNV-1a over `'N'`, the 32-byte little-endian bitmap of `mask`, then
                            8 little-endian bytes of each child hash
* `withValue vh below`    = FNV-1a over `'V'`, 8 bytes of `below`, then 8 bytes of `vh`

`HashSecurity.lean` proves that this layering is sound for any primitive: two logically
different tries that hash alike exhibit a collision of the primitive.
-/

namespace PathMapModel
namespace Hash

/-! ## FNV-1a -/

def fnvOffset : UInt64 := 0xcbf29ce484222325
def fnvPrime : UInt64 := 0x100000001b3

/-- Absorb one byte. -/
def absorb (h : UInt64) (b : UInt8) : UInt64 := (h ^^^ b.toUInt64) * fnvPrime

/-- Absorb a byte string. -/
def absorbBytes (h : UInt64) (bs : List UInt8) : UInt64 := bs.foldl absorb h

/-- The 8 bytes of a `UInt64`, least significant first. -/
def leBytes64 (x : UInt64) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
   (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]

/-- A byte from its bits, least significant first: `digits [b0, b1, ..] = b0 + 2 * (b1 + 2 * ..)`. -/
def digits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * digits bs

/-- The 32-byte little-endian bitmap of a child mask: byte `i` holds bits `8i .. 8i+7`, so byte
`b` of the mask sets bit `b % 8` of byte `b / 8`.  This is the in-memory layout of
`pathmap::utils::ByteMask` (`[u64; 4]`) on a little-endian machine, which is what the crate
absorbs.  Written through `digits` so that `HashSecurity.lean` can show it is injective. -/
def maskBytes (m : ByteMask) : List UInt8 :=
  (List.range 32).map fun i =>
    UInt8.ofNat (digits ((List.range 8).map fun j => m.contains (UInt8.ofNat (8 * i + j))))

/-! ## The scheme (`Fnv1a64Scheme`) -/

/-- The primitive: FNV-1a over a whole message. -/
def fnv (msg : List UInt8) : UInt64 := absorbBytes fnvOffset msg

/-- `HashScheme::value` for `u64`: what `<u64 as Hash>::hash` writes, little-endian. -/
def value (v : UInt64) : UInt64 := fnv (leBytes64 v)

/-- `HashScheme::start`, `child`, `finish` in one: a logical node with the given children, in
the order given (callers pass them in ascending byte order). -/
def node (m : ByteMask) (children : List UInt64) : UInt64 :=
  children.foldl (fun h c => absorbBytes h (leBytes64 c))
    (absorbBytes (absorb fnvOffset 0x4E) (maskBytes m))

/-- `HashScheme::with_value`. -/
def withValue (vh below : UInt64) : UInt64 :=
  absorbBytes (absorbBytes (absorb fnvOffset 0x56) (leBytes64 below)) (leBytes64 vh)

/-- `HashScheme::leaf`: a position with no children and no value. -/
def leaf : UInt64 := node [] []

/-- `HashScheme::step`: one byte of a non-branching run above `below`. -/
def step (b : UInt8) (below : UInt64) : UInt64 := node [b] [below]

/-! ## The hash of a logical trie -/

/-- The hash of the subtrie at `p`, given `fuel` at least the depth of the trie below `p`.
Fuel is a bound on recursion depth: with enough of it the result does not depend on it, and
the trie is finite so `logicalHash` always supplies enough.  Running out of fuel yields the
hash of the empty message, which no node or value message can produce (see
`HashSecurity.lean`), so an inadequate fuel can never be mistaken for a real hash. -/
def hashFuel {V : Type} (vh : V → UInt64) (t : PathMap V) : Nat → Path → UInt64
  | 0, _ => fnv []
  | fuel + 1, p =>
      let m := t.childMask p
      let below := node m (m.map fun b => hashFuel vh t fuel (p ++ [b]))
      match t.valAt p with
      | some v => withValue (vh v) below
      | none => below

/-- The length of the longest existing path: every position in the trie is at most this deep. -/
def depth {V : Type} (t : PathMap V) : Nat :=
  t.paths.foldl (fun acc p => max acc p.length) 0

/-- `CatamorphismCached::hash_with_scheme` of a zipper whose focus is `p`, and of a `PathMap`
when `p = []`: the hash of the logical trie at and below `p`, including the value at `p`. -/
def logicalHash {V : Type} (vh : V → UInt64) (t : PathMap V) (p : Path) : UInt64 :=
  hashFuel vh t (depth t + 1) p

/-- The harness's instance: `PathMap<u64>` under `Fnv1a64Scheme`. -/
def hashU64 (t : PathMap UInt64) (p : Path) : UInt64 := logicalHash value t p

/-- 16 lowercase hex digits, matching the crate's `format!("{:016x}")`. -/
def hex64 (x : UInt64) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList <| (List.range 16).reverse.map fun i => digit ((x >>> (UInt64.ofNat (4 * i))).toNat % 16)

end Hash
end PathMapModel
