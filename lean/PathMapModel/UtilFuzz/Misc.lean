import PathMapModel.UtilFuzz.Base
import PathMapModel.UtilFuzz.Ints

/-!
# Util fuzzer, ops 80–99: path sorting and the feature-gated modules

## `sort_paths` / `sort_paths_par` (ops 80–84)

`paths_serialization::sort_paths(source, target, memory_bytes, temp_dir)`
reads an unordered `.paths` stream (a zlib stream of `[u32 len LE][path]`
records) and writes a `.paths` stream of the **same set of paths, in strictly
increasing byte order** (so deduplicated; `.paths` holds no values, so there is
nothing for stability to apply to).  Its documented contract, all of which the
ops check:

* `memory_bytes < 1 MiB` is refused with `InvalidInput`;
* a path longer than `memory_bytes / 16` is an `InvalidData` error;
* the returned `SerializationStats` are those of writing the output:
  `path_count` paths, `bytes_in` = Σ (4 + len) uncompressed bytes, `bytes_out`
  = the bytes written to `target`;
* run files go in the caller's `temp_dir` and are removed on success **and**
  on error: the directory is left empty (`t=0`);
* "a stream that ends partway through a path" is cut short silently: the
  complete records before the cut are sorted.

`sort_paths_par` is documented as a drop-in replacement with the same
arguments, output (decoded) and temporary-file contract, with one difference:
a stream that ends partway through a path (or partway through a length prefix)
is an `InvalidData` error.  A stream that stops at a record boundary without
its zlib trailer is accepted by both (the parallel sorter's code says "the
stream stopped short; accept its whole records").  Compressed bytes differ and
are not compared; only `bytes_out` = bytes written is.

The model below is the sorted, deduplicated path list; the parallel sorter is
held to exactly the same model (and so to the serial one), op by op.

See `differential/src/utilfuzz/misc.rs` for the op table and operand formats.
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec hexPath showBool)

namespace Misc

def mib : Nat := 1048576

/-! ### The sorted path set -/

/-- Byte-string order: unsigned bytes, a proper prefix first. -/
def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

def dedupAdj : List Path → List Path
  | a :: b :: rest => if a == b then dedupAdj (b :: rest) else a :: dedupAdj (b :: rest)
  | l => l

/-- The set of `ps`, in strictly increasing byte order. -/
def sortedSet (ps : List Path) : List Path :=
  dedupAdj (ps.mergeSort fun a b => !lexLt b a)

/-- `SerializationStats::bytes_in` of writing `ps`. -/
def bytesIn (ps : List Path) : Nat := ps.foldl (fun n p => n + 4 + p.length) 0

/-- FNV-1a 64 of the records `[u32 len LE][path]`. -/
def fnv (ps : List Path) : UInt64 :=
  let eat (h : UInt64) (b : UInt8) : UInt64 := (h ^^^ b.toUInt64) * 0x100000001b3
  ps.foldl (fun h p =>
    let n := p.length
    let h := [n % 256, n / 256 % 256, n / 65536 % 256, n / 16777216 % 256].foldl
      (fun h b => eat h (UInt8.ofNat b)) h
    p.foldl eat h) 0xcbf29ce484222325

def hex16 (x : UInt64) : String :=
  String.join ((List.range 8).reverse.map fun i => Fuzz.hexByte (UInt8.ofNat (x.toNat / 256 ^ i % 256)))

def showShort (p : Path) : String :=
  if p.length > 64 then "#" ++ toString p.length else hexPath p

/-- A sorter's answer for input paths `ps` (complete records) under budget
`mem`.  `truncated`: the stream ended inside a record, which only the parallel
sorter (`par`) reports. -/
def sorted (ps : List Path) (mem : Nat) (digest par truncated : Bool) : String :=
  if mem < mib then "err:InvalidInput,t=0"
  else if ps.any (·.length > mem / 16) then "err:InvalidData,t=0"
  else if par && truncated then "err:InvalidData,t=0"
  else
    let out := sortedSet ps
    let head := "n=" ++ toString out.length ++ ",u=" ++ toString (bytesIn out) ++ ",o=1,t=0"
    if digest then
      let f := match out.head? with | some p => showShort p | none => "-"
      let l := match out.getLast? with | some p => showShort p | none => "-"
      head ++ ";h=" ++ hex16 (fnv out) ++ ",f=" ++ f ++ ",l=" ++ l
    else head ++ ";[" ++ ",".intercalate (out.map hexPath) ++ "]"

def both (ps : List Path) (mem : Nat) (digest : Bool) (truncated : Bool := false) : String :=
  "S" ++ sorted ps mem digest false truncated ++ "|P" ++ sorted ps mem digest true truncated

/-- The records of a decompressed `.paths` prefix: the complete ones, and
whether bytes of an incomplete one follow. -/
partial def records (bs : List UInt8) : List Path × Bool :=
  match bs with
  | [] => ([], false)
  | a :: b :: c :: e :: rest =>
      let n := a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * e.toNat
      if rest.length < n then ([], true)
      else
        let (ps, t) := records (rest.drop n)
        (rest.take n :: ps, t)
  | _ => ([], true)

def encode (ps : List Path) : List UInt8 :=
  ps.flatMap fun p =>
    let n := p.length
    [n % 256, n / 256 % 256, n / 65536 % 256, n / 16777216 % 256].map UInt8.ofNat ++ p

/-! ### Fixtures -/

#guard sortedSet [[2], [1, 5], [], [1], [1, 5], [255], [1, 0]] == [[], [1], [1, 0], [1, 5], [2], [255]]
#guard sortedSet [] == []
#guard bytesIn [[1, 2], []] == 10
#guard records (encode [[1, 2], [], [7]]) == ([[1, 2], [], [7]], false)
#guard records ((encode [[1, 2], [3, 4, 5]]).take 9) == ([[1, 2]], true)
#guard records ((encode [[1, 2], [3]]).take 7) == ([[1, 2]], true)
#guard records ((encode [[1, 2], [3]]).take 6) == ([[1, 2]], false)
#guard sorted [[3], [1], [3]] mib false false false == "n=2,u=10,o=1,t=0;[01,03]"
#guard sorted [[3]] (mib - 1) false false false == "err:InvalidInput,t=0"
#guard sorted [[3]] mib false true true == "err:InvalidData,t=0"
#guard sorted [[3]] mib false false true == "n=1,u=5,o=1,t=0;[03]"
#guard sorted [List.replicate 65537 0] mib true false false == "err:InvalidData,t=0"
#guard sorted [List.replicate 65536 0] mib true false false |>.startsWith "n=1,u=65540"
#guard hex16 0xcbf29ce484222325 == "cbf29ce484222325"

/-! ### Operands -/

def readMem (d : Dec) : Option (Nat × Dec) := do
  let (m, d) ← d.u8
  let m := m.toNat
  some (if m % 16 == 0 then mib - 1 - m / 16 else (1 + m % 4) * mib, d)

def alphas : List Nat := [2, 4, 256]

def readList (d : Dec) : Option (List Path × Dec) := do
  let (a, d) ← d.mod 3
  let alpha := alphas.getD a 256
  let (n, d) ← d.mod 24
  Ints.many (fun d => do
    let (len, d) ← d.mod 20
    Ints.many (fun d => do
      let (b, d) ← d.u8
      pure (UInt8.ofNat (b.toNat % alpha), d)) len d) n d

def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

def pathOf (z : UInt64) (maxlen alpha : UInt64) : Path :=
  let z := lcg z
  go ((z >>> 40) % maxlen).toNat z []
where
  go : Nat → UInt64 → List UInt8 → List UInt8
    | 0, _, acc => acc.reverse
    | k + 1, z, acc =>
        let z := lcg z
        go k z (UInt8.ofNat ((z >>> 56) % alpha).toNat :: acc)

def generate (n : Nat) (maxlen alpha distinct seed : UInt64) : List Path :=
  go n (lcg seed) []
where
  go : Nat → UInt64 → List Path → List Path
    | 0, _, acc => acc.reverse
    | k + 1, x, acc => go k (lcg x) (pathOf (seed + (x >>> 16) % distinct) maxlen alpha :: acc)

def readGenerated (d : Dec) : Option ((List Path × Nat) × Dec) := do
  let (g, d) ← d.u8
  let (n, d) ← if g.toNat % 4 == 0 then do
      let (k, d) ← d.mod 20; pure (2000 * (1 + k), d)
    else do
      let (k, d) ← d.mod 8; pure (200 * (1 + k), d)
  let (ml, d) ← d.mod 3
  let maxlen := [8, 24, 64].getD ml 64
  let (a, d) ← d.mod 3
  let alpha := alphas.getD a 256
  let (di, d) ← d.mod 3
  let distinct := [n / 4, n, 2 ^ 32].getD di (2 ^ 32)
  let (b0, d) ← d.u8; let (b1, d) ← d.u8; let (b2, d) ← d.u8; let (b3, d) ← d.u8
  let seed := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
  let (mm, d) ← d.mod 2
  some ((generate n maxlen.toUInt64 alpha.toUInt64 distinct.toUInt64 seed.toUInt64, (1 + mm) * mib), d)

/-- `sort_cut`: how many data bytes of the stored-block stream survive. -/
def readCut (dataLen : Nat) (d : Dec) : Option (Nat × Dec) := do
  let total := dataLen + 11
  let (mode, d) ← d.mod 4
  if mode == 0 then pure (total, d)
  else if mode == 1 then do
    let (lo, d) ← d.u8; let (hi, d) ← d.u8
    pure (7 + (lo.toNat + 256 * hi.toNat) % (dataLen + 1), d)
  else if mode == 2 then do
    let (k, d) ← d.mod 4; pure (total - 1 - k, d)
  else d.mod 7

end Misc

open Misc in
def stepMisc (op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  if op == 80 || op == 81 then do
    let (mem, d) ← readMem d
    let (ps, d) ← readList d
    let par := op == 81
    some (((if par then "sort_paths_par" else "sort_paths"), sorted ps mem false par false), d)
  else if op == 82 then do
    let ((ps, mem), d) ← readGenerated d
    some (("sort_big", both ps mem true), d)
  else if op == 83 then do
    let (ps, d) ← readList d
    let data := encode ps
    let (keep, d) ← readCut data.length d
    -- Byte `7 + i` of the stream is data byte `i`; the trailer adds no data.
    let (recs, partial_) := records (data.take (keep - 7))
    some (("sort_cut", both recs mib false partial_), d)
  else if op == 84 then do
    let (δ, d) ← d.mod 3
    let (ps, d) ← readList d
    let (_at, d) ← d.mod (ps.length + 1)
    some (("sort_long", both (List.replicate (65535 + δ) 0xa5 :: ps) mib true), d)
  else
    some (("nop", "-"), d)

end UtilFuzz
end PathMapModel
