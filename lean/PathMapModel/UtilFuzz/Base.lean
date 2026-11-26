import PathMapModel.Fuzz

/-!
# The util fuzzer: format and op ranges

A third differential program, selected with `--source util`, for the public
parts of `pathmap` that are neither a zipper nor a `PathMap`.  The Rust side is
`differential/src/utilfuzz/`.  Ops are **stateless**: each decodes its own
operands, and its trace line renders the crate's full answer.

## Wire format

The `PMFUZZ` header (magic + u16 selector count, `UTIL_NOPS` for new inputs),
then repeated `op := u8 % count ; operands`.  No header data.

## Trace format

One line per op: `<i> <name> ret=<r>`.

## Op ranges

| range | group | file |
|---|---|---|
| 0–29  | `ByteMask`, `BitMask for [u64; 4]`, other `utils/mod.rs` items | `Mask` |
| 30–59 | `ring.rs`: the `Lattice` / `DistributiveLattice` / `Quantale` impls, `AlgebraicResult`, `AlgebraicStatus`, `SetLattice` | `Lattice` |
| 60–79 | `utils/ints.rs`: `PathInteger` | `Ints` |
| 80–99 | path sorting (`sort_paths`, `sort_paths_par`) and the rest | `Misc` |
-/

namespace PathMapModel
namespace UtilFuzz

open Fuzz (Dec)

/-- `UTIL_NOPS` in `differential/src/utilfuzz/mod.rs` and `lean/input_format.py`. -/
def utilNops : Nat := 100

/-- A `ByteMask` operand: `n := u8 % 12`, then `n` member bytes (full range). -/
def maskBytes (d : Dec) : Option (List UInt8 × Dec) := do
  let (n, d) ← d.mod 12
  let rec go : Nat → Dec → Option (List UInt8 × Dec)
    | 0, d => some ([], d)
    | k + 1, d => do
        let (b, d) ← d.u8
        let (rest, d) ← go k d
        some (b :: rest, d)
  go n d

/-- `pathmap::ring::AlgebraicResult<V>` with its identity mask as a number (bit
`i` = "the result is argument `i`"; for a binary op `1` is `SELF_IDENT`, `2` is
`COUNTER_IDENT`).  `ValRes` in `Basic.lean` spells the mask as two flags, which
cannot express an n-ary result such as `join_all`'s; `ofValRes` converts. -/
inductive AlgResult (V : Type) where
  | none
  | identity (mask : Nat)
  | element (v : V)
deriving BEq, Repr

def AlgResult.ofValRes {V : Type} : ValRes V → AlgResult V
  | .elem v => .element v
  | .identity s c => .identity ((if s then 1 else 0) + (if c then 2 else 0))
  | .none => .none

/-- Render an `AlgebraicResult`: `None`, `Identity(<mask, decimal>)`,
`Element(<showV v>)`.  `show_alg_result` in `differential/src/utilfuzz/mod.rs`. -/
def showAlgResult {V : Type} (showV : V → String) : AlgResult V → String
  | .none => "None"
  | .identity m => s!"Identity({m})"
  | .element v => s!"Element({showV v})"

end UtilFuzz
end PathMapModel
