import PathMapModel.Fuzz

/-!
# The map-level fuzzer: state, decoding, rendering

A second differential program, selected with `--source map`, for everything
that is not a zipper walking a trie: the `PathMap` surface, the lattice ops on
whole maps, serialization round trips, `ArenaCompactTree` files and streams,
catamorphisms/anamorphisms, and `ZipperHead` sessions.  The Rust side is
`differential/src/mapfuzz/`; the two must decode the same bytes the same way
and print the same trace.

## Wire format

The `PMFUZZ` header (magic + u16 selector count, `MAP_NOPS` for new inputs),
then

```
header:  3 × ( n := u8 % 8 ; n × ( len := u8 % 6 ; len × pathbyte ; val := u8 ) )
body:    repeated: op := u8 % count ; operands per op
```

Path bytes are masked to `b % 4`, as in the zipper fuzzer.  A map operand is
`u8 % 3`.

## Trace format

One line per operation, then a dump of each map:

```
<i> <name> ret=<r> n=<val_count m0>,<val_count m1>,<val_count m2>
M0 <dump>  M1 <dump>  M2 <dump>
```

## Op ranges

Each group owns a range of selectors and lives in its own file
(`MapFuzz/<Group>.lean` here, `mapfuzz/<group>.rs` in Rust); a selector in a
range its group does not use is a `nop` on both sides.

| range | group | file |
|---|---|---|
| 0–19  | the `PathMap` surface | `Core` |
| 20–29 | whole-map lattice ops | `Lattice` |
| 30–39 | serialization round trips | `Serial` |
| 40–49 | `ArenaCompactTree` files, merge, stream | `Act` |
| 50–59 | catamorphisms, anamorphisms | `Morph` |
| 60–69 | `ZipperHead` sessions | `Head` |
| 70–79 | experimental zippers (`FullZipper`, `NullZipper`, `DiffZipper`) | `Exp` |
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V ops Dec hexPath hexByte showVal showBool dumpAt)

/-- Selector count for new map-fuzzer inputs; `MAP_NOPS` in
`differential/src/mapfuzz/mod.rs` and `lean/input_format.py`. -/
def mapNops : Nat := 80

/-- Three maps. -/
structure MSt where
  m0 : PathMap V
  m1 : PathMap V
  m2 : PathMap V
  out : List String := []
  step : Nat := 0

def MSt.get (s : MSt) : Nat → PathMap V
  | 0 => s.m0
  | 1 => s.m1
  | _ => s.m2

def MSt.set (s : MSt) (i : Nat) (t : PathMap V) : MSt :=
  match i with
  | 0 => { s with m0 := t }
  | 1 => { s with m1 := t }
  | _ => { s with m2 := t }

/-- One step's result: the op name, its rendered return value, the new state. -/
abbrev Res := String × String × MSt

/-- Read a map operand (`u8 % 3`). -/
def _root_.PathMapModel.Fuzz.Dec.map (d : Dec) : Option (Nat × Dec) := d.mod 3

/-- Read a value (`u8`, as `u64`). -/
def _root_.PathMapModel.Fuzz.Dec.val (d : Dec) : Option (V × Dec) := d.u8.map (fun (b, d') => (UInt64.ofNat b.toNat, d'))

/-- `PathMap::val_count` of each map, for the per-step line. -/
def counts (s : MSt) : String :=
  toString (s.m0.valCount []) ++ "," ++ toString (s.m1.valCount []) ++ "," ++
  toString (s.m2.valCount [])

def emit (s : MSt) (name ret : String) : MSt :=
  { s with
    out := (toString s.step ++ " " ++ name ++ " ret=" ++ ret ++ " n=" ++ counts s) :: s.out
    step := s.step + 1 }

/-- Render a list of `(path, value)` pairs as `path:val,...` (`_` for empty). -/
def showPairs (xs : List (Path × V)) : String :=
  if xs.isEmpty then "_" else
  String.intercalate "," (xs.map (fun (p, v) => hexPath p ++ ":" ++ toString v.toNat))

/-- Render a list of paths, `,`-separated (`_` for empty list, `_` for the
empty path too, which is unambiguous because it can only be alone or first). -/
def showPaths (xs : List Path) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map hexPath)

end MapFuzz
end PathMapModel
