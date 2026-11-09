import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 50–59: catamorphisms, anamorphisms

`src/morphisms.rs`: the `Catamorphism` trait in all its flavours and the
anamorphism `PathMap::new_from_ana(_in)` with its `TrieBuilder`.  The Rust side
is `differential/src/mapfuzz/morph.rs`.

## What a catamorphism visits

Everything here is stated on the **view**: the trie `T` the folded object
presents, relative to its root, plus the root's absolute path `r` (the `path`
argument is `ZipperAbsolutePath::origin_path`, so it carries `r`).  `T` includes
the root's value and every *existing* location below it, dangling ones
included — a dangling leaf is a location with an empty mask and no value, and is
visited like any other leaf.  The zipper's focus is ignored (the doc: "it will be
immediately reset to the root").

* **Stepping** (`into_cata_side_effect`, `into_cata_cached`): the closure runs
  once at every location of `T`, the root included ("exactly once for each
  unique path in the trie").  Its `children` are the results for `q ++ [b]`, one
  per bit `b` of its child mask, in ascending byte order.
* **Jumping** (`into_cata_jumping_*`): the closure runs only at *features* —
  locations with a value or a child count other than 1 (forks and leaves) —
  and "jumps over" the single-child, valueless locations between them.  A
  feature's `children` are, for each child byte `b`, the result at the first
  feature on the chain starting at `q ++ [b]`; its `jump` is the number of
  jumped bytes between it and the feature above it, *not counting* the byte
  that the parent's mask names (`|F| - |q| - 1`).  The root is visited iff it
  is a feature; when it is not (one child, no value) the result is its only
  child's, whose jump then counts from the root and includes that first byte
  (`|F|`).  This is the documented `combo/comet/comfort` example: four calls,
  the last with sub-path `com`.  The cached jumping flavour hands the closure
  the jumped bytes themselves, `sub_path = path[|path| - jump ..]`.
* **Side-effecting** flavours run in a deterministic post-order: all of a
  location's children (ascending byte order), then the location.  The closure
  here stamps each call with its sequence number, so the result records the
  order.  A `_fallible` run stops at the first `Err`: the result is that `Err`
  and no further call happens.
* **Cached** flavours see no path, may skip a shared subtrie whose result they
  already have, and promise nothing about order; their result must still be
  exactly the uncached fold of the same closure.  Their `_fallible` predicate
  here is order-independent (every `Err` is the same), so the answer is `Err`
  iff some visited location satisfies it.
* `hash` / `hash_with` are cached folds over (mask, children's hashes, value
  hash), so they are compared as an equivalence: two views hash equal iff they
  are the same trie (dangling paths included, through the masks) with equal
  values under `val_hash`.

## Anamorphisms

`new_from_ana(w, alg)` runs `alg(w, &mut val, builder, path)` at the root, then,
depth-first in push order, at `path ++ sub` for every child `(sub, w')` pushed
into the builder (`push_byte`, `push`, `set_child_mask`).  `graft_at_byte(b, rz)`
instead places the subtrie strictly *below* `rz`'s focus at `path ++ [b]` and
does not recurse (the value at `rz`'s focus is not part of that node).  The
result holds exactly: the values set, the grafted content (dangling paths
included), and their prefixes.  A location that got neither a value nor
anything below it does not exist.  `ana` below is that rule for any closure;
`copyAlg` and `repAlg` are the two closures the fuzzer runs.

## Ops

| op | name | operands | result |
|---|---|---|---|
| 50 | `cata_side` | csrc, `e` | stepping side-effect fold; `e` odd: `_fallible`, `Err` at call `(e >> 1) % 32` |
| 51 | `cata_jump_side` | csrc, `e` | the same, jumping |
| 52 | `cata_cached` | csrc, `pred`, `v` | stepping cached fold; `pred % 4 ≠ 0`: `_fallible` (see `cachedFails`) |
| 53 | `cata_jump_cached` | csrc, `pred`, `v` | the same, jumping |
| 54 | `hash` | csrc, csrc | `eq=` hashes equal, `eqw=` `hash_with(v % 3)` equal |
| 55 | `ana_copy` | `i`, `p`, `dst`, `s`, `in` | `m[dst] := new_from_ana(_in)(p, copyAlg m[i] s)` |
| 56 | `ana_replicate` | `i`, `p`, `dst`, `lv`, `mb` | `m[dst] :=` a `lv`-level tree grafting `m[i]`'s node at `p` (see `repAlg`) |

A *csrc* is `i : map, kind : u8 % 3, p : path(4), f : path(4), q : path(6)`: a
clone of `m[i]` with `q` created as a (possibly dangling) path, folded as the
map itself (`kind 0`, root `[]`), as `read_zipper_at_path(p)` (`kind 1`) or as
`into_read_zipper(p)` (`kind 2`), the zippers first moved to `f`.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool)

namespace Morph

/-! ## The folded view -/

structure CSrc where
  i : Nat
  kind : Nat
  p : Path
  f : Path
  q : Path

def decCSrc (d : Dec) : Option (CSrc × Dec) := do
  let (i, d) ← d.map
  let (kind, d) ← d.mod 3
  let (p, d) ← d.path 4
  let (f, d) ← d.path 4
  let (q, d) ← d.path 6
  some ({ i, kind, p, f, q }, d)

/-- The trie a csrc presents, relative to its root, and the root's absolute path. -/
def CSrc.view (s : MSt) (c : CSrc) : PathMap V × Path :=
  let t := s.get c.i
  let t := if c.q.isEmpty then t else t.addPath c.q
  if c.kind == 0 then (t, []) else (t.subtrie c.p, c.p)

/-- A location a jumping fold stops at: valued, or not exactly one child. -/
def isFeature (T : PathMap V) (q : Path) : Bool :=
  (T.valAt q).isSome || T.childCount q != 1

/-- The first feature at or below `q` along its single-child chain. -/
def follow (T : PathMap V) : Nat → Path → Path
  | 0, q => q
  | n + 1, q =>
      if isFeature T q then q else
      match T.childMask q with
      | [b] => follow T n (q ++ [b])
      | _ => q

/-- Recursion bound: deeper than any path in `T`. -/
def fuel (T : PathMap V) : Nat := (T.paths.map List.length).foldl max 0 + 2

def showJump : Option Nat → String
  | none => ""
  | some j => ":" ++ toString j

/-- One side-effecting call's result and its `Err` (when it is the failing call). -/
def encSide (i : Nat) (path : Path) (jump : Option Nat) (v : Option V) (mask : ByteMask)
    (ws : List String) : String :=
  "(" ++ toString i ++ ":" ++ hexPath path ++ showJump jump ++ ":" ++ showVal v ++ ":" ++
    hexPath mask ++ String.join ws ++ ")"

def errSide (i : Nat) (path : Path) (jump : Option Nat) (v : Option V) (mask : ByteMask) : String :=
  "E" ++ toString i ++ ":" ++ hexPath path ++ showJump jump ++ ":" ++ showVal v ++ ":" ++
    hexPath mask ++ ":" ++ toString mask.length

/-! ## Side-effecting folds: post-order, numbered

Each returns `(result, next call number, the Err each call would return, in call order)`. -/

def sideStep (T : PathMap V) (r : Path) : Nat → Path → Nat → String × Nat × List String
  | 0, _, i => ("", i, [])
  | n + 1, q, i =>
      let mask := T.childMask q
      let (ws, i, log) := mask.foldl (fun (acc : List String × Nat × List String) b =>
        let (w, i', l') := sideStep T r n (q ++ [b]) acc.2.1
        (acc.1 ++ [w], i', acc.2.2 ++ l')) ([], i, [])
      let v := T.valAt q
      (encSide i (r ++ q) none v mask ws, i + 1, log ++ [errSide i (r ++ q) none v mask])

/-- At feature `q`, reached with `jump` jumped bytes. -/
def sideJump (T : PathMap V) (r : Path) : Nat → Path → Nat → Nat → String × Nat × List String
  | 0, _, _, i => ("", i, [])
  | n + 1, q, jump, i =>
      let mask := T.childMask q
      let (ws, i, log) := mask.foldl (fun (acc : List String × Nat × List String) b =>
        let f := follow T (fuel T) (q ++ [b])
        let (w, i', l') := sideJump T r n f (f.length - q.length - 1) acc.2.1
        (acc.1 ++ [w], i', acc.2.2 ++ l')) ([], i, [])
      let v := T.valAt q
      (encSide i (r ++ q) (some jump) v mask ws, i + 1,
        log ++ [errSide i (r ++ q) (some jump) v mask])

def sideFold (T : PathMap V) (r : Path) (jumping : Bool) : String × Nat × List String :=
  if !jumping then sideStep T r (fuel T) [] 0
  else if isFeature T [] then sideJump T r (fuel T) [] 0 0
  else
    let f := follow T (fuel T) []
    sideJump T r (fuel T) f f.length 0

/-- Ops 50/51: the result, `Err` at call `k` if there are that many calls. -/
def sideResult (T : PathMap V) (r : Path) (jumping : Bool) (errAt : Option Nat) : String :=
  let (w, n, log) := sideFold T r jumping
  match errAt with
  | some k =>
      match log[k]? with
      | some e => "Err:" ++ e ++ " calls=" ++ toString (k + 1)
      | none => w ++ " calls=" ++ toString n
  | none => w ++ " calls=" ++ toString n

/-! ## Cached folds: pure, no path -/

def encCached (sub : Option Path) (v : Option V) (mask : ByteMask) (ws : List String) : String :=
  "(" ++ (match sub with | some s => hexPath s ++ ":" | none => "") ++ showVal v ++ ":" ++
    hexPath mask ++ String.join ws ++ ")"

def cachedStep (T : PathMap V) : Nat → Path → String
  | 0, _ => ""
  | n + 1, q =>
      let mask := T.childMask q
      encCached none (T.valAt q) mask (mask.map fun b => cachedStep T n (q ++ [b]))

/-- At feature `q`, which the fold reached by jumping over `sub`. -/
def cachedJump (T : PathMap V) : Nat → Path → Path → String
  | 0, _, _ => ""
  | n + 1, q, sub =>
      let mask := T.childMask q
      encCached (some sub) (T.valAt q) mask (mask.map fun b =>
        let f := follow T (fuel T) (q ++ [b])
        cachedJump T n f (f.drop (q.length + 1)))

def cachedFold (T : PathMap V) (jumping : Bool) : String :=
  if !jumping then cachedStep T (fuel T) []
  else if isFeature T [] then cachedJump T (fuel T) [] []
  else
    let f := follow T (fuel T) []
    cachedJump T (fuel T) f f

/-- The `_fallible` predicate, `pred % 4`: 1 the value is `v`; 2 the child count
is `(pred >> 2) % 4`; 3 one child and no value (a location only a *stepping*
fold visits). -/
def cachedFails (pred : Nat) (v : V) (T : PathMap V) (q : Path) : Bool :=
  match pred % 4 with
  | 1 => T.valAt q == some v
  | 2 => T.childCount q == (pred / 4) % 4
  | 3 => T.childCount q == 1 && (T.valAt q).isNone
  | _ => false

/-- Ops 52/53.  The visited set: every location (stepping) or every feature
(jumping; the root only when it is one). -/
def cachedResult (T : PathMap V) (jumping : Bool) (pred : Nat) (v : V) : String :=
  let visited := if jumping then T.paths.filter (isFeature T) else T.paths
  if pred % 4 != 0 && visited.any (cachedFails pred v T) then "Err:E"
  else cachedFold T jumping

/-! ## Hashing -/

def mapVals (f : V → V) (T : PathMap V) : PathMap V :=
  PathMap.mk' (T.vals.map fun (p, x) => (p, f x)) T.paths

def sameTrie (a b : PathMap V) : Bool := a.entries == b.entries

/-! ## Anamorphisms -/

/-- What the closure put in the `TrieBuilder`. -/
inductive AnaKid (W : Type) where
  /-- `push(sub, w)` / `push_byte` / `set_child_mask`: recurse at `path ++ sub`. -/
  | w (sub : Path) (w : W)
  /-- `graft_at_byte(b, rz)`: `node` is the subtrie at `rz`'s focus; only what is
  strictly below its root is placed, at `path ++ [b]`. -/
  | graft (b : UInt8) (node : PathMap V)

/-- Values, grafted locations and call paths (pre-order) of an anamorphism. -/
def anaGo {W : Type} (alg : W → Path → Option V × List (AnaKid W)) :
    Nat → W → Path → List (Path × V) × List Path × List Path
  | 0, _, _ => ([], [], [])
  | n + 1, w, path =>
      let (v, kids) := alg w path
      let vals0 : List (Path × V) := match v with | some x => [(path, x)] | none => []
      kids.foldl (fun (acc : List (Path × V) × List Path × List Path) k =>
        match k with
        | .w sub w' =>
            let (vs, ps, cs) := anaGo alg n w' (path ++ sub)
            (acc.1 ++ vs, acc.2.1 ++ ps, acc.2.2 ++ cs)
        | .graft b node =>
            (acc.1 ++ node.vals.filterMap (fun (q, x) =>
                if q.isEmpty then none else some (path ++ [b] ++ q, x)),
             acc.2.1 ++ node.paths.filterMap (fun q =>
                if q.isEmpty then none else some (path ++ [b] ++ q)),
             acc.2.2)) (vals0, [], [path])

/-- `PathMap::new_from_ana(w, alg)`: the map and the paths `alg` was called at. -/
def ana {W : Type} (alg : W → Path → Option V × List (AnaKid W)) (w : W) (fuel : Nat) :
    PathMap V × List Path :=
  let (vs, ps, cs) := anaGo alg fuel w []
  (PathMap.mk' vs ps, cs)

/-- Op 55's closure.  `W` is a path in `src`.  The value at `w` is kept unless
`(v + depth) % 4 = (s >> 2) % 4`, and is increased by `s >> 6`.  If
`((s >> 1) + depth) % 3 = 0` every child is set at once with `set_child_mask`;
otherwise child `b` is, by `((s >> 4) % 4 + b + depth) % 4`: 0 `push_byte`,
1 `push` of `b` and the single-child chain after it, 2 `graft_at_byte` of
`src` at `w ++ [b]` (`push_byte` when that has nothing below), 3 dropped. -/
def copyAlg (src : PathMap V) (s : Nat) (w : Path) (path : Path) : Option V × List (AnaKid Path) :=
  let depth := path.length
  let v := match src.valAt w with
    | some x => if (x.toNat + depth) % 4 != (s / 4) % 4 then some (x + UInt64.ofNat (s / 64)) else none
    | none => none
  let mask := src.childMask w
  if ((s / 2) + depth) % 3 == 0 then (v, mask.map fun b => .w [b] (w ++ [b]))
  else (v, mask.filterMap fun b =>
    let wc := w ++ [b]
    match ((s / 16) % 4 + b.toNat + depth) % 4 with
    | 0 => some (.w [b] wc)
    | 1 => let ch := (follow src (fuel src) wc).drop wc.length
           some (.w (b :: ch) (wc ++ ch))
    | 2 => if src.childCount wc > 0 then some (.graft b (src.subtrie wc)) else some (.w [b] wc)
    | _ => none)

/-- Op 56's closure.  `W` is the remaining level count: level 0 grafts `node`
at each byte of `bytes` (if it has anything below its root), higher levels
`push_byte` each byte with one level less; with `setVals` every call sets the
value `|path|`. -/
def repAlg (node : PathMap V) (has : Bool) (bytes : List UInt8) (setVals : Bool) (lvl : Nat)
    (path : Path) : Option V × List (AnaKid Nat) :=
  (if setVals then some (UInt64.ofNat path.length) else none,
   if lvl == 0 then (if has then bytes.map (fun x => .graft x node) else [])
   else bytes.map (fun x => .w [x] (lvl - 1)))

/-- Location bound for `ana_replicate`; `REP_CAP` in morph.rs. -/
def repCap : Nat := 256

end Morph

open Morph in
def stepMorph (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 50 | 51 => do
      let (c, d) ← decCSrc d
      let (e, d) ← d.u8
      let errAt := if e.toNat % 2 == 0 then none else some ((e.toNat / 2) % 32)
      let (T, r) := c.view s
      some (((if op == 50 then "cata_side" else "cata_jump_side"),
        sideResult T r (op == 51) errAt, s), d)
  | 52 | 53 => do
      let (c, d) ← decCSrc d
      let (pred, d) ← d.u8
      let (v, d) ← d.val
      let (T, _) := c.view s
      some (((if op == 52 then "cata_cached" else "cata_jump_cached"),
        cachedResult T (op == 53) pred.toNat v, s), d)
  | 54 => do
      let (a, d) ← decCSrc d
      let (b, d) ← decCSrc d
      let (ta, _) := a.view s
      let (tb, _) := b.view s
      let m3 := mapVals (fun x => x % 3)
      some (("hash", "eq=" ++ showBool (sameTrie ta tb) ++ " eqw=" ++
        showBool (sameTrie (m3 ta) (m3 tb)), s), d)
  | 55 => do
      let (i, d) ← d.map
      let (p, d) ← d.path 4
      let (dst, d) ← d.map
      let (sb, d) ← d.u8
      let (_useIn, d) ← d.bool
      let src := s.get i
      let (m, calls) := ana (copyAlg src sb.toNat) p (fuel src + 1)
      some (("ana_copy", "calls=" ++ String.intercalate "," (calls.map hexPath), s.set dst m), d)
  | 56 => do
      let (i, d) ← d.map
      let (p, d) ← d.path 4
      let (dst, d) ← d.map
      let (lv, d) ← d.mod 3
      let (mb, d) ← d.u8
      let src := s.get i
      let bytes0 := [0, 1, 2, 3].filter (fun x => (mb.toNat / 2 ^ x) % 2 == 1)
      let bytes := (if bytes0.isEmpty then [0] else bytes0).map UInt8.ofNat
      let setVals := (mb.toNat / 16) % 2 == 1
      let node := src.subtrie p
      -- `skip:too-big` (`SKIP_TOO_BIG` in morph.rs): repeated replication would
      -- otherwise grow a map exponentially, past what this list model handles
      -- quickly.  Bound: node locations × |bytes|^(lv+1) ≤ `repCap`.
      if (if src.pathExists p then node.paths.length else 1) * bytes.length ^ (lv + 1) > repCap then
        some (("ana_replicate", "skip:too-big", s), d)
      else
      let (m, calls) := ana (repAlg node (src.childCount p > 0) bytes setVals) lv (lv + 2)
      some (("ana_replicate", "calls=" ++ toString calls.length, s.set dst m), d)
  | _ => some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
