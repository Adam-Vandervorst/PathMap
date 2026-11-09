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

/-! ## `viz` (ops 85–87; cargo feature `viz`, enabled in the differential crate)

`viz_maps(maps, config, out)` draws the tries of one or more `PathMap`s, as
Mermaid markup or as an ASCII tree.  What it draws, for maps whose nodes are
not shared (the ops build each map from scratch with `set_val_at`, so physical
sharing never shows):

* **Logical rendering** (`logical: true`): a radix tree.  Its nodes are the
  root and every location that branches (two or more children) or, unless
  `hide_value_paths`, holds a value and continues with one child.  Every other
  location is folded into the edge through it, labelled with the path bytes
  between the two nodes.  A value at a node is drawn at that node, a value at
  a leaf as an edge from the nearest node; `hide_value_paths` draws no values,
  `minimize_values` draws them without their text.  Labels are the bytes as a
  string when `ascii_path` and they are valid UTF-8, else `[b, b, ...]`.
* **ASCII** (`VizMode::Ascii`): the exact text (`asciiText`): a
  `PathMap[i] = v` line, then the edges in byte order of their labels, drawn
  with `├── ` / `└── ` and indented `│   ` / `    `; maps separated by a
  blank line; `(empty)` under a root with nothing to draw.  `color` only
  colours shared-node markers, so it never shows here.
* **Mermaid, logical**: node ids are hashes of addresses, so the rendering is
  compared as a graph (`mermaidCanon`): from each map's root, the labelled
  edges in byte order, to nodes or to values (a node's own value is an edge
  with the empty label).
* **Mermaid, physical** (`logical: false`): nodes are the in-memory nodes, so
  only what the layout must show is compared (`mermaidValues`): the values
  reached by concatenating edge labels from the root, i.e. every value of the
  map at its path.

A root value is part of the map, so every rendering shows it.  The mermaid
renderers do not (finding `viz_mermaid_drops_root_value`): an op on maps with
a root value is named `viz_mermaid_rv` / `viz_phys_rv`, leaves the root value
out of its answer and ends with `;skip:viz-mermaid-root-value` (same token in
`misc.rs`), so the rest of the graph is still compared.
`viz_maps` panics on a map with nothing below the root (finding
`viz_no_root_node`): such an op renders `skip:viz-no-root-node` on both sides.
-/

/-- A logical map: `(path, value)` pairs, paths distinct, root value allowed. -/
abbrev LMap := List (Path × Nat)

def LMap.set (m : LMap) (p : Path) (v : Nat) : LMap :=
  if m.any (·.1 == p) then m.map fun e => if e.1 == p then (p, v) else e else m ++ [(p, v)]

def LMap.val? (m : LMap) (p : Path) : Option Nat := (m.find? (·.1 == p)).map (·.2)

/-- The children bytes of location `p`, ascending. -/
def LMap.children (m : LMap) (p : Path) : List UInt8 :=
  ((m.filterMap fun (q, _) => if p.isPrefixOf q && q.length > p.length then q[p.length]? else none).eraseDups).mergeSort (· ≤ ·)

/-- An edge of the radix tree: to a node (its own value, its edges) or to a value. -/
inductive GEdge where
  | node (label : Path) (val : Option Nat) (kids : List GEdge)
  | value (label : Path) (v : Nat)

def GEdge.label : GEdge → Path
  | .node l _ _ => l
  | .value l _ => l

def isGraphNode (m : LMap) (hide : Bool) (q : Path) : Bool :=
  let cc := (m.children q).length
  cc > 1 || ((m.val? q).isSome && cc == 1 && !hide)

/-- The edges out of the node at `p`. -/
partial def graphEdges (m : LMap) (hide : Bool) (p : Path) : List GEdge :=
  let rec walk (q : Path) : List GEdge :=
    if isGraphNode m hide q then
      [.node (q.drop p.length) (if hide then none else m.val? q) (graphEdges m hide q)]
    else
      let here := match m.val? q with
        | some v => if hide then [] else [GEdge.value (q.drop p.length) v]
        | none => []
      here ++ (m.children q).flatMap fun b => walk (q ++ [b])
  ((m.children p).flatMap fun b => walk (p ++ [b])).mergeSort fun a b => !lexLt b.label a.label

def byteList (p : Path) : String := "[" ++ ", ".intercalate (p.map fun b => toString b.toNat) ++ "]"

def label (ascii : Bool) (p : Path) : String :=
  if ascii then (String.fromUTF8? ⟨p.toArray⟩).getD (byteList p) else byteList p

structure VizCfg where
  ascii : Bool
  hide : Bool
  minimize : Bool

def valuePart (c : VizCfg) : Option Nat → String
  | none => ""
  | some v => if c.minimize then "" else " = " ++ toString v

partial def asciiEdges (c : VizCfg) (prefix_ : String) (es : List GEdge) : List String :=
  let n := es.length
  (es.zipIdx).flatMap fun (e, i) =>
    let last := i + 1 == n
    let conn := if last then "└── " else "├── "
    match e with
    | .value l v => [prefix_ ++ conn ++ label c.ascii l ++ valuePart c (some v)]
    | .node l v kids =>
        (prefix_ ++ conn ++ label c.ascii l ++ valuePart c v) ::
          asciiEdges c (prefix_ ++ (if last then "    " else "│   ")) kids

/-- The exact ASCII rendering of logical maps. -/
def asciiText (c : VizCfg) (ms : List LMap) : String :=
  "\n".intercalate <| (ms.zipIdx).map fun (m, i) =>
    let rv := if c.hide then none else m.val? []
    let es := graphEdges m c.hide []
    let lines := ("PathMap[" ++ toString i ++ "]" ++ valuePart c rv) ::
      (if es.isEmpty && rv.isNone then ["(empty)"] else asciiEdges c "" es)
    String.join (lines.map (· ++ "\n"))

def valText (c : VizCfg) (v : Nat) : String := if c.minimize then "." else toString v

partial def canonNode (c : VizCfg) (es : List GEdge) : String :=
  let es := es.mergeSort fun a b => !lexLt b.label a.label
  "{" ++ ",".intercalate (es.map fun
    | .value l v => hexPath l ++ "=" ++ valText c v
    | .node l v kids =>
        hexPath l ++ canonNode c ((match v with | some v => [GEdge.value [] v] | none => []) ++ kids)) ++ "}"

/-- The graph of the logical Mermaid rendering (see `mermaid_canon`).
`withRoot := false` leaves root values out (`skip:viz-mermaid-root-value`). -/
def mermaidCanon (c : VizCfg) (ms : List LMap) (withRoot : Bool := true) : String :=
  ";".intercalate <| ms.map fun m =>
    let rv := if c.hide || !withRoot then [] else match m.val? [] with | some v => [GEdge.value [] v] | none => []
    "M" ++ canonNode c (rv ++ graphEdges m c.hide [])

/-- The values of the physical Mermaid rendering (see `mermaid_values`). -/
def mermaidValues (c : VizCfg) (ms : List LMap) (withRoot : Bool := true) : String :=
  ";".intercalate <| ms.map fun m =>
    let m := if withRoot then m else m.filter (!·.1.isEmpty)
    let vs := if c.hide then [] else m.mergeSort fun a b => !lexLt b.1 a.1
    "M[" ++ ",".intercalate (vs.map fun (p, v) => hexPath p ++ "=" ++ valText c v) ++ "]"

/-- Rust's `esc`: `\n`, `\\`, and non-printable-ASCII chars as `\u{hex}`. -/
def esc (s : String) : String :=
  String.join <| s.toList.map fun ch =>
    if ch == '\n' then "\\n" else if ch == '\\' then "\\\\"
    else if ' ' ≤ ch && ch ≤ '~' then ch.toString
    else "\\u{" ++ String.mk (Nat.toDigits 16 ch.toNat) ++ "}"

private def vx : LMap := [([], 1), ("ab".toUTF8.toList, 2), ("abc".toUTF8.toList, 3), ("abd".toUTF8.toList, 4), ("b".toUTF8.toList, 5)]

-- The crate's own rendering of this map (probe run, 2026-11-09).
#guard asciiText ⟨true, false, false⟩ [vx] ==
  "PathMap[0] = 1\n├── ab = 2\n│   ├── c = 3\n│   └── d = 4\n└── b = 5\n"
#guard asciiText ⟨false, true, false⟩ [vx] == "PathMap[0]\n└── [97, 98]\n"
#guard asciiText ⟨true, true, false⟩ [[("ab".toUTF8.toList, 1)]] == "PathMap[0]\n(empty)\n"
#guard mermaidCanon ⟨true, false, false⟩ [vx] == "M{_=1,6162{_=2,63=3,64=4},62=5}"
#guard mermaidValues ⟨true, false, true⟩ [vx] == "M[_=.,6162=.,616263=.,616264=.,62=.]"
#guard label true [0xc3, 0xa9] == "é" && label true [0xc3] == "[195]"
#guard esc "a\n├é" == "a\\n\\u{251c}\\u{e9}"

def vizAlpha : List UInt8 := [0x61, 0x62, 0xc3, 0xa9]

def readSmallMap (d : Dec) : Option (LMap × Dec) := do
  let (rv, d) ← d.u8
  let m : LMap := if rv.toNat % 2 == 1 then [([], rv.toNat / 2)] else []
  let (n, d) ← d.mod 8
  let rec go : Nat → LMap → Dec → Option (LMap × Dec)
    | 0, m, d => some (m, d)
    | k + 1, m, d => do
        let (len, d) ← d.mod 5
        let (p, d) ← Ints.many (fun d => do let (i, d) ← d.mod 4; pure (vizAlpha.getD i 0, d)) len d
        let (v, d) ← d.u8
        go k (m.set p v.toNat) d
  go (n + 1) m d

def readMaps (d : Dec) : Option (List LMap × Dec) := do
  let (k, d) ← d.mod 3
  Ints.many readSmallMap (k + 1) d

def readVizCfg (d : Dec) : Option (VizCfg × Dec) := do
  let (f, d) ← d.u8
  let f := f.toNat
  some (⟨f % 2 == 1, f / 2 % 4 == 0, f / 8 % 2 == 1⟩, d)

def vizOp (op : Nat) (d : Dec) : Option ((String × String) × Dec) := do
  let (ms, d) ← readMaps d
  let (c, d) ← readVizCfg d
  let rv := !c.hide && ms.any fun m => (m.val? []).isSome
  let name :=
    if op == 85 then "viz_ascii"
    else if op == 86 then (if rv then "viz_mermaid_rv" else "viz_mermaid")
    else (if rv then "viz_phys_rv" else "viz_phys")
  if ms.any fun m => m.all (·.1.isEmpty) then
    some ((name, "skip:viz-no-root-node"), d)
  else
    let ret :=
      if op == 85 then esc (asciiText c ms)
      else if op == 86 then mermaidCanon c ms (withRoot := !rv)
      else mermaidValues c ms (withRoot := !rv)
    some ((name, if rv && op != 85 then ret ++ ";skip:viz-mermaid-root-value" else ret), d)

/-! ## `random` (ops 88–92; cargo feature `random`, enabled in the differential crate)

The module's distributions draw from a caller-supplied RNG, so their exact
output is the RNG's business.  What they promise, and what the ops check:

* `RandomTrie { size, pd, vd }` samples `size` (path, value) pairs, `pd` then
  `vd`, and `set_val_at`s them in order: with scripted `pd` / `vd` (cycling
  lists, `Replay` in `misc.rs`) the answer is exactly that fold.
* `FairTrieValue` returns one of the map's `(path, value)` pairs.  A root value
  is a value of the map, but the sampler counts it without ever visiting it and
  panics (finding `fair_trie_value_root_value`): maps with a root value render
  `skip:fair-value-root-value`.
* `DescendFirstTrieValue` with `unbiased_descend_first_policy` descends from
  the root to the **first** value on its way: a value no proper prefix of whose
  path holds a value.  The policy at a location with children is a choice over
  exactly its child bytes (`elements`, ascending).
* `FairTriePath` returns a location of the trie (the root or a prefix of a
  value's path) with the value there, if any.
* `DescendTriePath` with `unbiased_descend_last_policy` descends to a **leaf**
  (a location without children) and returns its value.  The policy at `q`:
  `db` = "q has children", `dx` over the child bytes, `dy` = the value at `q`.

Each answer is exact when the property leaves one candidate, else `in=1` (the
sample is a candidate; the crate side checks membership); `det=1`: two samples
from equally seeded `StdRng`s agree.

## `counters` (ops 93–94; cargo feature `counters`, enabled in the differential crate)

* `cow_counters` / `reset_cow_counters`: writes to a map whose nodes nobody
  else holds never clone (`cow_clones = 0`); after `clone()`, a write below the
  root clones at least one node (when the map had any node to share, i.e.
  something below its root); once the clone is dropped, writes are unshared
  again; always `cow_clones <= make_unique_calls`.  (The counters are global:
  other threads writing maps at the same time would disturb them; the trace
  runs one input at a time.)
* `Counters::new()` is all zero; `Counters::count_ocupancy` on a map with
  nodes counts at least one node and at least `nodes - 1` child items (every
  node but the root is some node's child item).  The per-depth histograms are
  node-layout statistics with no model, and the `print_*` functions write to
  stdout, which is the trace channel; they are not called.  `count_ocupancy`
  panics on a map without a root node (finding `count_ocupancy_no_root_node`):
  `skip:counters-no-root-node`.
-/

def showSample (p : Path) (v : Option Nat) : String :=
  hexPath p ++ ":" ++ (match v with | some v => toString v | none => "-")

/-- The root and every prefix of a value's path, in byte order. -/
def LMap.locations (m : LMap) : List Path :=
  dedupAdj ((m.flatMap fun (p, _) => (List.range (p.length + 1)).map p.take).mergeSort fun a b => !lexLt b a)

def LMap.sorted (m : LMap) : LMap := m.mergeSort fun a b => !lexLt b.1 a.1

def readPolicyPath (d : Dec) : Option (Path × Dec) := do
  let (q, d) ← d.path 5
  some (q.map fun b => vizAlpha.getD b.toNat 0, d)

def randomOp (op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  if op == 88 then do
    let (np, d) ← d.mod 6
    let (paths, d) ← Ints.many (fun d => d.path 5) (np + 1) d
    let (nv, d) ← d.mod 4
    let (vals, d) ← Ints.many Dec.u8 (nv + 1) d
    let (size, d) ← d.mod 16
    let (_seed, d) ← d.u8
    let m := (List.range size).foldl (fun (m : LMap) i =>
      m.set (paths.getD (i % paths.length) []) (vals.getD (i % vals.length) 0).toNat) []
    some (("random_trie", "[" ++ ",".intercalate (m.sorted.map fun (p, v) => showSample p (some v)) ++ "]"), d)
  else if op == 89 then do
    let (m, d) ← readSmallMap d
    let (_seed, d) ← d.u8
    if (m.val? []).isSome then some (("fair_trie_value", "skip:fair-value-root-value"), d)
    else
      let ans := match m with | [(p, v)] => showSample p (some v) | _ => "in=1"
      some (("fair_trie_value", ans ++ ",det=1"), d)
  else if op == 90 then do
    let (m, d) ← readSmallMap d
    let (_seed, d) ← d.u8
    let (q, d) ← readPolicyPath d
    let firsts := m.filter fun (p, _) => (List.range p.length).all fun k => (m.val? (p.take k)).isNone
    let ans := match firsts with | [(p, v)] => showSample p (some v) | _ => "in=1"
    let cs := m.children q
    let pol := if cs.isEmpty then "-" else hexPath cs
    some (("descend_first_value", ans ++ ",det=1;pol=" ++ pol), d)
  else if op == 91 then do
    let (m, d) ← readSmallMap d
    let (_seed, d) ← d.u8
    let ans := match m.locations with | [p] => showSample p (m.val? p) | _ => "in=1"
    some (("fair_trie_path", ans ++ ",det=1"), d)
  else do
    let (m, d) ← readSmallMap d
    let (_seed, d) ← d.u8
    let (q, d) ← readPolicyPath d
    let leaves := m.locations.filter fun l => (m.children l).isEmpty
    let ans := match leaves with | [p] => showSample p (m.val? p) | _ => "in=1"
    let cs := m.children q
    some (("descend_last_path", ans ++ ",det=1;db=" ++ showBool (!cs.isEmpty) ++ ",dx=" ++ hexPath cs ++
      ",dy=" ++ (match m.val? q with | some v => toString v | none => "-")), d)

def countersOp (op : Nat) (d : Dec) : Option ((String × String) × Dec) :=
  if op == 93 then do
    let (_rv, d) ← d.u8
    let (n, d) ← d.mod 8
    let (writes, d) ← Ints.many (fun d => do
      let (p, d) ← d.path 5
      let (_v, d) ← d.u8
      pure (p, d)) (n + 1) d
    let (_p, d) ← d.path 5
    let (_b, d) ← d.pathByte
    let (_v, d) ← d.u8
    let hasNode := writes.any (!·.isEmpty)
    some (("cow_counters", "unshared=0,shared=" ++ showBool hasNode ++ ",after_drop=0,le=1"), d)
  else do
    let (m, d) ← readSmallMap d
    let ret := if m.all (·.1.isEmpty) then "new=0,0;skip:counters-no-root-node"
      else "new=0,0;nodes>0=1,items>=nodes-1=1"
    some (("count_ocupancy", ret), d)

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
  else if op ≤ 87 then vizOp op d
  else if op ≤ 92 then randomOp op d
  else if op ≤ 94 then countersOp op d
  else
    some (("nop", "-"), d)

end UtilFuzz
end PathMapModel
