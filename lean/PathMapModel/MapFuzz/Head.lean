import PathMapModel.MapFuzz.Base

/-!
# Map fuzzer, ops 60–69: ZipperHead sessions

`src/zipper_head.rs`, `src/zipper_tracking.rs`.  The Rust side is
`differential/src/mapfuzz/head.rs`.  Op 60 runs one decoded *session*: a
`ZipperHead` on (a clone of) `m[i]`, several zippers opened from it, used,
dropped, and the map written back when the session ends.

## The head (operand `mode = u8 % 3`)

* `0`: `m.zipper_head()`; head root `b = []`.
* `1`: `m.into_zipper_head(base)` (`base : path(4)`), a `ZipperHeadOwned`,
  turned back into the map with `into_map`; `b = base`.
* `2`: `m.write_zipper_at_path(r)` moved to `f` (`r, f : path(3)`), then
  `zipper_head()` at its focus; `b = r ++ f`.  After the head is dropped the
  write zipper is used once more (`post : u8`; odd: `descend_to_byte((post >> 1) % 4)`,
  `set_val(post >> 3)`, reported as `post=<old>`): a head must leave its parent
  where it was.

Every zipper path is relative to `b`.

## Steps (`n := u8 % 10`, then `n × (kind := u8 % 12 ; operands)`)

| kind | step | operands | reports |
|---|---|---|---|
| 0 | `read_zipper_at_path` | `path(5)` | `o<slot>` / conflict |
| 1 | `read_zipper_at_borrowed_path` | `path(5)` | same |
| 2 | `write_zipper_at_exclusive_path` | `path(5)` | same |
| 3 | `…_with_buffer` (the held buffer, if any; else as 2) | `path(5)` | same |
| 4 | `read_zipper_at_path_unchecked` / `write_…_unchecked` | `writer : bool`, `path(5)` | `o<slot>` |
| 5 | drop slot `k` | `k := u8` (see `pick`) | `d` |
| 6 | through writer `k`: `reset; descend_to(rel)`, then `sub`: 0 `set_val(v)`, 1 `remove_val(v odd)`, 2 `remove_branches(v odd)`, 3 `create_path` | `k, sub := u8 % 4, rel : path(3), v : u8` | `s<old>` `r<old>` `b<0/1>` `c<0/1>` |
| 7 | read slot `k` from its root | `k` | `e<path_exists>[<dump>]` |
| 8 | `cleanup_write_zipper` on writer `k` | `k` | `cl` |
| 9 | writer `k`: `into_read_zipper`; reader `k`: `clone` into a new slot | `k` | `cv` / `k<slot>` |
| 10 | a nested session (`n := u8 % 6`, no further nesting) on writer `k`'s `zipper_head()` | `k` | `[<steps>]` |
| 11 | writer `k`: `into_zipper_buffer`, held for the next kind 3 | `k` | `buf` |

Slot operands are a byte `k` resolved by `pick` (among the live slots, or the
live writers for writer-only steps).  A step that lands on an empty slot, or a
slot of the wrong kind, reports `-` and
does nothing (a nested session's steps are then not decoded).  There are 8
slots; an open takes the lowest free one (`full` when there is none).  Slots
still live at the end are dropped in slot order.

## Semantics

* **Conflicts.**  A path is *locked* by each live tracked zipper.  A new writer
  at `p` conflicts with any writer or reader whose path is a prefix of `p`, equal
  to it, or an extension of it; a new reader only with writers (readers share).
  Writers are checked first.  The reported location: the *shortest* lock that is
  a prefix of (or equal to) `p`, if any; otherwise the depth-first-*first* lock
  below `p`.  `C:W@<path>` for a writer, `C:R<count>@<path>` for readers, where
  the count is how many readers hold that exact path.  A failed open changes
  nothing.
* **What zippers see.**  Readers and writers never overlap, so a reader's view
  is the current map at `b ++ p`: it sees every write made before it was opened,
  and nothing changes under it while it lives.  A writer edits the map at
  `b ++ p` through the ordinary write-zipper model (`Write.lean`), and its
  writes are in the map the moment they are made.
* **Opening a writer creates its path** (`b ++ p` exists afterwards, dangling
  unless it holds something): the documented reason `cleanup_write_zipper`
  exists.  Opening a reader creates nothing.
* `cleanup_write_zipper(w)` drops `w` and then prunes the dangling chain ending
  at `b ++ p`, never above the head's root `b` (`PathMap.prunePath`).
* `into_read_zipper` turns the writer's lock into a reader lock on the same path;
  a cloned reader holds one more reader lock.  `into_zipper_buffer` releases the
  lock without pruning.
* **`_unchecked` zippers** are not tracked in release builds; the caller promises
  there is no conflict for their lifetime.  The harness keeps that promise with
  its own rule (`uncheckedClash`): an open that would conflict with a live
  unchecked zipper, or an unchecked open that would conflict with any live
  zipper, is skipped as `skip:unchecked-conflict`.  `into_read_zipper` on an
  unchecked writer panics in release (it unwraps the absent tracker) and is
  skipped as `skip:unchecked-into-read`; see lean/findings/map-morph.md.
* After the session the Rust side rebuilds the map from scratch, location by
  location (`rebuild`, the identity on meaning, so nothing here): a session
  leaves representation behind (an empty `CellByteNode` stump from a writer
  dropped without cleanup; an empty node under a leaf a reader was opened at)
  that later `remove`s mishandle (lean/findings/map-morph.md), which would
  otherwise surface in every later op.
* A nested session runs on writer `k`'s `zipper_head()`, whose root is that
  writer's focus (`b ++ p ++ rel` of its last write step, or its root after a
  read); it has its own tracker.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V Dec hexPath showVal showBool dumpAt)

namespace Head

structure Slot where
  writer : Bool
  unchecked : Bool
  /-- Relative to the head. -/
  p : Path
  /-- A writer's focus, relative to its root. -/
  focus : Path := []

def slotCap : Nat := 8

structure HS where
  m : PathMap V
  b : Path
  /-- `false` for a head taken from a write zipper whose focus is below its
  root: `cleanup_write_zipper` is skipped there (`skip:cleanup-off-root`; it
  resolves the path against the parent's root, lean/findings/map-morph.md). -/
  cleanupOk : Bool := true
  slots : List (Option Slot) := List.replicate slotCap none
  buf : Bool := false

def skipUncheckedConflict : String := "skip:unchecked-conflict"
def skipUncheckedIntoRead : String := "skip:unchecked-into-read"
def skipHeadRootAbsent : String := "skip:head-root-absent"
def skipCleanupOffRoot : String := "skip:cleanup-off-root"

/-- The slot a step names: byte `k` picks among the live slots (live writers,
for a writer-only step) in slot order; with none, slot 0, which the step then
finds empty or of the wrong kind. -/
def pick (l : List (Option Slot)) (k : Nat) (writers : Bool) : Nat :=
  let live := (List.range l.length).filter fun i =>
    match l[i]?.join with
    | some s => !writers || s.writer
    | none => false
  if live.isEmpty then 0 else live[k % live.length]!

def freeSlot (l : List (Option Slot)) : Option Nat := l.findIdx? (·.isNone)

def related (p q : Path) : Bool := (p ≼ q) || (q ≼ p)

/-- The harness's promise-keeping rule for `_unchecked` zippers. -/
def uncheckedClash (l : List (Option Slot)) (p : Path) (writer unchecked : Bool) : Bool :=
  l.any fun
    | some s => (unchecked || s.unchecked) && (writer || s.writer) && related s.p p
    | none => false

/-- The paths a tracker holds for one kind (with multiplicity). -/
def locks (l : List (Option Slot)) (writer : Bool) : List Path :=
  l.filterMap fun
    | some s => if s.writer == writer && !s.unchecked then some s.p else none
    | none => none

/-- The lock a new zipper at `p` runs into: the shortest one at or above `p`,
else the depth-first-first one below it. -/
def firstConflict (ls : List Path) (p : Path) : Option Path :=
  let pick (better : Path → Path → Bool) (xs : List Path) : Option Path :=
    xs.foldl (fun acc q => match acc with
      | none => some q
      | some a => if better q a then some q else some a) none
  match pick (fun q a => q.length < a.length) (ls.filter (· ≼ p)) with
  | some q => some q
  | none => pick (fun q a => Path.lt q a) (ls.filter (fun q => (p ≼ q) && q != p))

def conflict (l : List (Option Slot)) (p : Path) (writer : Bool) : Option String :=
  match firstConflict (locks l true) p with
  | some q => some ("C:W@" ++ hexPath q)
  | none =>
      if !writer then none else
      let rs := locks l false
      match firstConflict rs p with
      | some q => some ("C:R" ++ toString (rs.filter (· == q)).length ++ "@" ++ hexPath q)
      | none => none

/-- Writer slot `s` as a write zipper on the current map. -/
def wzOf (h : HS) (s : Slot) (rel : Path) : Zip V := { trie := h.m, root := h.b ++ s.p, path := rel }

/-- Run a session: head root, whether cleanup is allowed, map, input. -/
abbrev Nest := Path → Bool → PathMap V → Dec → Option (String × PathMap V × Dec)

def runStep (nest : Option Nest) (h : HS) (d : Dec) : Option (String × HS × Dec) := do
  let (kind, d) ← d.mod 12
  match kind with
  | 0 | 1 | 2 | 3 | 4 =>
      let (writer, unchecked, d) ←
        if kind ≤ 1 then some (false, false, d)
        else if kind ≤ 3 then some (true, false, d)
        else do let (w, d) ← d.bool; some (w, true, d)
      let (p, d) ← d.path 5
      -- `skip:head-root-absent`: a reader from a head whose root does not exist
      -- creates the root (lean/findings/map-morph.md); skipped so the stray path
      -- does not contaminate the rest.
      if !writer && !h.m.pathExists h.b then some (skipHeadRootAbsent, h, d) else
      if uncheckedClash h.slots p writer unchecked then some (skipUncheckedConflict, h, d) else
      match freeSlot h.slots with
      | none => some ("full", h, d)
      | some ix =>
          -- kind 3 takes the held buffer whether or not the open succeeds
          let h := if kind == 3 then { h with buf := false } else h
          match (if unchecked then none else conflict h.slots p writer) with
          | some e => some (e, h, d)
          | none =>
              let m := if writer then h.m.addPath (h.b ++ p) else h.m
              some ("o" ++ toString ix,
                { h with m, slots := h.slots.set ix (some { writer, unchecked, p }) }, d)
  | 5 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat false
      match h.slots[k]?.join with
      | some _ => some ("d", { h with slots := h.slots.set k none }, d)
      | none => some ("-", h, d)
  | 6 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat true
      let (sub, d) ← d.mod 4
      let (rel, d) ← d.path 3
      let (v, d) ← d.val
      match h.slots[k]?.join with
      | some s =>
          if !s.writer then some ("-", h, d) else
          let z := wzOf h s rel
          let prune := v.toNat % 2 == 1
          let (r, z) := match sub with
            | 0 => let (o, z) := z.setVal v; ("s" ++ showVal o, z)
            | 1 => let (o, z) := z.removeVal prune; ("r" ++ showVal o, z)
            | 2 => let (o, z) := z.removeBranches prune; ("b" ++ showBool o, z)
            | _ => let (o, z) := z.createPath; ("c" ++ showBool o, z)
          some (r, { h with m := z.trie, slots := h.slots.set k (some { s with focus := rel }) }, d)
      | none => some ("-", h, d)
  | 7 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat false
      match h.slots[k]?.join with
      | some s =>
          let at_ := h.b ++ s.p
          some ("e" ++ showBool (h.m.pathExists at_) ++ "[" ++ dumpAt h.m at_ ++ "]",
            { h with slots := h.slots.set k (some { s with focus := [] }) }, d)
      | none => some ("-", h, d)
  | 8 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat true
      match h.slots[k]?.join with
      | some s =>
          if !s.writer then some ("-", h, d) else
          if !h.cleanupOk then some (skipCleanupOffRoot, h, d) else
          some ("cl", { h with m := (h.m.prunePath h.b.length (h.b ++ s.p)).2,
                               slots := h.slots.set k none }, d)
      | none => some ("-", h, d)
  | 9 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat false
      match h.slots[k]?.join with
      | some s =>
          if s.writer then
            if s.unchecked then some (skipUncheckedIntoRead, h, d)
            else some ("cv", { h with slots := h.slots.set k (some { s with writer := false }) }, d)
          else
            match freeSlot h.slots with
            | some ix => some ("k" ++ toString ix,
                { h with slots := h.slots.set ix (some { s with focus := [] }) }, d)
            | none => some ("full", h, d)
      | none => some ("-", h, d)
  | 10 => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat true
      match h.slots[k]?.join, nest with
      | some s, some run =>
          if !s.writer then some ("-", h, d) else
          let (r, m, d) ← run (h.b ++ s.p ++ s.focus) s.focus.isEmpty h.m d
          some ("[" ++ r ++ "]", { h with m }, d)
      | _, _ => some ("-", h, d)
  | _ => do
      let (kb, d) ← d.u8
      let k := pick h.slots kb.toNat true
      match h.slots[k]?.join with
      | some s =>
          if !s.writer then some ("-", h, d) else
          some ("buf", { h with slots := h.slots.set k none, buf := true }, d)
      | none => some ("-", h, d)

def runSteps (nest : Option Nest) : Nat → HS → Dec → Option (List String × HS × Dec)
  | 0, h, d => some ([], h, d)
  | n + 1, h, d => do
      let (r, h, d) ← runStep nest h d
      let (rs, h, d) ← runSteps nest n h d
      some (r :: rs, h, d)

/-- A nested session (no further nesting). -/
def inner : Nest := fun b cleanupOk m d => do
  let (n, d) ← d.mod 6
  let (rs, h, d) ← runSteps none n { m, b, cleanupOk } d
  some (String.intercalate " " rs, h.m, d)

/-- A top-level session. -/
def outer : Nest := fun b cleanupOk m d => do
  let (n, d) ← d.mod 10
  let (rs, h, d) ← runSteps (some inner) n { m, b, cleanupOk } d
  some (String.intercalate " " rs, h.m, d)

end Head

open Head in
def stepHead (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 60 => do
      let (i, d) ← d.map
      let (mode, d) ← d.mod 3
      let t := s.get i
      match mode with
      | 0 =>
          let (r, m, d) ← outer [] true t d
          some (("head", "m0 " ++ r, s.set i m), d)
      | 1 =>
          let (base, d) ← d.path 4
          let (r, m, d) ← outer base true t d
          some (("head", "m1 " ++ r, s.set i m), d)
      | _ =>
          let (r0, d) ← d.path 3
          let (f, d) ← d.path 3
          let (post, d) ← d.u8
          let (r, m, d) ← outer (r0 ++ f) f.isEmpty t d
          let (pr, m) :=
            if post.toNat % 2 == 1 then
              let (o, m) := m.setVal (r0 ++ f ++ [UInt8.ofNat ((post.toNat / 2) % 4)])
                (UInt64.ofNat (post.toNat / 8))
              (showVal o, m)
            else ("-", m)
          some (("head", "m2 " ++ r ++ " post=" ++ pr, s.set i m), d)
  | _ => some (("nop", "-", s), d)

end MapFuzz
end PathMapModel
