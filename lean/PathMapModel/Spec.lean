import PathMapModel.Map

/-!
# Specification

The definitions in `PathMap.lean`, `Zipper.lean`, `Write.lean` and `Map.lean` *are*
the formal semantics: each is a total, executable function whose docstring names
the `pathmap` item it specifies.  This module adds the two things a bare
definition does not give you.

## §1 Proved laws

Structural theorems about the cursor algebra — the identities a caller is
entitled to rely on when composing zipper movements.  These are proved, not
tested.

## §2 Checkable laws

Metamorphic properties relating *different* API functions: "`join` is
commutative", "`take_map` then `graft_map` is the identity", "`drop_head` undoes
`insert_prefix`".  They are written as decidable `Bool`-valued functions of a
state so that

* `#guard` can check them at build time on the fixture battery below, and
* the differential oracle can evaluate them on *every* state a fuzzer reaches,
  turning them into runtime assertions on the real crate as well.

A property that holds in the model but fails in `pathmap` is a crate bug; one
that fails in both is a spec bug.  Both are worth finding, which is why the
laws are kept separate from the definitions.
-/

namespace PathMapModel

/-! ## §1 Proved laws: the cursor algebra -/

namespace Zip
variable {V : Type} (z : Zip V)

@[simp] theorem focus_def : z.focus = z.root ++ z.path := rfl

@[simp] theorem path_descendTo (k : Path) : (z.descendTo k).path = z.path ++ k := rfl

@[simp] theorem trie_descendTo (k : Path) : (z.descendTo k).trie = z.trie := rfl

@[simp] theorem root_descendTo (k : Path) : (z.descendTo k).root = z.root := rfl

/-- Descending is a monoid action of paths on zippers. -/
@[simp] theorem descendTo_nil : z.descendTo [] = z := by
  simp [descendTo]

theorem descendTo_append (a b : Path) :
    z.descendTo (a ++ b) = (z.descendTo a).descendTo b := by
  simp [descendTo, List.append_assoc]

theorem focus_descendTo (k : Path) : (z.descendTo k).focus = z.focus ++ k := by
  simp [focus, descendTo, List.append_assoc]

/-- `origin_path = root_prefix_path ++ path`, as documented on `ZipperAbsolutePath`. -/
theorem origin_eq_root_append_path : z.rootPrefixPath ++ z.path = z.focus := rfl

@[simp] theorem atRoot_reset : z.reset.atRoot = true := by
  simp [reset, atRoot]

@[simp] theorem reset_idem : z.reset.reset = z.reset := rfl

/-- After `reset`, `origin_path = root_prefix_path`. -/
theorem focus_reset : z.reset.focus = z.rootPrefixPath := by
  simp [reset, focus, rootPrefixPath]

@[simp] theorem ascend_zero : z.ascend 0 = (0, z) := by
  simp [ascend]

/-- The count `ascend` reports is exactly the depth the focus lost.

This is the heart of the blind-zipper contract: a zipper with no `path()` learns
how far it moved only from this number, so it had better be exact. -/
theorem ascend_accounts (n : Nat) :
    ((z.ascend n).2).path.length + (z.ascend n).1 = z.path.length := by
  simp [ascend]
  omega

/-- Ascending exactly as far as you descended returns you to where you were, and
says so. -/
theorem ascend_descendTo (k : Path) :
    (z.descendTo k).ascend k.length = (k.length, z) := by
  simp [ascend, descendTo, Nat.add_sub_cancel]

/-- Ascending past the root stops at the root and reports the shortfall. -/
theorem ascend_overshoot {n : Nat} (h : z.path.length < n) :
    z.ascend n = (z.path.length, z.reset) := by
  simp [ascend, reset, Nat.min_eq_right (Nat.le_of_lt h)]

/-- Ascending never moves the focus below where it was. -/
theorem ascend_le (n : Nat) : ((z.ascend n).2).path.length ≤ z.path.length := by
  simp [ascend]

/-- Movement never changes the trie: the read API is pure. -/
@[simp] theorem trie_ascend (n : Nat) : ((z.ascend n).2).trie = z.trie := rfl

@[simp] theorem trie_reset : z.reset.trie = z.trie := rfl

/-- A fork sees the same location its parent was looking at, and is at its root. -/
@[simp] theorem focus_fork : z.forkReadZipper.focus = z.focus := by
  simp [forkReadZipper, focus]

@[simp] theorem atRoot_fork : z.forkReadZipper.atRoot = true := by
  simp [forkReadZipper, atRoot]

/-- `child_count` is the population count of `child_mask`, by construction. -/
@[simp] theorem childCount_eq : z.childCount = z.childMask.length := rfl

/-- `descend_to_byte` is `descend_to` with a one-byte key. -/
@[simp] theorem descendToByte_eq (b : UInt8) : z.descendToByte b = z.descendTo [b] := rfl

/-- `ascend_byte` is `ascend 1` compared against 1, as the trait now defines it. -/
@[simp] theorem ascendByte_eq :
    z.ascendByte = ((z.ascend 1).1 == 1, (z.ascend 1).2) := rfl

/-- `focus_byte` is the last byte of the relative path.

At the root the trait leaves this unspecified, and the model's answer there is
`none`; nothing may be concluded from it either way. -/
theorem focusByte_eq : z.focusByte = z.path.getLast? := rfl

end Zip

namespace Path

@[simp] theorem isPrefixOf_nil (p : Path) : ([] : Path) ≼ p := by
  simp [isPrefixOf]

@[simp] theorem isPrefixOf_refl (p : Path) : p ≼ p := by
  induction p with
  | nil => simp [isPrefixOf]
  | cons a as ih => simp [isPrefixOf, ih]

theorem isPrefixOf_append (p q : Path) : p ≼ (p ++ q) := by
  induction p with
  | nil => simp [isPrefixOf]
  | cons a as ih => simp [isPrefixOf, ih]

@[simp] theorem lt_irrefl (p : Path) : Path.lt p p = false := by
  induction p with
  | nil => simp [Path.lt]
  | cons a as ih => simp [Path.lt, ih]

end Path

namespace PathMap

/-- Every location carrying a value exists.

This used to be a runtime check in `Laws`, because the two-list representation
allowed a value to be recorded at a path that was not listed as existing, and
the constructors had to be trusted to keep the two in step.  With one list of
`(path, Option value)` the property is structural, so it is a theorem instead:
`vals` reads off a sublist of `entries`, and `paths` reads off all of them. -/
theorem mem_vals_pathExists {V : Type} (t : PathMap V) (kv : Path × V)
    (h : kv ∈ t.vals) : t.pathExists kv.1 = true := by
  simp only [vals, List.mem_filterMap] at h
  obtain ⟨p, _, hmap⟩ := h
  cases hc : (t.entryAt p).val with
  | none => simp [hc] at hmap
  | some v =>
    simp [hc] at hmap
    simpa [pathExists, ← hmap] using Entry.present_of_val hc

/-- Pruning can never remove more bytes than separate the focus from the
zipper's root: `prune_path` cannot prune above the root. -/
theorem pruneCount_le {V : Type} (t : PathMap V) (rootLen : Nat) (p : Path) :
    t.pruneCount rootLen p ≤ p.length - rootLen := by
  unfold pruneCount
  split
  · omega
  · split
    · omega
    · exact Nat.sub_le_sub_left (Nat.le_max_left _ _) _

end PathMap

/-! ## §2 Checkable laws

Each law takes the data it needs and returns `true` when it holds.  `LawReport`
bundles them so the oracle can report exactly which one broke. -/

namespace Laws

variable {V : Type}

/-- Every location carrying a value exists.

Kept as a runtime check only to guard the *fixtures*: it is now structurally
true of any `PathMap` (see `PathMap.mem_vals_pathExists`), so a failure here would
mean a fixture was built by hand rather than through the constructors. -/
def valsExist (t : PathMap V) : Bool :=
  t.vals.all (fun kv => t.pathExists kv.1)

/-- The set of existing locations is closed under taking prefixes. -/
def prefixClosed (t : PathMap V) : Bool :=
  t.paths.all (fun q => (Path.prefixes q).all (fun r => t.pathExists r))

/-- `child_mask` lists exactly the bytes whose child location exists. -/
def childMaskAgrees (t : PathMap V) (p : Path) : Bool :=
  (t.childMask p).all (fun b => t.pathExists (p ++ [b])) &&
  t.paths.all (fun q =>
    match Path.stripPrefix p q with
    | some [b] => (t.childMask p).contains b
    | _ => true)

/-- `val_count` at the root counts exactly the entries of `iter`. -/
def valCountAgrees (t : PathMap V) : Bool := t.valCount [] == t.vals.length

/-- After `set_val` the focus is a location carrying exactly that value.

One `Entry` case, rather than "the value is `v`" and "the path exists"
checked separately — the second was only there because the first could not say
it. -/
def setValThenVal (ops : ValOps V) (z : Zip V) (v : V) : Bool :=
  match ((z.setVal v).2).entry with
  | .valued w => ops.beq w v
  | .bare | .absent => false

/-- `remove_val` clears the value but leaves the location dangling — which is
to say the focus ends up exactly `.bare`. -/
def removeValLeavesPath (z : Zip V) : Bool :=
  if z.pathExists then ((z.removeVal false).2).entry matches .bare else true

/-- `create_path` makes the focus exist; a second call reports "already there". -/
def createPathIdempotent (z : Zip V) : Bool :=
  if z.atRoot then true
  else
    let (_, z1) := z.createPath
    let (c2, z2) := z1.createPath
    z1.pathExists && !c2 && z2.pathExists

/-- `prune_path` undoes a `create_path` that dangled off an existing location. -/
def createThenPrune (ops : ValOps V) (z : Zip V) : Bool :=
  if z.atRoot || z.pathExists then true
  else
    let (_, z1) := z.createPath
    let (_, z2) := z1.prunePath
    PathMap.beqT ops z2.trie z.trie

/-- `descend_to_existing` always lands on an existing location, provided the
focus existed when it was called. -/
def descendToExistingLands (z : Zip V) (k : Path) : Bool :=
  if z.pathExists then (z.descendToExisting k).2.pathExists else true

/-- `descend_indexed_byte` lands on an existing location for every valid index,
and the byte it reports is the byte it landed on. -/
def descendIndexedLands (z : Zip V) : Bool :=
  (List.range z.childCount).all (fun i =>
    match z.descendIndexedByte i with
    | (some b, z') => z'.pathExists && z'.focusByte == some b
    | (none, _) => false)

/-- `to_next_sibling_byte` and `to_prev_sibling_byte` are mutually inverse —
**but only from an existing location**.

From an off-trie focus the round trip fails, and correctly so: the sibling
moves are defined by the parent's `child_mask`, which does not contain the
current byte, so `next_bit` jumps to some larger set byte and `prev_bit` comes
back to a *different* one.  A caller that steps sideways from a non-existent
path cannot expect to step back. -/
def siblingRoundTrip (z : Zip V) : Bool :=
  if !z.pathExists then true
  else
    match z.toNextSiblingByte with
    | (none, _) => true
    | (some b, z') =>
        z'.focusByte == some b &&
          (match z'.toPrevSiblingByte with
           | (some _, z'') => z''.path == z.path
           | (none, _) => false)

/-- `descend_until_observed` reports exactly the bytes it descended.

A blind zipper has no `path()`, so this sequence is its only account of where it
went; it must equal the path delta. -/
def descendUntilObservedExact (z : Zip V) : Bool :=
  let (moved, obs, z') := z.descendUntilObserved
  (z'.path == z.path ++ obs) && (moved == !obs.isEmpty)

/-- `ascend_until` never ascends past the zipper's root, and reports the exact
distance travelled. -/
def ascendUntilAccounts (z : Zip V) : Bool :=
  let (n, z') := z.ascendUntil
  z'.path.length + n == z.path.length && z.path.length ≥ n

/-- `to_next_val` enumerates values in strictly increasing depth-first order and
finishes at the root. -/
def toNextValMonotone (z : Zip V) : Bool :=
  let (moved, z') := z.toNextVal
  if moved then Path.lt z.path z'.path && z'.isVal else z'.atRoot

/-- `join` is commutative **on locations**, but not on values.

`pathmap`'s `u64` (and `usize`, `u32`, `u16`, `u8`) `Lattice` instances define
`pjoin` as `Identity(SELF_IDENT)` — a left-biased projection.  So joining two
maps that disagree at a key keeps whichever value belongs to the receiver, and
`a.join(b)` and `b.join(a)` differ.  The *set of paths* is still symmetric, and
that is what this law asserts.  Any test that assumes value-level commutativity
is asserting something the crate does not promise for these value types. -/
def joinCommOnPaths (ops : ValOps V) (a b : PathMap V) : Bool :=
  (PathMap.join ops a b).paths == (PathMap.join ops b a).paths &&
  (PathMap.join ops a b).vals.map (·.1) == (PathMap.join ops b a).vals.map (·.1)

/-- `join` is idempotent. -/
def joinIdem (ops : ValOps V) (a : PathMap V) : Bool :=
  PathMap.beqT ops (PathMap.join ops a a) a

/-- `join` is associative, values included: left-biasing is itself associative. -/
def joinAssoc (ops : ValOps V) (a b c : PathMap V) : Bool :=
  PathMap.beqT ops (PathMap.join ops (PathMap.join ops a b) c) (PathMap.join ops a (PathMap.join ops b c))

/-- `meet` is idempotent *on values*.  It is not idempotent on locations: a meet
discards dangling paths, so `meet a a` keeps only the value-bearing skeleton. -/
def meetIdemOnVals (ops : ValOps V) (a : PathMap V) : Bool :=
  (PathMap.meet ops a a).vals.map (·.1) == a.vals.map (·.1)

/-- Subtracting a map from itself leaves no values. -/
def subSelfEmptyVals (ops : ValOps V) (a : PathMap V) : Bool :=
  (PathMap.sub ops a a).vals.isEmpty

/-- `restrict a a = a`: every path of `a` is validated by the value at its own
end (or by the root value).  This is the law that caught a real `prestrict`
bug — see `tests/pathmap_algebra_differential.rs`. -/
def restrictSelf (ops : ValOps V) (a : PathMap V) : Bool :=
  PathMap.beqT ops (Map.restrict a a) a

/-- `take_map` followed by `graft_map` restores the trie exactly. -/
def takeThenGraft (ops : ValOps V) (z : Zip V) : Bool :=
  let (m, z1) := z.takeMap false
  let z2 := z1.graftMap (m.getD PathMap.empty)
  PathMap.beqT ops z2.trie z.trie

/-- Grafting one subtrie into two places makes two *independent* copies:
writing under one leaves the other exactly as it was.

In the model this cannot fail — a `PathMap` is a flat list of entries, so the two
copies are separate elements and there is no aliasing to leak through.  The law
is stated anyway for two reasons: it is what the crate must do (`graft` clones a
refcounted pointer, so the copies really are shared until copy-on-write
separates them), and it would catch a model that grew sharing of its own.

See FINDINGS.md #16: the crate gets this right where it completes, but aborts
when the shared subtrie contains a dangling path. -/
def graftedCopiesIndependent (ops : ValOps V) (s : PathMap V)
    (a b k : Path) (v : V) : Bool :=
  let at_ := fun (t : PathMap V) (p : Path) => ({ trie := t, root := [], path := p } : Zip V)
  let one := ((at_ PathMap.empty a).graftMap s).trie
  let both := ((at_ one b).graftMap s).trie
  let after := (((at_ both (a ++ k)).setVal v).2).trie
  PathMap.beqT ops (both.subtrie b) (after.subtrie b)

/-- `graft` copies the source subtrie: after grafting, `make_map` at the
destination equals `make_map` at the source. -/
def graftThenMakeMap (ops : ValOps V) (dst src : Zip V) : Bool :=
  PathMap.beqT ops (dst.graft src).makeMap src.makeMap

/-- `drop_head k` undoes `insert_prefix` of a `k`-byte prefix, as documented on
`ZipperWriting::insert_prefix`.

Only the *branches* are compared: `insert_prefix` does not move the focus value,
and `drop_head` discards values at depth exactly `k`, so the focus value plays no
part on either side. -/
def dropHeadUndoesInsertPrefix (ops : ValOps V) (z : Zip V) (pre : Path) : Bool :=
  if z.focusNodeIsEmpty || pre.isEmpty then true
  else
    let (_, z1) := z.insertPrefix pre
    let (_, z2) := z1.joinKPathInto ops pre.length false
    PathMap.beqT ops z2.focusNode z.focusNode

/-- `join_into` with an empty source is a no-op and reports `Identity`
(or `None` when the destination is empty too). -/
def joinEmptyIdentity (ops : ValOps V) (z : Zip V) : Bool :=
  let src : Zip V := { trie := PathMap.empty, root := [], path := [] }
  let (st, z') := z.joinInto ops src
  PathMap.beqT ops z'.trie z.trie &&
    (st == (if z.focusNodeIsEmpty then AlgStatus.none else AlgStatus.identity))

/-- Joining a zipper into itself is the identity, and reports it. -/
def joinSelfIdentity (ops : ValOps V) (z : Zip V) : Bool :=
  let (st, z') := z.joinInto ops z
  PathMap.beqT ops z'.trie z.trie &&
    (st == (if z.focusNodeIsEmpty then AlgStatus.none else AlgStatus.identity))

/-- `remove_branches` empties the focus but preserves its value. -/
def removeBranchesKeepsVal (ops : ValOps V) (z : Zip V) : Bool :=
  let (_, z') := z.removeBranches false
  z'.focusNodeIsEmpty &&
    (match z.val, z'.val with
     | none, none => true
     | some a, some b => ops.beq a b
     | _, _ => false)

/-- `remove_unmasked_branches` with a full mask changes nothing. -/
def removeUnmaskedFullMask (ops : ValOps V) (z : Zip V) : Bool :=
  let full := ByteMask.ofList ((List.range 256).map (fun i => UInt8.ofNat i))
  PathMap.beqT ops (z.removeUnmaskedBranches full false).trie z.trie

/-- `remove_unmasked_branches` with an empty mask equals `remove_branches`. -/
def removeUnmaskedEmptyMask (ops : ValOps V) (z : Zip V) : Bool :=
  PathMap.beqT ops (z.removeUnmaskedBranches [] false).trie (z.removeBranches false).2.trie

end Laws
end PathMapModel
