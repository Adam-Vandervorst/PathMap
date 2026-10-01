import PrunedModel.Write

/-!
# What this model claims

`PathMapModel/Spec.lean` has to say, operation by operation, which valueless
locations survive it.  This model has a single claim instead, and everything
else is a consequence.

**There is no dangling path.**  A location that exists with nothing below it
carries a value — not as an invariant the constructors maintain, but because
existence is *defined* as "some key runs through here".  `no_dangling` is the
proof, and its shortness is the measure of what dropping the `Option` buys.

The consequence the fuzzer trades on: `prune_path` has nothing to do, so the
crate must report `0` for it on any trie built from this subset.  Each time it
does not, some operation in the subset leaked a location that leads nowhere.

The `#guard`s at the end are the executable half — small concrete tries run
through the definitions and checked at elaboration time.  They catch the class
of mistake that type-checks right through: a swapped argument order, a `take`
that should have been a `drop`.
-/

namespace PrunedModel
namespace PrunedMap

open PathMapModel

variable {V : Type}

/-! ## Keys and lookup -/

/-- Every path is a prefix of itself. -/
theorem isPrefixOf_self : ∀ p : Path, (p ≼ p) = true
  | [] => rfl
  | _ :: as => by simp [Path.isPrefixOf, isPrefixOf_self as]

/-- A key is bound: `lookup` finds whatever `map (·.1)` saw. -/
theorem lookup_isSome_of_mem_keys {l : List (Path × V)} {p : Path}
    (h : p ∈ l.map (·.1)) : (l.lookup p).isSome = true := by
  obtain ⟨kv, hmem, heq⟩ := List.mem_map.mp h
  exact List.lookup_isSome_iff.mpr ⟨kv, hmem, by simp [heq]⟩

/-- …and conversely, `lookup` only succeeds on a key. -/
theorem mem_keys_of_lookup_isSome {l : List (Path × V)} {p : Path}
    (h : (l.lookup p).isSome = true) : p ∈ l.map (·.1) := by
  obtain ⟨kv, hmem, hb⟩ := List.lookup_isSome_iff.mp h
  exact List.mem_map.mpr ⟨kv, hmem, (eq_of_beq hb).symm⟩

/-- Holding a value entails existing. -/
theorem pathExists_of_valAt {t : PrunedMap V} {p : Path} {v : V}
    (h : t.valAt p = some v) : t.pathExists p = true := by
  have hmem : p ∈ t.keys :=
    mem_keys_of_lookup_isSome (l := t.entries) (p := p)
      (show (t.entries.lookup p).isSome = true by
        rw [show t.entries.lookup p = some v from h]; rfl)
  cases hp : p.isEmpty with
  | true => simp [pathExists, hp]
  | false =>
      simp only [pathExists, hp, Bool.false_or, List.any_eq_true]
      exact ⟨p, hmem, isPrefixOf_self p⟩

/-! ## The claim -/

/-- **No dangling paths.**  A location that some key runs through, and that has
nothing strictly below it, carries a value.

`pathExists` admits the root unconditionally — `PathMap::new().read_zipper()`
reports `path_exists() == true`, and the root of an empty trie is the one
location that exists without leading anywhere — so the hypothesis here is its
other disjunct.  Together with "nothing strictly below `p`", the key running
through `p` can only be `p` itself. -/
theorem no_dangling {t : PrunedMap V} {p : Path}
    (hx : t.keys.any (fun k => p ≼ k) = true) (hb : t.belowIsEmpty p = true) :
    (t.valAt p).isSome = true := by
  obtain ⟨k, hk, hpk⟩ := List.any_eq_true.mp hx
  have hkp : k == p := by simpa [hpk] using (List.all_eq_true.mp hb) k hk
  exact lookup_isSome_of_mem_keys (by simpa [keys, eq_of_beq hkp] using hk)

/-- Hence `prune_path` has nothing to prune, and reports `0`… -/
theorem prunePath_eq_zero (t : PrunedMap V) (p : Path) : (t.prunePath p).1 = 0 := rfl

/-- …and leaves the trie alone. -/
theorem prunePath_id (t : PrunedMap V) (p : Path) : (t.prunePath p).2 = t := rfl

/-- The empty trie has no values, so `is_empty` and "no keys" coincide. -/
theorem isEmptyMap_empty : (empty : PrunedMap V).isEmptyMap = true := rfl

/-- The root of the empty trie still exists — the one location that does. -/
theorem pathExists_root (t : PrunedMap V) : t.pathExists [] = true := by
  simp [pathExists]

/-! ## Executable checks

Concrete tries, run through the definitions at elaboration time.  `t1` branches
at the root and carries a value at an interior location; `t2` is a single chain
beside a single leaf, which is the shape every dangling-path question is about. -/

section Guards

private def t1 : PrunedMap UInt64 := mk' [([0, 1], 7), ([0], 3), ([2], 9)]
private def t2 : PrunedMap UInt64 := mk' [([0, 1, 2], 5), ([3], 7)]

-- Canonical form: sorted depth-first, so a prefix precedes its extensions.
#guard t1.keys == [[0], [0, 1], [2]]
#guard t1.paths == [[], [0], [0, 1], [2]]
#guard t1.valAt [0] == some 3
#guard t1.valAt [1] == none
#guard t1.valCount [] == 3 && t1.valCount [0] == 2
#guard t1.childMask [] == ([0, 2] : List UInt8)
#guard t1.childCount [0] == 1 && t1.childCount [0, 1] == 0

-- Existence is the prefix closure of the keys, and nothing more.
#guard t1.pathExists [0, 1] && !t1.pathExists [1] && !t1.pathExists [0, 1, 2]
#guard t2.pathExists [0] && t2.pathExists [0, 1] && !t2.pathExists [0, 2]

-- `no_dangling`, concretely: the one location with nothing below it is valued.
#guard t1.belowIsEmpty [0, 1] && (t1.valAt [0, 1]).isSome

-- Removing a value removes the chain that existed only to reach it…
#guard (t2.removeVal [0, 1, 2]).2.keys == [[3]]
#guard !(t2.removeVal [0, 1, 2]).2.pathExists [0]
-- …but not a location some other key still runs through.
#guard (t1.removeVal [0]).2.keys == [[0, 1], [2]] && (t1.removeVal [0]).2.pathExists [0]

-- `set_val` reports the value it replaced.
#guard (t1.setVal [0] 11).1 == some 3 && (t1.setVal [0] 11).2.valAt [0] == some 11
#guard (t1.setVal [5] 11).1 == none && (t1.setVal [5] 11).2.keys == [[0], [0, 1], [2], [5]]

-- Grafting an empty node below a *valued* location keeps the location…
#guard (t1.graftBelow [0] empty).keys == [[0], [2]]
-- …and below a valueless one takes the whole chain with it.  This is the
-- model's central disagreement with `pathmap` 0.4.0, which leaves `[0]` and
-- `[0,1]` behind as dangling paths.
#guard (t2.graftBelow [0, 1] empty).keys == [[3]]
#guard !(t2.graftBelow [0, 1] empty).pathExists [0]

-- Sub-tries carry the focus value as their root value.
#guard (t1.subtrie [0]).keys == [[], [1]] && (t1.subtrie [0]).valAt [] == some 3
#guard (t1.subtrie [9]).isEmptyMap

-- Algebra.  `u64`'s `psubtract` annihilates on equal values, and its `pjoin`
-- and `pmeet` are left-biased projections.
#guard (sub u64Ops t1 t1).isEmptyMap
#guard (sub u64Ops t1 (mk' [([0], 3)])).keys == [[0, 1], [2]]
#guard (meet u64Ops t1 t1).keys == t1.keys
#guard (meet u64Ops t1 (mk' [([0], 99)])).entries == [([0], 3)]
#guard (join u64Ops t1 empty).entries == t1.entries
#guard (join u64Ops (mk' [([0], 1)]) (mk' [([2], 4)])).entries == [([0], 1), ([2], 4)]

-- `prestrict` validates on a non-empty prefix only, so the root value of the
-- filter is invisible at node level.
#guard (restrictBelowRoot t1 (mk' [([0], 1)])).keys == [[0], [0, 1]]
#guard (restrictBelowRoot t1 (mk' [([], 1)])).isEmptyMap

-- `drop_head` discards the values sitting at depth exactly `k`: `[3]` is at
-- depth 1, so its value has nowhere to go in the joined node.
#guard (dropHead u64Ops t2 1).entries == [([1, 2], 5)]
#guard (dropHead u64Ops t2 0).entries == t2.entries

-- A write zipper at the map root, as the fuzzer builds it.
private def z2 : PZip UInt64 := { trie := t2, root := [], path := [0, 1] }

-- `remove_branches` at a valueless focus takes the focus with it: it has no
-- value of its own and now nothing below, so it stops existing.
#guard (PZip.removeBranches z2).1 && (PZip.removeBranches z2).2.trie.keys == [[3]]
-- Nothing to prune afterwards, which is what the crate is checked against.
#guard (PZip.prunePath (PZip.removeBranches z2).2).1 == 0
-- `remove_val` at a location with no value is a no-op, flag and all.
#guard (PZip.removeVal z2).1 == none && (PZip.removeVal z2).2.trie.entries == t2.entries

end Guards

end PrunedMap
end PrunedModel
