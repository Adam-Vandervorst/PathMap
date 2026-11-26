import PathMapModel.Source

/-!
# The owned zippers (`--source owned`)

`differential/src/sources/owned.rs`: the write zipper is
`map0.into_write_zipper(root0)` (`WriteZipperOwned`), the read zipper
`map1.into_read_zipper(root1)` (`ReadZipperOwned`) or its `clone()`.  They are
native zippers that own their map, so the view and the capabilities are the
native ones (`ReadZipperOwned`, like `ReadZipperTracked`, has the witness forms
of the read-only value traits; see `Sources/Head.lean`).

What is new is the ownership plumbing, which extra lines after `ROOT1` check:

* `ITER0` — `IntoIterator for WriteZipperOwned`, from a clone reset to its root:
  every value below the zipper root, depth-first (= lexicographic), with paths
  relative to the root.  At most 64.
* `ITERF` — the same iterator from a clone at `wz`'s focus.  `OwnedZipperIter`
  yields the focus value, then follows `to_next_val`; it removes (with pruning)
  what it yields, which removes no *value* it has not yet reached, so it yields
  exactly the values at or after the focus in depth-first order.
* `W2R` — `WriteZipperOwned::into_read_zipper` keeps the root and focus, so its
  fingerprint is the write zipper's.  (`MAP0`, before these, comes from
  `into_map()` on whichever of the two is left.)
* `RCLONE` / `WCLONE` — a `clone()` of a zipper is the same zipper: same root,
  same focus.  `rz` is first moved off its root (`reset`, `descend_last_path`),
  `wz` is wherever the program left it.  Last, since the crate's clones lose
  the focus (a known defect) and an input is classified by its first
  differing line.

Fields are joined with `;`/`/`, never spaces, `,` or `:`, so `differential.py`'s
divergence-shape rules cannot file a difference here under a known class.
-/

namespace PathMapModel

/-- A fingerprint as one token. -/
def ownedFp (r : Render) (z : Zip UInt64) : String :=
  String.map (fun c => if c == ' ' then ';' else c) (r.fingerprint z)

/-- `(path, value)` pairs as the trailer prints them: at most 64, `-` for none. -/
def ownedPairs (r : Render) (l : List (Path × UInt64)) : String :=
  if l.isEmpty then "-"
  else String.intercalate "/" ((l.take 64).map fun (p, v) => r.hexPath p ++ "=" ++ toString v.toNat)

def ownedTrailer (r : Render) (_hdr : Nat) (wz rz : Zip UInt64) : List String :=
  let vs := (wz.trie.subtrie wz.root).vals
  [ "ITER0 " ++ ownedPairs r vs,
    "ITERF " ++ ownedPairs r (vs.filter fun (q, _) => Path.le wz.path q),
    "W2R " ++ ownedFp r wz,
    "RCLONE " ++ ownedFp r rz.descendLastPath.2,
    "WCLONE " ++ ownedFp r wz ]

def Source.owned : Source :=
  { name := "owned"
    caps := { trieRef := true }
    trailer := ownedTrailer }

end PathMapModel
