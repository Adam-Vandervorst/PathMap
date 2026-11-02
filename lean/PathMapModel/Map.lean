import PathMapModel.Write

/-!
# The `PathMap` surface

A `pathmap::PathMap` *is* a `PathMap`: the value at the empty path is the map's
root value.  Almost every `PathMap` method is implemented in `pathmap` by
opening a temporary zipper at the root and delegating, and the model does the
same, so the two layers cannot drift apart.

The one genuinely map-level operation is `PathMap::restrict`, which differs from
`ZipperWriting::restrict`: it consults the *root value* of the right-hand map,
which a node-level `prestrict` cannot see.  See `Map.restrict`.
-/

namespace PathMapModel
namespace Map

variable {V : Type}

/-- `PathMap::new`. -/
def new : PathMap V := PathMap.empty

/-- `PathMap::single`. -/
def single (p : Path) (v : V) : PathMap V := (PathMap.empty.setVal p v).2

/-- A read/write zipper at the root of the map. -/
def zipper (t : PathMap V) : Zip V := { trie := t, root := [], path := [] }

/-- A zipper rooted at `p` (`read_zipper_at_path` / `write_zipper_at_path`).
The zipper cannot ascend above `p`, and its `val()` at the root is the map's
value at `p`. -/
def zipperAt (t : PathMap V) (p : Path) : Zip V := { trie := t, root := p, path := [] }

/-- `PathMap::get_val_at` / `get`. -/
def getValAt (t : PathMap V) (p : Path) : Option V := t.valAt p

/-- `PathMap::contains`: whether there is a **value** at `p`.

Not the same question as `path_exists_at`, and the gap between them is the bare
case: a path created by `create_path`, or left behind by `remove_val(false)`,
exists but is not contained. -/
def contains (t : PathMap V) (p : Path) : Bool :=
  match t.entryAt p with
  | .valued _ => true
  | .bare | .absent => false

/-- `PathMap::path_exists_at`. -/
def pathExistsAt (t : PathMap V) (p : Path) : Bool := t.pathExists p

/-- `PathMap::set_val_at` / `insert`. -/
def setValAt (t : PathMap V) (p : Path) (v : V) : Option V × PathMap V := t.setVal p v

/-- `PathMap::remove_val_at` / `remove` (`remove` passes `prune = true`). -/
def removeValAt (t : PathMap V) (p : Path) (prune : Bool) : Option V × PathMap V :=
  let (old, z) := ((zipper t).descendTo p).removeVal prune
  (old, z.trie)

/-- `PathMap::val_count`. -/
def valCount (t : PathMap V) : Nat := t.valCount []

/-- `PathMap::is_empty`. -/
def isEmpty (t : PathMap V) : Bool := t.isEmptyMap

/-- `PathMap::create_path`. -/
def createPath (t : PathMap V) (p : Path) : Bool × PathMap V :=
  let (b, z) := ((zipper t).descendTo p).createPath
  (b, z.trie)

/-- `PathMap::prune_path`. -/
def prunePath (t : PathMap V) (p : Path) : Nat × PathMap V :=
  let (n, z) := ((zipper t).descendTo p).prunePath
  (n, z.trie)

/-- `PathMap::remove_branches_at`. -/
def removeBranchesAt (t : PathMap V) (p : Path) (prune : Bool) : Bool × PathMap V :=
  let (b, z) := ((zipper t).descendTo p).removeBranches prune
  (b, z.trie)

/-- All key/value pairs, in depth-first (lexicographic) key order — `PathMap::iter`. -/
def iter (t : PathMap V) : List (Path × V) := t.vals

variable (ops : ValOps V)

/-- `PathMap::join`: union, root values included. -/
def join (a b : PathMap V) : PathMap V := PathMap.join ops a b

/-- `PathMap::meet`: intersection, root values included. -/
def meet (a b : PathMap V) : PathMap V := PathMap.meet ops a b

/-- `PathMap::subtract`: difference, root values included. -/
def subtract (a b : PathMap V) : PathMap V := PathMap.sub ops a b

/-- `PathMap::restrict`: keep the paths of `a` that have *some* prefix carrying a
value in `b`.

The empty prefix counts here, so a root value in `b` validates everything and
the result is `a` unchanged (root value included).  Otherwise the result never
has a root value, because a node-level `prestrict` has no slot for one.  This is
the documented behaviour of `PathMap::restrict`, and it is *not* what
`ZipperWriting::restrict` does — see `Zip.restrict`. -/
def restrict (a b : PathMap V) : PathMap V :=
  if (b.valAt []).isSome then a else PathMap.restrictBelowRoot a b

end Map
end PathMapModel
