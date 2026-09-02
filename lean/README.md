# A Lean model of the `pathmap` zipper

An executable formal specification of `pathmap`'s trie and zipper API, written
in Lean 4, meant to serve as an oracle for differential fuzzing of the real
crate.

**The model** (`PathMapModel/`) is a total, executable definition of what each
API function *means*, with the laws relating them.

## Build and run

Lean is installed through `elan`, which reads `lean-toolchain` and fetches the
pinned version (`leanprover/lean4:v4.33.1`, ~300 MB) on the first build.  The
model has no package dependencies.

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # or: brew install elan-init
source ~/.elan/env
```

```bash
# the model, its build-time law checks, and the oracle binary
cd lean && lake build

```

`lake build` also checks every `#guard` in `PathMapModel/Check.lean`, so a build
failure there means a law or a regression fixture broke.

## Why a model rather than more property tests

A property test asserts things you already suspect.  A model asserts *everything*
at once: for each generated program the harness compares every return value and
the entire resulting trie against what the specification says should happen.  The
interesting consequence is that writing the model is where most of the value was
— several defects were found by trying to state
the semantics precisely and discovering there was no consistent statement to
make, before a single fuzz input had been generated.

## The model is not a trie

Worth stating plainly, because the name would otherwise mislead: a trie is a
prefix tree, and this model is a flat list of `(path, value?)` pairs.  It is not
one, and does not try to be.

The model specifies the *meaning* a trie carries, not the trie.  Shaped like the
implementation, it would inherit the implementation's structure — and a bug in
how that structure is handled could then be present in both and cancel out.
Three of the crate defects the fuzzing found are of exactly that kind (an invalid node built
by `graft`, a dense-node path in `graft_child_maps`, empty nodes in the sharing
machinery), and the model catches them precisely because it has no nodes to get
wrong.  The type is named `PathMap`, after the crate's own name for the thing a
trie implements.

## The representation

Everything rests on one observation.  A `pathmap` trie is **not** just a
path→value map: `create_path` makes a location that exists without carrying a
value, and `remove_val(false)` leaves one behind.  So a location and a value at
that location are separate facts, and the state records both:

```lean
structure PathMap (V : Type) where
  entries : List (Path × Option V)   -- every location that exists, with its
                                     -- value if it has one
```

One list rather than a path→value map beside a set of existing paths.  The two
halves the API actually observes — `paths` and `vals` — are *derived* from it,
which makes the awkward invariant "every valued path also exists" structural
rather than something every constructor has to maintain: a value cannot be
recorded at a location that is not in the list.  A `none` entry is exactly a
dangling path.  (`PathMap.mem_vals_pathExists` states this as a theorem; it used to
be a runtime check, because in the two-list form it could fail.)

The list is canonical — sorted by path, no duplicates, prefix-closed, containing
`[]` — so **structural equality of `PathMap`s is observational equality**, which is
exactly what is needed to decide `AlgebraicStatus::Identity` versus `Element`.

A location is therefore in one of three states, and asking about it returns all
three at once rather than splitting the question across two accessors:

```lean
inductive Entry (V : Type) | absent | bare | valued : V → Entry V
-- absent ~ Rust's Vacant, valued ~ Occupied, and `bare` is the state a
-- HashMap has no room for: there, but holding nothing.

def entryAt   : PathMap V → Path → Entry V
def valAt      t p := (t.entryAt p).val       -- derived
def pathExists t p := (t.entryAt p).present   -- derived
```

The middle case is where this API keeps going wrong — `create_path` produces it,
`remove_val(false)` leaves it behind, and several crate operations
mishandle it.  A definition written against `Entry` cannot
quietly forget it: the `match` will not compile until it says what happens.  And
`valued` entails existence by construction, so "a value at a path that is not
there" is unrepresentable rather than merely false
(`PathMap.Entry.present_of_val`).

A zipper is that trie plus two paths:

```lean
structure Zip (V : Type) where
  trie : PathMap V   -- the map (a snapshot, for a read zipper; live, for a write zipper)
  root : Path     -- root_prefix_path(): where the zipper was created
  path : Path     -- path(): the relative path to the focus
```

`origin_path() = root ++ path`.  The focus is allowed not to exist — `descend_to`
moves anywhere — so `path` is an unconstrained list of bytes.

Two distinctions the model keeps explicit because `pathmap` depends on them:

* **A node is what lies strictly below a location.**  The value *at* a location
  lives in its parent's cell.  `get_focus`, `graft_internal` and every `*_dyn`
  algebraic primitive operate on nodes, so they never touch the focus value;
  `PathMap.subtrie` includes it, `Zip.focusNode` does not.
* **The `graft_root_vals` feature is on by default**, so `graft`, `graft_map`,
  `make_map`, `take_map`, `join_map_into`, `meet_into` and `subtract_into` handle
  the focus value in a separate step — while `join_into` does not.  The model
  reproduces that asymmetry rather than smoothing it over.

Depth-first traversal order is exactly lexicographic order on paths (a proper
prefix sorts before its extensions), so every iteration primitive is specified
denotationally — "the `Path.lt`-least existing location strictly after the
focus, such that ..." — instead of as a node walk.

## Layout

| file | contents |
| --- | --- |
| `PathMapModel/Basic.lean` | paths, the prefix and lexicographic orders, `ByteMask`, `ValOps`/`ValRes` (the fragment of `Lattice`/`DistributiveLattice` the trie consumes, including the left-biased `u64` instance), `AlgebraicStatus` |
| `PathMapModel/PathMap.lean` | what a trie *means*: the flat representation, its observations, sub-tries and grafting, point updates, pruning, and the trie-level `join` / `meet` / `sub` / `prestrict` / `drop_head` |
| `PathMapModel/Zipper.lean` | the read API: `trait Zipper`, `ZipperValues`, `ZipperMoving`, `ZipperIteration`, `ZipperForking`, `ZipperAbsolutePath` |
| `PathMapModel/Write.lean` | the write API: `ZipperWriting` in full |
| `PathMapModel/Map.lean` | the `PathMap` surface, which is the zipper API applied at the root — plus `PathMap::restrict`, the one genuinely map-level operation |
| `PathMapModel/Spec.lean` | §1 proved laws (the cursor algebra); §2 checkable laws (metamorphic properties) |
| `PathMapModel/Check.lean` | `#guard`s: regression fixtures transcribed from `src/write_zipper.rs`'s own tests, and the §2 laws over a battery of tries |

## What is proved versus what is checked

Honest accounting, because it matters for how much the model is worth:

* **Proved** (`Spec.lean` §1): the cursor algebra — `descend_to` is a monoid
  action of paths on zippers, ascending exactly as far as you descended is the
  identity, ascending past the root stops at the root and reports failure,
  movement never mutates the trie, `origin_path = root_prefix_path ++ path`,
  `child_count = |child_mask|`, and `prune_path` never removes more bytes than
  separate the focus from its stop depth.
* **Machine-checked on fixtures** (`Check.lean`): the metamorphic laws in
  `Spec.lean` §2, evaluated at build time over six trie shapes crossed with
  eight focus positions — plus regression fixtures whose expected values are
  transcribed from `pathmap`'s own unit tests (`write_zipper_prune_path_test2`,
  `write_zipper_drop_head_test1/3/6`) and the `restrict` oracle from
  `tests/pathmap_algebra_differential.rs`.

The definitions themselves are the specification.  They are total and executable,
so "the spec" and "the oracle" cannot drift apart.

## The blind-zipper contract

The model follows master's blind-zipper contract, where `ZipperMoving` no longer
provides `path()`.  A zipper that does not track its own path is *blind*;
`path()` and `move_to_path()` moved to a separate `ZipperPath: ZipperMoving`
trait, which the concrete `ReadZipper`/`WriteZipper` types still implement.

What that cost the model, in full:

* **`Zipper.lean` gained `focusByte`** — the only positional information a blind
  zipper can read.  Its value at the root is *unspecified* by the trait.
* **The movement operations report distance or destination, not a flag.**
  `ascend`, `ascend_until` and `ascend_until_branch` return the number of bytes
  ascended; `descend_indexed_byte`, `descend_first_byte`, `descend_last_byte`,
  `to_next_sibling_byte` and `to_prev_sibling_byte` return the `Option<u8>` byte
  they moved to.  `ascend_byte` survives as `ascend(1) == 1`.
* **`descend_until_observed` is new**, and is the interesting addition: a blind
  zipper learns where it went only from what the operation reports to a
  `PathObserver`.  The model specifies the reported sequence as the path delta,
  and `Laws.descendUntilObservedExact` states the property.

`ZipperWriting`, `Zipper` and `ZipperValues` are unchanged, so `PathMap.lean`,
`Write.lean` and `Map.lean` needed nothing.  Two proved laws were restated
around the new return types, and one was added — `ascend_accounts`, that the
count `ascend` reports is exactly the depth the focus lost, which is what a
blind caller has to rely on.

## Is the specification just a copy of the bugs?

A hand-written model checked against the implementation it was written from has
a specific failure mode: if a defect was **transcribed into the spec**, the two
agree, and the harness reports that agreement as confirmation.  That is worse
than no signal.

Most of the model is not exposed to this — it is derived from trait
documentation (`to_next_val` is "the least existing location after the focus
carrying a value"), from what the types force, or from mathematics (join is
union).  But some of it is not.  Auditing the ~130 definitions, these encode
observed behaviour rather than intent, and are the places to distrust:

| definition | why it is suspect |
| --- | --- |
| `AlgStatus.merge` | transcribed line-for-line from `src/ring.rs` |
| `joinVal` / `meetVal` / `subVal` | follow `Option<V>`'s impls in `src/ring.rs` |
| `Zip.prunePath` | stop depth determined empirically; the doc comment is wrong |
| `Zip.toNextKPath` | deliberately follows the native `ReadZipper` over the trait default |
| `PathMap.dropHead` | "values at depth exactly `k` are lost" is observed, not documented |
| `Zip.joinMapInto` | the short-circuit asymmetry with `join_into` is observed |
| `Zip.meet2` | "never reports `Identity`" comes from a comment in the impl |
| `Check.lean` fixtures | expected values copied from the crate's own passing tests |

**The primary defence is the style the model is written in.**  A definition that
restates its docstring can be checked by reading it; a definition that *simulates
the implementation* has to be executed in your head, and that is where a
transcribed bug hides.  So every operation is written declaratively -- as "the
location such that ...", never as a loop that walks there:

```lean
/-- the next existing location carrying a value, in depth-first order -/
def toNextVal : Bool × Zip V :=
  match z.subPaths.find? (fun q => Path.lt z.path q && (z.trie.valAt (z.root ++ q)).isSome) with
  | some q => (true, { z with path := q })
  | none => (false, z.reset)
```

`subPaths` is in depth-first order, so `find?` *is* "the next one".  The
docstring and the code say the same thing, and no amount of staring at
`ReadZipperCore`'s iterator tokens would change what this definition means.

The same idiom covers ascent -- "the deepest strict ancestor that branches,
carries a value, or is the root" is a `filter` over `Path.properPrefixes`
followed by `getLast?`, not a walk upward.  `descend_until` is "the nearest
descendant that is a value or is not single-childed".  `descend_to_existing` is
"the longest prefix of `k` that still exists", which is well-defined precisely
because existence is prefix-closed.  Nothing in the model recurses with a fuel
bound any more, and nothing computes an index like `p.length - 1 - j`.

This costs efficiency -- several definitions are quadratic where the crate is
constant-time -- and that is the intended trade.  The model is a specification
that happens to run, not an implementation.

Two further defences, in increasing order of how much they actually prove:

**1. Metamorphic laws** (`Spec.lean` §2) relate *different* API functions to each
other — `take_map` then `graft_map` is the identity, `drop_head` undoes
`insert_prefix`, `join` is commutative on paths.  Transcribing one function's
behaviour does not make these hold, so they keep working when the definitions
are contaminated.

**2. Naive oracles** (`Check.lean`) re-derive the same answer from a deliberately
stupid, independent route.  `joinKeysOracle`, `meetKeysOracle` and
`subKeysOracle` say which keys survive using set theory and nothing else — no
`ValOps`, no `PathMap`.  Where they agree with the real definitions, the `ring.rs`
transcription is excluded as a source of error.  This is the same technique the
crate's own `tests/pathmap_algebra_differential.rs` uses for `restrict`, where it
caught a real `prestrict` bug.

What none of this can do is prove the specification *right*.  It can only show
that the specification is not vacuous in a given region, and narrow the set of
places where "the model and the crate agree" might mean "they are wrong
together".  Every survivor is a place to go and re-derive the definition from the
documentation rather than from the code.

## Sharing

`pathmap` is a DAG: subtries are shared between paths, `graft` clones a
refcounted pointer rather than the data, and writes go through copy-on-write.
**The model has no notion of nodes at all** — a `PathMap` is a flat map from paths
to entries, so grafting the same subtrie into two places yields two independent
copies by construction, and sharing is invisible.

That is deliberate.  Sharing is an implementation strategy, not part of the
meaning, and the crate says so itself about the two methods that expose it:
`shared_node_id` "is not stable across runs", and of `is_shared`, "your code
must never rely on the return value for correctness".  Specifying them would
mean specifying non-determinism, so `ZipperConcrete` is out of the harness.

Nothing is refused: a write whose focus lies inside a shared subtrie goes
through, and the sharing is dissolved as it happens.  `make_unique` compares the
refcount and clones when it is not 1, so the node stops being shared at the
moment of the write — `is_shared` at the written location goes `true` → `false`
while the other reference keeps the original node.  Copy-on-write, not a
restriction.

Not modelling sharing is what makes sharing bugs *detectable* rather than what
hides them: the model says two grafted copies are independent, so a mutation
leaking from one to the other is a divergence.

## Out of scope

`ZipperHead` and the concurrency story, `ProductZipper` / `PrefixZipper` /
`OverlayZipper` / the ACT format, serialisation, `merkleize`, catamorphisms, and
allocator behaviour.  The model covers `PathMap`, `ReadZipper` and `WriteZipper`
over an in-memory trie.
