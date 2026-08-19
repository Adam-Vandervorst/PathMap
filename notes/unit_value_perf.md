# Unit-value optimizations: measured results

Two optimizations aimed at `PathMap<()>` and other trivially-valued tries, from a
survey of places the trie pays for a value that carries no information.

| commit | change |
| --- | --- |
| `218a256` | Skip value-drop work in `LineListNode` when `V` has none to do |
| `18d40ec` | Honor `Lattice::IDEMPOTENT` in the node algebra, and short-circuit `join_into` |
| `9f73907` | Memory attribution by node type under the `counters` feature |

A fourth change -- packing the CoFree value flag into its child pointer -- was
built and measured but **not merged**; see [below](#shelved-packing-the-value-presence-flag-into-the-child-pointer).

**A note on the survey these came from.** Its estimates were made by reading
struct definitions, and three of them did not survive measurement: S3 was not
implementable *and* worthless, S4 turned out to cost nothing to begin with, and
S1's headline ("2x node memory") was true per-node but meant 5% on
MORK-shaped data, because dense nodes are only a fifth of those bytes. Measure
first; the profiler in `9f73907` exists for that.

## Results

Min of 3 runs per side, each run itself the min of 7 timed repetitions, every
operation in its own process. 1M paths of 8 random bytes.

| operation | before (ms) | after (ms) | change | verdict |
| --- | ---: | ---: | ---: | --- |
| `join_into` — operands share a root | 108.1 | **0.000** | **eliminated** | real gain |
| `join` — operands share a root | 0.000 | 0.000 | — | already short-circuited |
| `subtract` — operands share a root | 0.000 | 0.000 | — | already short-circuited |
| `join_into` — disjoint operands | 102.4 | 104.6 | +2.1% | within noise |
| `join` — disjoint operands | 85.8 | 87.0 | +1.5% | within noise |
| `meet` — full overlap, distinct nodes | 95.0 | 95.0 | +0.0% | within noise |
| `subtract` — full overlap, distinct nodes | 123.3 | 114.3 | −7.3% | within noise |
| drop `PathMap<()>` | 193.1 | 193.7 | +0.3% | within noise |
| drop `PathMap<u64>` | 191.7 | 192.0 | +0.1% | within noise |
| drop `PathMap<Vec<u8>>` | 365.8 | 367.1 | +0.4% | within noise |

**Noise floor**, measured by running the same tree against itself three times:
7–11% on the algebra operations, 2–3% on the drops. Every row above except the
first sits inside it. Treat the −7.3% on `subtract` as noise, not a gain — the
change touches nothing on that path beyond a compile-time-constant guard.

## What each optimization actually bought

### `join_into` on a shared subtrie: 108 ms → free

The only unambiguous win, and it came from a shortcut that was *missing* rather
than one that was slow. `TrieNodeODRc::join_into` had no pointer-equality check
and went straight to `make_mut()`, which deep-copies the node when it is shared —
precisely the case where both sides are likely to be the same pointer. Three call
sites that hand-rolled `make_mut().join_into_dyn()` now route through it and
inherit the check:

- `PathMap::join_into`
- `CoFree::join_into` (the recursive branch)
- `WriteZipper::join_into_take`

The size of the win scales with the trie, because the whole descent disappears.
It is worth the most in workloads that join overlapping tries built by grafting
or cloning, where pointer sharing is common — which is the regime `()` values plus
merkleization create.

### Drop elision: no measurable throughput change

`LineListNode`'s drop paths tested whether each payload slot held a child or a
value, then called `ManuallyDrop::drop` on the value. For a value type with no
drop glue that call does nothing, but the branches around it still ran.

LLVM was already folding the no-op `LocalOrHeap<(), _>::drop` at `-O2`, so what
the change removes on top of that is a well-predicted branch — invisible against
the allocator traffic and cache misses of walking a million-node trie. What it
does buy:

- The elision is explicit rather than optimizer-dependent, so it holds in debug too.
- The drop path got simpler: `is_used_child_N()` replaces four separate bit tests.
- It generalizes past `()` to any value type with no drop glue that fits inline.

One trap worth recording. The obvious guard, `needs_drop::<V>()`, is **wrong**
here. The slot is a `LocalOrHeap<V, _>`, which carries an unconditional `Drop`
impl and boxes any `V` too large to store inline — so a `[u8; 64]` has no drop
glue of its own but does own a heap allocation. The predicate has to cover both:

```rust
pub(crate) const fn val_slot_needs_drop<V>() -> bool {
    core::mem::needs_drop::<V>() || core::mem::size_of::<V>() > core::mem::size_of::<ValSlotStorage>()
}
```

`ValSlotStorage` is now the type alias the union itself uses, so the size
threshold cannot drift away from the layout. `cargo miri test` covers the
`[u8; 64]` case, since only miri can observe the leak a wrong guard would cause.

### `IDEMPOTENT`: a correctness fix, not a speedup

The gating half of `18d40ec` costs and saves nothing at `()`, because
`IDEMPOTENT` is `true` there and folds away. Its value is that the constant now
means something. Six sites take the shared-subtrie shortcut — not the three that
grepping for `ptr_eq` finds, but also the `TaggedNodeRef` dispatchers underneath,
which is where it fires at *every* level of a descent, in two copies (one per
`slim_dispatch` setting). Before this change a value type whose join actually
combines its operands — a multiset adding multiplicities — would have had its
structurally shared branches silently skipped instead of combined.

No in-tree value type declares `IDEMPOTENT = false`, so no existing behavior
changed; all 710 lib tests pass unchanged.

## Method

- rustc 1.95.0-nightly, `--release`, `-C target-cpu=native` (from `.cargo/config.toml`)
- Default features (`graft_root_vals`, `slim_ptrs`, `serialization`); jemalloc **off**
- x86_64 Linux, 64 cores
- Baseline is `master` at `8b8802a` in a separate worktree with its own target dir
- Each operation runs in its own process. This matters: an earlier pass that timed
  everything in one process showed a spurious 6–9% regression on three operations,
  because at baseline the self-shared join does real allocator work that warms the
  heap for whatever is measured next. Process isolation removed it.
- Inputs are built outside the timed region; results are dropped outside it.

The timing harness was temporary and is not in the tree; reconstructing it means
building two `PathMap<()>`s from xorshift-generated 8-byte keys, timing the
operation with `Instant`, and taking the min across repetitions. The *memory*
harness is in the tree -- `cargo test --release --features counters,serialization
--test memory_profile -- --nocapture` reproduces every memory table below.

## Where the memory actually is

`memory_profile` (`9f73907`) walks physical nodes and attributes bytes by node type.
Three tries, all `PathMap<()>`:

| dataset | values | list nodes | dense nodes | bytes/value |
| --- | ---: | ---: | ---: | ---: |
| `big_logic.metta` (MORK) | 91,692 | 7.63 MB (**79.7%**) | 1.95 MB (20.3%) | 104.5 |
| 1M random 8-byte keys | 1,000,000 | 62.2 MB (69.2%) | 27.7 MB (30.8%) | 89.9 |
| shakespeare words | 67,505 | 2.16 MB (52.8%) | 1.93 MB (47.2%) | 60.7 |

The split swings from 80/20 to 53/47 with key shape, so "shrink a dense slot" and
"shrink a list node" mean very different things depending on the workload. On the
MORK-shaped data, list nodes are four fifths of the trie.

### Dense slot arrays run 16-41% over-allocated

| dataset | slots used | slots allocated | slack |
| --- | ---: | ---: | ---: |
| MORK | 52,474 | 60,714 | 15.7% |
| random 8-byte | 1,038,499 | 1,466,715 | **41.2%** |
| shakespeare | 55,916 | 72,132 | 29.0% |

`Vec`'s amortized doubling, on arrays that top out at 256 slots and are usually
built one byte at a time.

## Shelved: packing the value-presence flag into the child pointer

**Implemented, measured, and not merged.** It lives on branch
`experiment/cofree-pointer-packing` (`2fd48be`), rebuilt on top of this branch's
history. It works, it is miri-clean, and it buys real memory -- but it costs
roughly 9% on iteration over MORK-shaped data, which is the workload that
matters here, so the trade goes the wrong way. Kept as a branch to show the
approach is viable and to record what it costs.


A dense-node slot was `{ Option<TrieNodeODRc>, Option<V> }`: one word for the
pointer, and a whole word more for `Option<V>` once alignment rounds it up. Node
allocations are 8-byte aligned, so bits 0..3 of a node address are always zero.
`OrdinaryCoFree` now stores an absent child as the empty-node sentinel instead of
`None` -- so the word is never null -- and borrows bit 0 to say whether its
`MaybeUninit<V>` is initialized.

| slot | before | after |
| --- | ---: | ---: |
| `OrdinaryCoFree<()>` | 16 B | **8 B** |
| `OrdinaryCoFree<u32>` | 16 B | 16 B |
| `OrdinaryCoFree<u64>` | 24 B | **16 B** |

Pinned by static assertions, so the layout cannot regress silently.

### Result

| dataset | memory | build | iterate | lookup |
| --- | ---: | ---: | ---: | ---: |
| `big_logic.metta` (MORK) | 9.58 -> 9.09 MB (**-5.1%**) | +3.3% | +9.3% | +0.7% |
| 1M random 8-byte keys | 89.94 -> 78.21 MB (**-13.0%**) | -7.8% | -3.4% | -9.2% |
| shakespeare words | 4.10 -> 3.52 MB (**-14.1%**) | -11.6% | -11.5% | -28.3% |

Memory is a clean win and lands within a tenth of a percent of what the profiler
predicted. **The timing is why this is shelved.** Shakespeare gets faster on every
axis and random keys improve modestly, but MORK iteration measures ~9% slower.
That is at the edge of what these benchmarks resolve, so it may be less than it
looks -- but 5% memory is not worth risking 9% iteration on the target workload,
and the burden of proof is on the change.

The likely cause is that `has_rec()` went from an `Option` null check to
`is_empty()`, which extracts and compares the pointer tag. That is a few
instructions on a very hot path, and MORK's tries are list-node-heavy, so they
pay it without getting much of the dense-node memory win in return. Anyone
picking this up should start there. The algebra
micro-benchmarks (`join`, `meet`, `subtract`, both disjoint and overlapping) all
moved less than 5%.

### Why the flag went in the pointer rather than a mask on the node

The alternative was a second `ByteMask` on `ByteNode`. It would have been safer
per-line but much larger: a `CoFree` would stop being self-describing, and the
algebra clones and drops them *outside* the node that owns them --
`pjoin`, `pmeet`, `psubtract` and `prestrict` each accumulate `CoFree`s into a
fresh vector before any node exists to own it. Keeping the flag inside the slot
left all ~108 call sites untouched.

### The invariant, and what it cost

The bit belongs to the **slot**, not to either node, so every in-place
replacement of a `TrieNodeODRc` must preserve it. `replace_node` and `swap_node`
do; plain assignment does not, and the failure is silent -- the slot's value just
disappears. Converting the assignment sites broke six existing tests, and one
more case (`ByteNode::node_replace_child`) that no existing test covered and that
a regex over deref-assignments missed because of the method-call chain
(`*cf.rec_mut().unwrap() = new_node`).

Every failure was a slot holding a value *and* a child -- i.e. a path that is a
proper prefix of another path. `tests/cofree_val_flag.rs` pins that down:
copy-on-write of a shared trie, node upgrades under a write zipper, grafting over
a slot that holds a value, algebra over prefix-heavy tries, and removal from a
slot that holds both. All pass under miri, along with the differential algebra
test and 118 filtered lib tests. The suite is kept on the main line as
`tests/prefix_value_preservation.rs`, since the property is worth pinning down
whatever the representation.

Two notes for anyone touching this again:

- The empty sentinel moved from `0xBAADF00D` to `0xBAADF00C`, because it has to
  be able to carry the flag like any other node pointer. A static assertion
  enforces that bit 0 is clear.
- `ptr_eq` and `shared_node_id` mask the bit off. Leaving it in would have
  silently defeated the shared-subtrie shortcuts from `18d40ec` and weakened the
  catamorphism cache, without failing a single test.

### S2 -- the CellCoFree box: not worth doing

`CellCoFree` keeps the old `Option` layout under the name `PinnedCoFree`, because
`CellByteNode::prepare_cf` hands a `WriteZipper` a `&mut Option<V>` that has to
point at a real `Option`. That costs nothing measurable: cell nodes appear only
under a `ZipperHead` and account for **zero bytes** in all three tries profiled
here, so halving their per-slot box would have saved nothing.

## Negative results

These seven were measured and rejected. Recording them so they are not
re-attempted from first principles.

### F4 -- "the result-merging machinery is what actually costs": off by an order of magnitude

The survey claimed the generic algebra's result plumbing -- `AlgebraicResult`,
`merge`, `combine_algebraic_results`, the `Hetero*` traits -- is where a
`PathMap<()>` spends its time, because the identity masks keep it from folding
away. Profiled with `perf` on 400k-path joins, meets and subtracts, attributing
cycles by source line so inlined code lands on its own line:

| source | cycles |
| --- | ---: |
| `malloc.c` | **29.72%** |
| `dense_byte_node.rs` | 17.71% |
| `trie_node.rs` | 13.31% |
| `option.rs` | 3.82% |
| `atomic.rs` (refcounts) | 2.71% |
| `line_list_node.rs` | 2.48% |
| **`ring.rs`** -- all of `AlgebraicResult` and the `Lattice` impls | **1.06%** |

`combine_algebraic_results` shows up separately at 2.86%. So the merging
machinery is roughly **4%**, against **30% in the allocator**. Rewriting it as
bit arithmetic -- which is what the survey proposed, and which depended on the
shelved S1 anyway -- would have chased about a twenty-fifth of the runtime.

## The thing the F4 profile actually found

Where the allocator time goes is worth its own section, because it is a real and
fixable inefficiency, and it is not unit-value-specific.

`ByteNode::pjoin` allocates the result slot vector and clones every slot into it
*before* it knows whether the result is a new node or just one of its operands.
When the answer turns out to be `Identity`, all of that is discarded. Instrumented
on 400k-path joins:

| operands | calls returning `Identity` | slot clones wasted |
| --- | ---: | ---: |
| disjoint | 0.0% | 0 of 789,291 (0.0%) |
| one is a subset of the other | **99.7%** | 159,078 of 167,800 (**94.8%**) |
| 95% overlap | **100.0%** | 449,799 of 451,600 (**99.6%**) |

Each wasted slot clone is an atomic refcount increment plus a matching decrement
on drop, and each wasted call is a `Vec` allocation and free. The effect is
visible end to end, and it inverts what you would expect:

| join | time |
| --- | ---: |
| disjoint operands -- builds a genuinely new 800k-path trie | 48.75 ms |
| one operand a subset -- result equals the larger operand | 42.64 ms |
| 95% overlap -- result is essentially the larger operand | **74.96 ms** |

The join that has almost nothing to do takes **1.5x longer** than the one that
doubles the trie, because it does the full copy and then throws it away. Joining
a trie with something it already mostly contains is a common shape -- it is what
incremental ingestion looks like -- so this is worth fixing.

The fix is to defer materializing the vector until the first slot result that is
neither `SELF_IDENT` nor `COUNTER_IDENT`. While both node-level identity flags
are alive, the result prefix is exactly one operand's slots, so it can be
back-filled at the point the flags die, using the side that was still identity.
Recursive sub-joins that returned `Identity` allocated nothing themselves, so the
saving is the whole per-node cost. Not attempted here.

### S5 -- `LocalOrHeap` "pins the payload union at 8 bytes": it does not

The survey said the `LocalOrHeap<V, [u8; 8]>` arm is why a payload slot is 8
bytes wide, and that a set-specialized node would have to replace it. Both halves
are wrong.

`LocalOrHeap` is a *fixed-size cell* -- it boxes anything too big to fit -- so
the value arm is the same width for every `V`, and the union's width is set by
its **other** arm, the child pointer:

| `V` | `size_of::<V>()` | union | boxed? |
| --- | ---: | ---: | --- |
| `()` | 0 | 8 | no |
| `u64` | 8 | 8 | no |
| `String` | 24 | 8 | **yes** |
| `[u8; 1024]` | 1024 | 8 | **yes** |

Deleting the value arm entirely would not shrink the union by a byte, because the
child pointer needs those 8 regardless. And for `()` the arm costs nothing at
runtime either: `size_of::<()>() == 0`, so nothing is boxed.
`val_slot_layout_tests` asserts both facts.

**What it did surface, which is real but not a unit-value concern.** Values live
overwhelmingly in list-node slots, and those are the ones that box:

| dataset | values in list slots | in dense slots |
| --- | ---: | ---: |
| `big_logic.metta` (MORK) | **99.93%** | 0.07% |
| 1M random 8-byte keys | **100.00%** | 0.00% |
| shakespeare words | 53.44% | 46.56% |

So for a `V` over the threshold, MORK-shaped data pays roughly one heap
allocation *per value*. Priced on 91,692 paths:

| value | size | boxed | build | drop |
| --- | ---: | --- | ---: | ---: |
| `u64` | 8 | no | 23.66 ms | 6.94 ms |
| `[u8; 8]` | 8 | no | 23.76 ms | 6.96 ms |
| `[u8; 9]` | 9 | **yes** | 28.22 ms (**+19%**) | 9.43 ms (**+36%**) |
| `[u8; 16]` | 16 | yes | 26.02 ms | 9.13 ms |

One byte over the line costs ~19% on insertion and ~36% on drop. Widening the
cell would fix it, but only by making every node bigger for every `V` --
including `()`, which needs none of it -- and sizing the cell per-`V` needs
`generic_const_exprs`. So the actionable part is documentation: the cliff is now
described on [`TrieValue`](../src/lib.rs), where someone choosing a value type
will see it.

### F3 -- eliding the value hash in `merkleize`: nothing to elide, and the obvious version is a bug

The survey said `merkleize` "requires `V: Hash` to hash nothing". The natural
reading -- put a const branch around `val.hash(&mut hasher)` -- is wrong twice.

Both sites hash `Option<&V>`, not `V`, and the `Option` is what carries the
information:

| expression | bytes written | hash |
| --- | ---: | --- |
| `().hash(h)` | **0** | -- |
| `Option::<&()>::None` | 8 | `0` |
| `Option::<&()>::Some(&())` | 8 | `27512614111` |

So the value payload *already* costs nothing at `()` -- `impl Hash for ()` writes
zero bytes and the call folds away. What the 8 bytes carry is the discriminant,
and for a set trie that discriminant is the only information there is: whether
the path is a member. Skipping it would make a path with a value hash identically
to one without, and `merkleize` would merge structurally distinct tries. That is
a correctness bug, not an optimization.

The `V: Hash` bound cannot come off either -- it is needed for a general `V`, and
`()` implements `Hash`, so it costs nothing to satisfy.

One adjacent remnant is real but too small to take: the "value, no child" branch
builds a fresh `GxHasher` per leaf value to compute what is, for any zero-sized
`V`, a constant. Priced directly:

    merkleize, big_logic.metta   21.03 ms for 91,692 values  (229 ns/value)
    merkleize, shakespeare        5.65 ms for 67,505 values  ( 84 ns/value)
    the per-leaf hasher            3.03 ns x 91,692 leaves = 0.28 ms

0.28 ms of 21.03 ms is **1.3%** -- below this machine's measured noise floor, in
the one routine where a subtle change silently corrupts structural sharing.
Not worth it.

### S4 -- replacing the dangling-path sentinel with a bit: nothing to save

The earlier survey claimed that a path kept alive by `remove_val(prune = false)`
costs "a pointer + node per pruned leaf", because a `LineListNode` records it by
pointing the slot's child link at `TrieNodeODRc::new_empty()`. Measured, it costs
nothing at all:

- **The sentinel never allocates.** `new_empty()` is a bogus address
  (`0xBAADF00D`) carrying `EMPTY_NODE_TAG`. There is no node.
- **The payload word exists regardless.** A `LineListNode` is a fixed-size
  struct, so the union the sentinel sits in is there whether the slot uses it or
  not. Marking the slot "dangling" in the header instead would free zero bytes.
- **A `DenseByteNode` already does what S4 proposed.** It represents a dangling
  path as a CoFree holding neither a child nor a value -- there is no sentinel in
  a dense node to begin with.

The measurement: taking shakespeare and removing half its values with
`prune = false` produces 14,212 dangling slots and leaves the trie **byte for
byte identical**, 4,095,744 before and after. `tests/memory_profile.rs` asserts
this so the claim does not have to be re-derived.

Also checked, since it was the only caller that really allocates: a `WriteZipper`
opened on a path that does not exist allocates an empty `LineListNode` for its
root, but does **not** leave it behind -- creating 2000 such zippers and dropping
them without writing moved the byte count by exactly 0, and no allocated empty
node was ever observed in any trie profiled here.

### S3 -- reclaiming value-slot bytes for list-node keys: not possible, and worthless

The earlier survey claimed a `LineListNode` value slot's 8 bytes could go to key
storage when `V` is a ZST, taking `KEY_BYTES_CNT` from 42 to 58. That was wrong
twice over.

**It cannot be done.** The slot is a union with a child pointer, and which one it
holds is a runtime property of the node. The space has to be sized for the pointer
whatever `V` is. There is no static reclaim without a separate node type.

**It would not be worth it anyway.** Only 10.4% of MORK list nodes are at the
42-byte cap, and *zero* on the other two datasets.

### Sweeping `KEY_BYTES_CNT`: already near-optimal for MORK, no single best value

| K | node size | MORK | random 8-byte | shakespeare |
| ---: | ---: | ---: | ---: | ---: |
| 10 | 32 B | +18% | **-35%** | **-27%** |
| 14 | 40 B | +16% | -28% | -20% |
| 18 | 40 B | +1.5% | -28% | -20% |
| 26 | 48 B | **-2%** | -19% | -14% |
| 34 | 56 B | -2% | -10% | -7% |
| 42 | 64 B | baseline | baseline | baseline |

Timings moved less than 5% throughout. MORK's long paths want the current 42;
short-key workloads want roughly 10. No single constant serves both, which is an
argument for a second, smaller list-node type rather than a different constant.

### Bounded growth for dense slot arrays: a wash

Replacing `Vec` doubling with growth to the next multiple of `SLOT_GROWTH`:

| growth | MORK | random 8-byte | shakespeare | random build time |
| --- | ---: | ---: | ---: | ---: |
| exact | -1.4% | **-7.6%** | -5.6% | **+26%** |
| 2 | -1.1% | -7.0% | -4.6% | +8.5% |
| 4 | -0.6% | -5.9% | -2.3% | +8.3% |
| 8 | +1.6% | -3.6% | +2.2% | ~flat |

The memory it reclaims is paid for in build time, and for granularity 8 and above
the rounding wastes more than doubling did on MORK's small dense nodes (3.4 slots
on average). Rejected.

## Still on the table

Both of these are small items from a wider survey. The larger unit-value wins are
untouched:

- **Dense-node slots are 16 bytes where 8 carry information.** `OrdinaryCoFree` is
  `{ Option<TrieNodeODRc>, Option<V> }`; at `()` the pointer is 8 bytes and
  `Option<()>` is 1, which alignment rounds to 16. Hoisting the presence bit into a
  second `ByteMask` halves a 256-way dense node from 4128 to 2112 bytes.
- **The algebra becomes mask arithmetic** once that split exists: the value
  dimension of join/meet/subtract/restrict is one bitwise operation, and recursion
  narrows to the intersection of the two child masks.
- **`LineListNode` spends 16 of its 64 bytes on payload slots a set doesn't need**,
  which could go to inline key bytes instead (42 → 58 for a two-leaf node).

These need either a value policy carrying an associated slot type — the refactor
`ring.rs` and `dense_byte_node.rs` already gesture at, and that
`pathmap-book/src/A.0003_policy_API.md` is a stub for — or parallel set-specialized
node types. Neither is reachable with the kind of local guard used here.
