# Unit-value optimizations: measured results

Two optimizations aimed at `PathMap<()>` and other trivially-valued tries, from a
survey of places the trie pays for a value that carries no information.

| commit | change |
| --- | --- |
| `218a256` | Skip value-drop work in `LineListNode` when `V` has none to do |
| `18d40ec` | Honor `Lattice::IDEMPOTENT` in the node algebra, and short-circuit `join_into` |
| `9f73907` | Memory attribution by node type under the `counters` feature |

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

## Negative results

These three were measured and rejected. Recording them so they are not
re-attempted from first principles.

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
