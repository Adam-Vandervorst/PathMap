
# Discussion on Inter-Node References & Internal Resource Management

The [TrieNodeODRc](pathmap::trie_node::TrieNodeODRc) type is used for all inter-node links.  However it currently is just a `Arc<dyn TrieNode<V> + 'static>` and has a number of undesireable properties.

* It is a 128-bit fat pointer.  Links comprise a substantial amount of the in-memory footprint of the database, so shrinking this to 64 bits will be worth a lot.
* The `Arc` header in the node structure eats a further 16 bytes.  8 bytes for the weak count which is totally unused, and 8 bytes for the strong count, which probably has a lot more range than we need.
* Having each refcount separate on each node means we need to load the cache line for the node's header (which is often the whole node) into memory in order to check the refcount prior to freeing the node.  Sometimes this means freeing a trie is nearly as expensive as initializing it.
* There is no concept of availability that is separate from the refcount

Ideally we can solve all of these issues at the same time and lay the ground work for **persistence** (writable on-disk tries) at the same time.

## Desiderata

* Support for multiple (polymorphic) node data structures.
* Refcounts on each (inter-node) link, and maintain the "clone the pointer to increment the refcount" paradigm.
* Support for the `make_mut` copy-on-write pattern.  I.e. if a referenced node's refcount is 1, then allow mutation, otherwise clone the node to a new location for mutation.
* Support for multiple "node regions" in which nodes may be referenced and created. (More on node regions in its own section)
* Refcounts stored centrally so reading or modifying them doesn't thrash the cache.

**NOTE(igorm)**: Storing refcounts separately from the node itself requires storing an additional
pointer (or an index at minimum) for each child.
My prediction is that any savings from storing it separately will be offset by increasing node or child size by including this pointer. Additionally, it might be difficult to store a freelist of refcounts.
We can experiment on this, not sure how it goes.
**LP**: That's certainly not the design I intended to suggest.  A design where a node could point at any arbitrary refcount-storage object, and thus required a pointer, would indeed be very silly.  The design I had in mind would infer the location of the refcount from the node location or pointer.  For example, one idea is to store all refcounts in a section at the head of each NodeBlock.

### Nice to Have, but Ok if it's not possible

* Clean separation between node format code and resource management code.

## Proposal: Node Regions

Structures to own nodes and track dependencies.  A node region is a *logical* object responsible for node life cycles, that manifests in the API.

### Features Enabled by Node Regions

* It should be possible to mmap a file containing nodes, and work with those nodes directly, and create new nodes in the same file if the file is writable.

* It should also be possible to create new nodes in memory (not backed by a file) that reference nodes from a file. (For example a map that stores intermediate results)

* It should be possible to copy nodes from memory to a file, and from a file to memory.

**NOTE(igorm)**: what happens if we try to copy in-memory nodes that reference nodes on file?
**LP**: It depends on where we are copying them to (The destination region).  Before going through all the cases, I want to be clear on the distinction between copy (deep copy) and graft (create shallow reference).  I also want to establish that I see node region dependencies as being transitive.  i.e. if A depends on B, and B depends on C, then A also inherits a dependency on C.

The algorithm must proceed recursively from the source node.  Each time a node that resides in a region that is part of the destination region's dependencies is encountered, a simple reference is enough.  However if the node resiges in a foreign region (not in the dest region's dependencies) then a deep copy is needed, to copy the node to the destination region.

In the shallow graft-by-reference case, no recursive descent is needed.  When a deep copy occurs, each child node is visited and, depending on where it resides, it is either referenced or copied.

* It should be possible to work with multiple files at the same time, and potentially create in-memory structures that reference nodes in multiple files.

### Design Ideas for Node Regions

* Each node region is an object that handles its own resource management.  (Tracks all refcounts, Owns memory that stores all nodes).

* Some portion of a `TrieNodeODRc` smart pointer would point to a node region, and some other part of the pointer would identify the node within the region.

* A node region can have dependencies on other node regions, which are created when a graft or similar operation makes a cross-region node reference.  There is something like an `Arc` that keeps a region from deallocating / closing if one if its dependennt regions is still active.

* Node regions have properties that determine the behavior of operations that create references (graft-like operations).  For example, a file-backed region could not reference a node in a volatile memory region, so a graft-like operation would force a copy.  On the other hand a volatile in-memory region could reference a node in a file region.

It should probably be possible to inspect any node at runtime to determine its region.  To avoid bloating the node storage excessively, this would probably be accomplished using a global table of regions, and then we could either put a field on a NodeBlock or potentially use some of the space bits of the TrieNodeODRc pointer to specify which node_region a given node belongs to.

In addition to nodes, it is also necessary to track node region associations for maps and zippers for several reasons. Primarily, it may be necessary to create new nodes in different regions from the source.  For example when making writable copies of nodes on a read-only medium.  Also the empty node pointer is a sentinel constant, and therefore not associated with any region.

### Types of Node Regions

* A Transient Region does not track its nodes and thus does not have the ability to cleanup individual nodes.  It is used for temporary storage of nodes for intermediate operations.  Freeing a Transient Region can be done by dropping all of the backing memory.  **CAVEAT** Non-`Copy` value types will cause a problem with Transient Regions.  We either need to forbid non-`Copy` value types from Transient Regions, or engineer a values table that permits dropping of values.

* A Memory Region is intended to be long-lived, but not file-backed.  Individual nodes in a Memory Region can be freed, making room for new future nodes.  An entire Memory Region can be freed by dropping the backing memory (if the value type is `Copy`), but a more common usage patterns will be to have one persistent Memory Region for the life of the program.

* As the name suggests, a File Region is backed by a file.  We may want read-write and read-only flavors of File Regions.  TBD

#### Inter-Region Dependencies Allowed

| X -> Y    | Transient | Memory    | File      |
|-----------|-----------|-----------|-----------|
| Transient |      √    |     √     |     √     |
| Memory    |           |     √     |     √     |
| File      |           |           |           |

In English: "Any region can depend on a file region (and reference its nodes).  A file region can only reference nodes within itself."

### Node Regions and Allocators

When the `nightly` feature is enabled, it is now possible to use PathMap with custom allocators.  In concept, a node region is an extension of the allocator concept, so the right design is probably to forego the `_in` flavors of the various methods that take an allocator and pass a node region to the PathMap methods instead.  Then a node region could be backed by a custom allocator.

However, the pattern that is pervasive throughout the Rust stdlib, i.e. making the Allocator an optional type parameter with a default value, may not be quite right for node regions.  The Rust type system could enforce that a hybrid object isn't created; for example it could prevent the creation of a new map by joining together two maps with different allocators.  However, this use case is actually desirable for node regions, and therefore the region dependency needs to be maintained and checked at runtime.

Mixing allocators within the same map, on the other hand, is likely to lead to nothing but pain & UB.  So if a region implied an allocator that would be a problem.  Currently the types are configures so it just isn't possible to perform operations that would cause nodes from different allocators to mingle.

So, it's an open question what the relationship between allocators and regions needs to be.  The most sensible idea seems to me that allocators are checked at compile time, node regions are checked at runtime, and the type system would enforce that allocators are never mingled.  The alternative implementation would involve dispatching to allocators dynamically, which sounds like a terrible idea for many reasons.

## Proposal: Node Blocks

Structure that lays out multiple nodes in a contiguous block of memory.  A node block is a physical object that is not visible at the API level.   A node region could use a single node block, or be composed of multiple node blocks.

A node block would have:
* Partial paths and node information for multiple nodes
* A table of owned values
* A table of external (links outside the node block) links

Internal links, linking nodes within the node block to other nodes within the same block, could take the form of simple indices, as there may be no need to bump the refcount, and can be heavily compressed; perhaps 8 bits would be enough to describe any value, external link, or internal node within a 4K block.

**NOTE(igorm)**: there's an alternative that we can we pursue: use a custom allocator in each node region, which would be transparent over the API. i.e. allocate a specific node type.
As for having pointers within blocks, I don't know a good strategy (and I don't know if it exists) to separate nodes into blocks, such that they're densely linked to each other.
I'd have to find/make an algorithm to see if this is even possible.
Intuitively, it seems the *optimal* distribution of nodes is NP-hard,
greedy solutions are potentially many times worse, and maintaining the distribution of nodes while editing the tree/graph (specifically adding+removing nodes) is an unsolved problem.

> ...use a custom allocator in each node region.
**LP**: I did several days worth of work on an ultimately abandoned a custom allocator at the beginning of this year.  I had 2 reasons for leaving it.  A. the rust allocator API isn't stable, and it's actually churning pretty rapidly.  For example the [allocator-api2](https://crates.io/crates/allocator-api2) crate is kinda bit rotten already.  But the bigger reason was B. I felt like the custom allocator approach only solved some of the problems / features outlined in this document, and avoiding the memory allocator paradigm altogether is probably where we want to get to to ultimately achieve all of the features.

> I don't know a good strategy...
**LP**: I'll diagram up what I have in mind and we can discuss where it might fail.  We don't need *optimal*, just good enough, and we have an existence proof in the system allocator (or jemalloc) that something workable is possible.  The other point is that usage patterns will play a big role in efficiency.  It will certainly be possible to fragment the node blocks badly.  Especially when we layer in the requirement for atomic updating and robustness against write failure.

> maintaining the distribution of nodes while editing the tree/graph (specifically adding+removing nodes) is an unsolved problem
**LP**: This will be partially ameliorated by in-memory regions.  This lets the implementation skip the writing of a lot of the intermediate work.  It is certainly still a problem that requires careful consideration.  I think there are a lot of good ideas in the design of [LMDB](https://en.wikipedia.org/wiki/Lightning_Memory-Mapped_Database)

### Open Questions

* Do refcounts live with node blocks, or somewhere else?  If they live with node blocks, how do we make sure that circular references between blocks don't prevent deallocation?

**NOTE(igorm)**: I think this is not possible to do (1) using purely reference counting (2) FAST (3) in generic case.
The alternative is to have a garbage collector of some sort.

Let's look at the following tree:

```txt
a - b - c
  \ d - e
```

if you have references to `c,d`, `b,e`, and graft `d` onto `c`, then `b` onto `e`,
this will create the following graph:

```txt
a - b - c
 \    X
  \ d - e
```

which has a circular path `abedc(b)`. It seems to me that detecting this loop is not possible without visiting all subtrees of `b` and `d` when they get grafted.

**LP**: Circular references at the node level are illegal, so this is not a problem.  Without that behavior we could get infinite paths, and break our isolation guarantees, and a bunch of other horrible things.  So, if you performed those operations described above, here is what would happen...

> graft `d` onto `c`
This leads to:
```txt
a - b - c
 \    /
  \ d - e
```
> then `b` onto `e`
Will cause a copy-on-write of `d` and `e`, leading to"
```txt
a - b - c - d - e
 \   ^------<.
  \ d' - e' -^
```
My fear of circular references was referring to circularity at the node-block level.  Although I think there is a credit scheme that can fix this too.  Although I haven't fully thought it through yet.

**LP**: For resource management, we may well want something that looks more like a GC than straight reference counts.  However, we will still need the refcounts on the nodes (or at least an atomic `is_shared` field) because that is a critical part of the copy-on-write semantic used to maintain structural sharing in the trie.  Before writing off refcounts entirely, 

### Proposal for action

1) We need a set of benchmarks *and* metrics to optimize for.
   Mork has a few benchmarks, and it would be nice to include some which measure deallocation.
2) As for additional metrics, we could measure the memory per node/path.
3) We can implement a set of cheap experiments:
  - replace global allocator with never-freeing allocator
    * What will we learn from this experiment?  Are you thinking you want to separate how much of the time spent in cleanup is time spent with refcount check-and-decrement, vs. how much is simply freeing the allocations?

    Many of the more complex tests and benchmarks will `forget` the maps.  And it does result in instant "cleanup".  However if we implement a NodeBlock approach, we get both centralized refcounts and big contiguous allocations, so it will cut both costs.
  - replace `Arc` with `Asc`
    * `Asc` is probably worth a test.  I did a prototype last year based on [triomphe](https://crates.io/crates/triomphe), and it actually got slower in spite of losing the weak counts, likely because of some of the pointer metadata not being available without the unstable APIs.

    My main hesitation here was just that I felt like addressing all the issues holistically is going to ultimately be less work and lead to a simpler and better-factored system.  For example the `ODRc` is an `&dyn` ptr, but I think there are probably only 8 or 16 different node types we actually need to support, so I think we can probably find 3 or 4 bits out of the 64 to use as a tag.  What we definitely don't want to do is a double-indirection (i.e. `&TaggedNodeRef`), so moving away from `&dyn` should happen at the same time as moving to a different smart-pointer type.
  - track allocated memory and created nodes, see the distribution
    * Right.  I'm imagining different `NodeBlock` formats will exist for different purposes.  We could even support native `NodeBlock` formats for some data file formats (not JSON because it doesn't contain lengths and offsets, but maybe [beve](https://github.com/beve-org/beve))
  - record profiling information during benchmarks and see differences
    * 100% agreed.  The `counters` feature provides a bit of that.  It's pretty ad-hoc and gets dusted off for each experiment when we want to run it.  But I'm definitely open to creating more tools and a better framework for the tools we want.
4) instead of having refcounting, we could have a GC of some sort.
  * Yes.  This is an option we shouldn't discount.

# Specific Format Proposals

## Pointer Structure

The new TrieNodeODRc would be a 64-bit type.  In that we want to encode the following:

* type_tag: 3 bits.  Which code path to use to interpret the node.
* block_addr: 44 bits (could be made smaller if necessary, by imposing restrictions on the computer / operating system architecture).  The pointer to any valid 4K node block in the user address space can be reconstructed from this field. See https://github.com/irrustible/ointers/blob/main/src/lib.rs for details and code pertaining to this.
* node_id: 7 bits.  An id of a node, used to interpret the node's location within a block.  Usually corresponds to a node block chunk index.
* spare: 10 bits.  Currently unused, by may permit tries that span multiple computers in the future.

```txt
       ┌07     ┌0F     ┌17     ┌1F     ┌27     ┌2F     ┌37     ┌3F
----------------------------------------------------------------

Precise layout TBD
```

## NodeBlock Format

A NodeBlock would be a 4KB aligned block of memory.  It would contain the following:

* ref_counts_table:  96 x 4-Bytes = 384 Bytes.  A ref-count for each node (each chunk) in the block.  4 Bytes seems like the right size for a refcount.  That would provide a saturating (race-proof with relaxed access) counter up to 2 billion.  An extreme minority of nodes will have >2B referencers so saturation will almost never happen.  Therefore, 8 Bytes is overkill; on the other hand 2 Bytes = only 32K before saturation occurs, which could be quite common.

* payload_meta_table: 16 Bytes.  Stores 1 occupied bit per slot in the `payloads_table`.

  GOAT OUTDATED.  IGNORE THIS PARAGRAPH.  IT's BETTER IF NODES STORE THE KEY-OR-VAL info inside the individual chunk formats * payload_meta_table: 32 Bytes.  Stores 2 bits per slot in the `payloads_table`.  1 bit for whether the slot is occupied, and 1 bit for whether it is a value or an external link.  We *could* increase the `payloads_table` capacity by an additional value by skipping the "value or link" bitmask, and instead couning links from 0 up, and values from MAX down, and then only storing the (8-bit) index where values switch to links.  However this increases the expsense of finding an empty slot and determining whether a given payload_ref is a value or a link.

  GOAT OUTDATED. IGNORE THIS PARAGRAPH.  THE REFCOUNTS CAN DOUBLE AS OCCUPIED MARKER. * chunks_meta_table: 16 Bytes.  Stores 1 occupied bit per slot in the `chunks_table`.

* payloads_table: 126 * 8-Bytes = 1008 Bytes.  Stores external links inter-mixed with values.  External links are full 64-bit TrieNodeODRc pointers.  Values are either the value type stored natively, if `V` is `Sized < 64 bits` or another TBD indirection to a key-value store or external allocation.

* chunks_table: 84 * 32-Bytes = 2688 Bytes.  Blocks of memory representing the nodes themselves.  Layout depends on the respective Chunk Format.

### Discussion

A NodeBlock is full when it runs out of either chunks or payloads.

The ratio of chunks-to-payloads can be changed depending on what we find when encoding the data.

We may determine there is a locality benefit to interleaving payload table entries and chunks within a block.  Specifically in the case where we are traversing "through" a block, e.g. in a descend operation.  We might only want to load a single chunk from a block, and if the payload(s) referenced by that chunk were in the same cache line then it would limit the number of fetches.

Deallocating node blocks may best be done with a GC algorithm, because, while we can prove nodes will not create circular references, we cannot prove the same thing about node blocks.  If we do go with the GC route, we may want to move the `child_or_value` flags from the individual chunks to a central location in the node block, in order to know which payload entries represent links to other blocks that need to be marked for GC.

# PayloadRef

A `PayloadRef` is an 8-bit type used within a Chunk Format, that either refers to another chunk within the same node block (local link) or a slot within the `payloads_table` (external link or value).

The simplest scheme would be for the high bit of a `PayloadRef` can indicate a local link if set, and an external link or value if not set.  Then the remaining 7 bits becomes an index in either the `chunks_table` or the `payloads_table`.  If we end up wanting more than 128 slots in the `payloads_table`, we can compare the 8-bit value against another constant, and subtract that constant to turn the `PayloadRef` into an index.

A `PayloadRef` can have several sentinel values.  These specific values were chosen to avoid interference with valid mappings onto indices in the other tables.  If those tables change size, we can tweak these sentinels.

- `ZERO_SIZED_VALUE = 0x7F`  Means "zero-size value exists here", and saves the need to actually fetch anything from the `payloads_table`.

- `NULL = 0xFF`  Means no "payload or value exists here".  Can be useful to encode information within a ChunkFormat.

## ByteUnsaturated Chunk Format

The `ByteUnsaturated` format represents a location in the trie, with up to 24 descending children, preceded by up to 4 straight prefix path bytes.

The prefix path bytes address a common pattern observed in the data where large fan-outs are often preceeded by reasonably straight paths.  For example this happens because a given encoding might construct paths to represent `key = value`, and a common `key` might have many different `values` branching from a constant prefix formed from `key`.  Or, for example `tag` data, such as arity markers, will manifest as low-variance prefixes.

The `ByteUnsaturated` format spans 2 32-Byte contiguous chunks, with the `child_mask` field occupying the entire second chunk.

Fields:

* common_header: `u8` = 1 Byte.  3-bits of tag, 3 bit integer to indicate the used length of `prefix_path`. `has_root_val` flag, and `saturated_ff_val_or_child` flag.

* val_or_child_bitfield: 24-element bitfield = 3 Bytes.  Indicates whether each payload in `payloads` is a value or a link.

* prefix_path: `[u8; 4]`, 4 Bytes.  Provides a short prefix path between the node's root and the multi-branching location.

* payloads: `[PayloadRef; 24]`, 24 Bytes.  References to all child links or values contained within the node.  If the node contains a root value (`has_root_val == 1`), it will be stored in `payloads_table[23]`

* child_mask: `ByteMask`, 32 Bytes.  Contains the bitfield that will be returned by `child_mask`

### Discussion

QUESTION: We can trade a few prefix path bytes for payload table slots or vice versa, depending on what the data tells us.

QUESTION: Do we want to stash the number of utilized slots in `payloads`?  Allows for fast paths for a few functions that would otherwise require 4 `popcnt` operations (or a 256-bit compare in the case of `is_empty`).  But we'd need to give up a child or a path prefix byte to get it.

QUESTION: We might want a "medium-saturated" format that could store up to 55ish or 88ish children before going all the way to a saturated node.  Depending on the utilization we find.

## ByteSaturatedHead Chunk Format

The `ByteSaturatedHead` format is needed to represent a fully saturated byte node.  One issue with a straightforward format in the same spirit as the others, however, is that a single saturated location (i.e. a location at which all or most children are occupied) will exceed the capacity of the `NodeBlock`'s `payloads_table` entries.  Therefore the chunk format needs to store the full 64-bit values or `TrieNodeODRc` links.  Also, to avoid the nasty requirement to copy and reformat large amounts of data in order to add or remove children in the middle of a heavily saturated node, a single logical node can be broken up across multiple chunk formats.

A `ByteSaturatedHead` chunk begins life as a `ByteUnsaturated` chunk, and has all the same fields.  However, when it needs to be upgraded to a `ByteSaturatedHead`, the payloads are migrated from the `NodeBlock` into new `ByteSaturatedBody` nodes, and the `payloads` field in this `ByteSaturatedHead` node is updated to reference the new `ByteSaturatedBody` chunks.

Allocation can be skipped for `ByteSaturatedBody` chunks that have no set values.  Given the fact that encoding algorithms often cluster values together (i.e. integers, printable ascii, etc.) it has been observed to be common to have large runs of unused children even for nodes that have 60+ children.

Mapping from a set bit in the `child_mask` to a location of a child node or value is acomplished with the following algorithm:
```rust, ignore
if (byte & 0xF) != 0xF {
  let body_node = get_node_from_payload_ref(self.payloads[byte >> 4]);
  let (body_node, idx) = (body_node, byte & 0xF);
  body_node.payloads[idx]
} else {
  let idx = self.payloads[byte >> 4];
  if idx != 0xF {
    let body_node = get_node_from_payload_ref(self.payloads[16]);
    body_node.payloads[idx]
  } else {
    let is_child = self.header.get_bit(saturated_ff_val_or_child);
    get_child_or_value_from_payload_ref(self.payloads[17], is_child);
  }
}
```

## ByteSaturatedBody Chunk Format

A `ByteSaturatedBody` spans 4 continguous chunks and can represent 15 child nodes.  A `ByteSaturatedBody` is **always** part of one and only one `ByteSaturatedHead`, and therfore its `refcount` must be 1.  Otherwise it indicates a bug.

A `ByteSaturatedBody` contains the following fields:

* payloads: `[ValOrChild; 15]` = 120 Bytes.  Links to 15 full values or full `TrieNodeODRc` nodes.

* metadata: 15-element bitfield = 2 Bytes.  Stores a bit indicating whether each payload is a value or a child.

* usused: 6 Bytes.  Could contain an `active` bitfield, used for debug asserts.  Otherwise unused, for now.

### Discussion

An alternative implementation is to break a `ByteSaturatedBody` into 4 non-contiguous 32-Byte section chunks, and use the usused bytes in section 0 to specify the location of sections 1..3.  This is equally dense, but trades the requirement to find contiguous 4-byte chunks for extra indirection.

`ByteSaturatedBody` chunks are the only place aside from a `NodeBlock`'s `payloads_table` where references to another node can be stored.  This means a GC on node blocks needs to be aware of them in order to function, which probably means we need to make a not block aware of all the chunks slots that represent `ByteSaturatedBody` chunks.  Maybe this could be done with a sentinel value in the associated `ref_counts`.

## StraightPath Chunk Format

The `StraightPath` format is the most efficient way to represent a long uninterrupted path.  It packs 29 key bytes into a single 32 Byte chunk with the following fields.

* common_header: `u8` = 1 Byte.  3-bits of tag, Bit 3 == `end_is_used`, Bit 4 == `end_val_or_child`, Bit 5 == `has_root_val` (only needed once the changes described in [A.0001_map_root_values.md] are implemented.), Bits 6 & 7 = `unused`.

* length: 1 Byte.  Bits [0..5] == `path_len`.

* end_payload: `PayloadRef`, 1 Byte.  The payload at the end of the path.

* path_bytes: `[u8; 29]`.  The segment of the key.  If the `has_root_val` flag is set, then `path_bytes[28]` is reinterpreted as the root value `PayloadRef`.

### Discussion

QUESTION: Should we allow the `end_payload` space to be used as an extra path byte if `V` is a zero-sized type?  We can use the `end_is_used` flag to distinguish a dangling path from a value.

## LOUDS Chunk Format

The `LOUDSChunkFormat` format represents a subtree with up to 8 payloads, with up to 18 total path bytes, arranged throughout the tree.  A crate to interpret the LOUDS bit strings can be found here: https://crates.io/crates/louds-rs.  I don't know how efficient that crate is, but it's probably a good starting point.

The format consists of the following fields packed into a single 32 Byte chunk.

* common_header: `u8` = 1 Byte.  3-bits of tag, flag = `has_root_val`, 4-bits of `unused`.

* path_bytes: `[u8; 18]`, 18 Bytes.  A 1-1 mapping with nodes encoded in the `louds_bit_string`

* endpoint_metadata: An 8-element bitfield = 1 Byte.  Each bit in this bitfield indicates whether the associated endpoint is a value or a link.

  GOAT OUTDATED.  IGNORE THIS PARAGRAPH endpoint_metadata: 8 2-bit tags = 2 Bytes.  Each tag encodes one of the following meanings: `[val, link, both, root]`, from which a mapping between an end-point in the LOUDS structure and an index in endpoints_table can be derived.  A `val` or `link` tag means 1 idx in `endpoints_table` is occupied; a `both` tag means 2 are occupied.  Therefore, the mapping function needs to take the whole `endpoint_metadata` `u16` into account, however this can be done cheaply with some bitwise arithmatic and a LUT.

* louds_bit_string: `[u8; 4]`, 4 Bytes.  A LOUDS bit string representing the structure of the subtrie.

* endpoints_table: `[PayloadRef; 8]`, 8 Bytes.  Stores the PayloadRefs for the values or links associated with each endpoint in the LOUDS tree.  If `has_root_val` is set, then the PayloadRef pointing to the root value will be stored at `endpoints_table[7]`.

  GOAT OUTDATED.  IGNORE THIS PART.  If `endpoint_metadata[0] == root`, then `endpoints_table[0]` will be a value associated with the root (zero-length path), once the changes described in [A.0001_map_root_values.md] are implemented.

### Discussion

QUESTION: The format described above does not allow values to be expressed along the path, only at path endpoints, with the root being a special case.  However, we could modify the LOUDS format to encode values as virtual children that don't get their own path bytes.  The limited experimentation I have done make me thing this is more complicated, but perhaps I am wrong.

QUESTION: Do we want to sacrifice a little bit of capacity for some pre-computed information that would speed up access without parsing the whole `louds_bit_string`?

QUESTION: Should we encode the existance of a root value in the `louds_bit_string`, rather than the `endpoint_metadata`?  It takes zero space in the `endpoint_metadata`.

QUESTION: Do we need the length (in bits) of the `louds_bit_string`?  It looks like we can infer it from the last endpoint node having no children.  But perhaps there is an optimization to knowing the length.

QUESTION: We could represent the bit_string in a depth-first encoding, rather than LOUDS' breadth-first.  This will make traversal more efficient at the cost of making computing a child mask more expensive.  My feeling is that LOUDS' breadth-first encoding probably wins.  But we'd need to try some experiments.

### Examples of the LOUDS Chunk Format

Example 1: Pair
```txt
(h)
 |-----+
(e)   (o)
 |     |
(l)   (w)
 |     |
(l)   (d)
 |     |
(o)   (y)

path_bytes: [h, e, o, l, w, l, d, o, y]
endpoint_metadata: [link, val, ...]
endpoints_table: [Link_o, Val_y, ...]
louds_bit_string: `1,0 | 1,1,0 | 1,0 | 1,0 | 1,0 | 1,0 | 1,0 | 1,0 | 0 | 0`
```

## Pair Chunk Format

Probably unneeded, as it only allows for a handful more path bytes above the LOUDS format.  A dedicated pair format could support a path length up to 29 bytes in total, while the LOUDS format is limited to 19 path bytes.  But a pair format probably doesn't have much reason to be, between the flexibility of the LOUDS format, and the simplicity of the StraightPath format.

## Star Chunk Format

A format appropriate for zero-sized V types, able to express dangling paths or paths terminating in values with only 2 bits-per-path.

GOAT TODO...  We should probably measure whether a Star node would ever get used.  In addition to identifying other node formats we could design to address frequently observed patterns.

{{#include api_links.md}}
