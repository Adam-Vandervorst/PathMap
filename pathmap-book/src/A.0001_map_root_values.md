
# Discussion on Map Root Values, get_value, set_value, and Zippers

Quite a lot of complexity (and a not-insignificant cost) comes from the outgrowth of the [`set_value`] / [`get_value`] API on [`PathMap`] and the zipper types.  This is because it is possible to call them with a zero-length path or with the zipper focus positioned at the root.

Conceptually the PathMap abstracts a `[CoFree; 256]` at each byte in the map.  Which means there is no conceptual location for a root value.  In the implementation it means each PathMap structure also needs to hold and `Option<V>` in addition to a root node, and each [`Zipper`] type needs to have a pointer to the root value in addition to the root node.

This means `PathMap` structures are bigger in memory and zippers are more expenseive to create, not to mention all the special case code paths dealing with root values.

Older versions of the code had the concept of rooted and un-rooted zippers, but this was a perennial foot gun and only partially addressed the problem.  It became unworkable with the introduction of the ZipperHead API, and was ultimately removed.

## Alternative: Redoing the public API to rework value access

As with many tradeoffs in software, making something simpler in one place often pushes the complexity elsewhere, and this situation is no exception.

So, let's explore what would be involved getting rid of the `root_value` (which I am taking as an assumption a priori has very little actual utility beyond making the API behave in a consistent and useable way)

Beginning with the API, firstly we would need to change the `get_value` / `set_value` zipper methods to require a path (or at least a byte), as opposed to simply operating on the focus.  A zero-length path would need to be disallowed and become a usage error leading to an immediate panic.

But we still need to be able to access a value at every location in the trie (save the absolute map root).  So we would do this by positioning the zipper's focus one level above the location the user needs to access.

But what how does the user access a value at the root of a zipper (not the map root, but a zipper rooted from a path within the map)?  The zipper would need to be lifted up one byte, but the same problem exists at that level too.

This becomes tricky when the the [`ZipperHead`] assigns exclusive paths to zippers.  The only way this can work is if multiple zippers are allowed to be positioned at the same focus path, but able to access exclusive (disjoint) sub-paths below that focus.

A simplification of that idea is that a given zipper is allowed to access one and only one specific byte below its root position.  This solves the problem, but leads to questions around the correct behavior of the `child_mask` API, and what should happen if the client attemps to modify an invalid path relative to the zipper's root.

This still may be preferable to the currently-implemented design however, as it's a more faithful abstraction of the underlying structure and leads to a tighter fast-path

## Alternative 2: Redo the abstract node interface to change CoFree assumption

The node contract expressed throught the `TrieNode` trait dictates that a node never holds a value at its root.  Instead the current trait dictates that an associated value is owned by the parent.  However this mismatch is in tension with the external API.

I think my preferred fix would be to change the trait methods to reflect the implications of values associated with node roots.

For example, a ByteNode currently is defined (conceptually) as:
```rust, ignore
    pub struct ByteNode<V> {
        mask: [u64; 4],
        values: Vec<CoFree<V>>,
    }
    pub struct CoFree<V> {
        rec: Option<TrieNodeODRc<V>>,
        value: Option<V>
    }
```

Under the new proposal, it'd be defined (conceptually) as:
```rust, ignore
    pub struct ByteNode<V> {
        root: Option<V>,
        mask: [u64; 4],
        values: Vec<ValOrChild<V>>,
    }
    pub enum ValOrChild<V> {
        Val(V),
        Child(TrieNodeODRc<V>)
    }
```

## Path Forward

Either of these changes have the promise to greatly simplify the code and probably can reduce zipper movement overheads by a bit (guessing 10% or so since they don't really effect memory coherence or density and those are the big wins).

I personally believe Alternative 2 is a better option, not least because I think the external API is actually ok as it is and avoiding big changes to that limits the disruption to the internals of PathMap.  However both options imply a massive amount of churn.

Therefore, I think much more complete fuzz tests are a prerequisite to embarking on either change.

{{#include api_links.md}}
