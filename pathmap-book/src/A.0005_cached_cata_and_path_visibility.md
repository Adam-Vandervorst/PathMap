# Cached Structural Catamorphism (partial path visibility)

## The problem

A full path argument is incompatible with a cached catamorphism because path information that is incorporated into the generation of the `W` value means that `W` value is no longer suitable for use in another place with a different prefix path.

However, eliminating the `path` argument entirely (as is currently done for the non-debug cached `cata` methods) might be overly strict and limit some legitimate use cases.

## Discussion

Adam said:
> I'm currently using the path argument in the experimental MORKL interpreter; Specifically, MORKL programs are represented variable-free as a trie where everything is inlined.  This is a huge exponential blow-up of the program, but it's mitigated by the sharing in the space.
>
> Now I re-introduced variables *as absolute paths in the program* because we don't have a serialization format the maintains sharing and this works because two invariants: the caching cata folding in order, and the absolute paths in the program referring to the first subtrie.
>
> So let's find a way around this... alternatively, I can look into formats that maintain sharing again.

LP said: have 3 answers, depending on timeframe.

1. The `_debug` method preserves the old behavior.  And, in spite of "debug" in the name, it's still available in release builds.  It's basically identical to the old behavior.  But I hate that answer.  Although it keeps this PR merge from creating a functionality regression in the short term.
2. I think the ACT format absolutely *should* be made to support sharing.  As opposed to providing yet another format.  I'm not sure about the challenges associated with making that work, but from a user-facing perspective, the ACT format should fill the niche of "compact read-only format".  Meaning we should engineer sharing into the format, even if it means creating a v2 of the format. Because sharing is pretty damn important for compactness.  (aside: I think we should engineer in compression into ACT as well.  Possibly through a 2-tier addressing scheme and compressing blocks individually.  But that's not relevant to this PR.)
3. But this use case makes me realize we want a cata API that enables both caching and paths.

So... caching and paths... How are those not fundamentally incompatible?

Consider this reframe: if instead of a trie of bytes, we have a trie of expressions, where each expression is conceptually defined as:
```rust
enum Expr {
    Sym(String),
    Var(usize),
    Expr(Vec<Expr>)
}
```
In other words, a caching cata absolutely should be able to work at the `Expr` level, and cache entire exprs, including all nested children.  But for us the issue is that the arity (and other header) info is potentially stored above the share point, making it impossible to access.  Even if it is accessible, it's just not convenient to assemble it from the child_masks and jump sub_paths provided by the current byte-wise API.

There are two directions I see here:

1. Make a "structure-aware" catamorphism (cata at first, but this will likely set the precedent for other morphisms as well).  Something that traverses the trie *as if* it were the above structure (or any structure, controllable via a traversal closure that can access paths)...  I haven't thought through the details here, but I already see some hairy issues.  Not saying it won't work, but it needs a lot more thinking.
2. Make a "hybrid" cata.  In this implementation, the closure would get a full `path` arg, but the closure must return `(W, usize)`, to inform the implementation how many trailing path bytes were used to construct the `W`.  Then, the partial path could be hashed along with the node_id to determine if the result was appropriate for sharing.

The biggest downside I see to API choice 2 is that it sounds easy to misunderstand and therefore misuse.  And misuses might be subtle and hard to detect.

However, API 1 could be implemented in terms of API 2, and through that lens, API 1 would be higher runtime overhead for not much practical gain.

Another consideration is whether we want a solution that extends beyond just catamorphism to other morphisms that may take advantage of caching in a more nuanced way.  E.g. a situation where paths within a subtrie is parameterized by information from earlier in the path (but not a strict prefix on the subtrie), but there are still multiple instances of the same parameter-subtrie combo.  My instinct is that situation is too complicated to capture with a morphism and people should just use zipper ops at that point, but it's not a settled question.

## Current Thinking

* Eventually support a `logical_cached_cata` (name subject to debate) that provides a path arg to the closure, and the prefix that becomes part of the cached value's hash (option 2).

* Update ACT format and zipper to support structural sharing.

{{#include api_links.md}}
