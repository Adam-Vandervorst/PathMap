
# Separation of algebraic policy from value type

Problems with current design.

Proposal

## Values policy


## Subtrie policy

octree example

Restrict & restricting as meet policies

### Invalidated Assumptions

#### Commutativity

Meet and join are assumed to be commutative, and therefore some implementations simply flip the order of arguments for code reuse.

#### Strict increase / decrease

Several parts of the code currently make the assumption that join will strictly increase the number of elements / size of a trie, and likewise meet and subtract will strictly reduce it.  Neither of these assumptions hold with configurable policies.

## Open Questions

### Is the value policy separate from the subtrie policy, or an argument to it?

GOAT

### Are join and meet (and subtract) still fundamentally different?

Do we need a separate API for a join policy, meet policy, and subtract policy?  Or is every operation with the same argument signature just a policy?  with a single set of entry-points on the zippers (and on PathMap) to perform that operation?

### Is there an ergonomics reason to keep policy types separate?

Even if we conclude that it is only the function signature that differentiates policies, it still sounds mind-meltingly-wrong to do something silly like using a join subtrie policy with a meet value policy.  So should the API have type-level opinions about this?

### Is "policy" the right word? Or have we come full circle back to "lattice"?

That's the question.  Do we need more terminology?

{{#include api_links.md}}
