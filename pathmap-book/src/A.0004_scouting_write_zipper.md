# Scouting write zipper

## The problem

Current WriteZipper movement changes the trie more than is necessary.  For example, descending a WZ past a share point will cause the in-memory nodes to become preemptively unique even before any chamges are made through the methods that would be expected to modify the trie.

The reason for this is that the trie keeps a stack of mutable node references, and obtaining one of them requires calling `make_mut` on the `TrieNodeODRc`.

### Example

Adam asks: "Why is re-traversal necessary?  Why can't we just coerce the read-ptr to a write ptr?"

Consider the trie produced by this code:
```rust
# extern crate pathmap;
# use pathmap::PathMap;
let paths = &["atropine", "botox", "colchicine", "digitalis"];
let mut shared = PathMap::<()>::new();

let mut wz = shared.write_zipper();
for path in paths {
    wz.move_to_path(b"compounds:");
    wz.descend_to(path.as_bytes());
    wz.set_val(());
}

let mut map = PathMap::<()>::new();
let mut wz = map.write_zipper();

//Most medicines need special care
wz.descend_to("keep_in_the_pharmacy:");
wz.graft_map(shared.clone());
wz.move_to_path("handle_with_care:");
wz.graft_map(shared.clone());

//Add some more poisons
wz.move_to_path("handle_with_care:compounds:endrin");
wz.set_val(());
wz.move_to_path("handle_with_care:compounds:fluorine");
wz.set_val(());
wz.move_to_path("handle_with_care:compounds:gyromitrin");
wz.set_val(());

//Watch what happens to the trie sharing before and after adding the additional poisons
let mut out_buf = Vec::new();
use pathmap::viz::{viz_maps, DrawConfig};
let cfg = DrawConfig{ ascii: true, hide_value_paths: false, minimize_values: true, logical: true };
viz_maps(&[map], &cfg, &mut out_buf).unwrap();
println!("```mermaid\n{}```", std::str::from_utf8(&out_buf).unwrap());
```

The sharing happens at the node associated with `compounds:`. But the write zipper would have a focus node somewhere around the split to each compound.  It must go up the trie to unique the nodes.  Otherwise we would have just added a bunch of poisons to our pharmacy.

But it's actually even worse.  If there were another zipper on `keep_in_the_pharmacy:` (because we used a `ZipperHead` at the `map` root), it is possible the writing in `handle_with_care:` could have modified the trie in such a way that the zipper in `keep_in_the_pharmacy` is now holding a pointer to garbage.

## Solution(s)

My current proposed solution is to essentilly postpone the `make_mut` operation until it's needed.  This would entail traversing the zipper using ordinary `as_tagged` accessors, and maintaining a stack of tagged (read-only) node refs for the top (most descended) portion of the stack.  Then when a trie modification was actually needed, the implementation would need to re-traverse those nodes to obtain unique mutable pointers along the path.

This sounds like twice as much traversal work - and it is, but at least the re-traversal is likely to hit cache.  More importantly, if it saves even a little bit of unnecessary node duplication (and thus breaking sharing) then I feel that it will be a net win.

I'm open to alternative ideas, however.

{{#include api_links.md}}
