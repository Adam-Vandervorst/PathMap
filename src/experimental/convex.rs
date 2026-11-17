//! Stable convex algebra on valued paths, preserving left-hand payloads.
//!
//! `meet(A,B) = live(A ∩ B, Hull(A) ∩ Hull(B))` and
//! `subtract(A,B) = live(A, Hull(A) \ B)`. In particular, a masked interior
//! survives if it supports a surviving original tip. `live(X, T)` selects the
//! paths in `X` that prefix a tip in `T`; `Hull` selects prefix-maximal valued
//! paths. Bare paths are not tips.
//!
//! The zipper and physical-node implementations are independent postorder
//! traversals. Neither materializes Hull, iterates pruning rounds, enumerates
//! pairs of keys, nor computes subtree cardinalities. Unaffected subtrees are shared.
//!
//! Geometry observes values only: a path is a tip when it has a value and no
//! strictly descending value. The result preserves left payloads without a
//! `Lattice` bound. Bare structure may be retained by sharing, so agreement with
//! Lean's canonical mixed-map adapters is by valued lookup, not bare locations.
//!
//! The zipper uses a heap stack. Native kernels recurse at branching nodes and
//! peel unary spines onto a heap stack (including valued spines). With fixed
//! node capacities, time is linear in inspected overlap, first-witness fringes,
//! and copying/writing work, with O(height) scratch space. Shared DAG nodes
//! are counted per visited occurrence.
//! Witness searches stop at the first value, but a wholly bare fringe requires
//! a full scan. Replacing an output also incurs its destruction/COW cost.
//!
//! ```
//! use pathmap::{PathMap, experimental::convex::{convex_meet, convex_subtract}};
//! let mut a = PathMap::new();
//! for (p, v) in [("a", 1), ("ab", 2), ("ac", 3)] { a.set_val_at(p, v); }
//! let mut b = PathMap::new();
//! b.set_val_at("a", ()); b.set_val_at("ab", ());
//! assert_eq!(convex_meet(&a, &b).val_count(), 2);
//! let difference = convex_subtract(&a, &b);
//! assert_eq!(difference.get_val_at("a"), Some(&1)); // supports surviving ac
//! assert_eq!(difference.get_val_at("ab"), None);
//! assert_eq!(difference.get_val_at("ac"), Some(&3));
//! ```

mod native;
mod zipper;

pub use native::{convex_meet, convex_subtract};
pub use zipper::{zipper_convex_meet, zipper_convex_subtract};

#[derive(Clone, Copy, Default)]
struct Summary {
    /// The summarized subtree contains an original value.
    live: bool,
    /// The summarized subtree contains a retained value.
    kept: bool,
}

impl Summary {
    fn include(&mut self, other: Self) {
        self.live |= other.live;
        self.kept |= other.kept;
    }
}

// Here the summary covers strict descendants of the candidate value.
// Testing original liveness prevents a newly exposed interior becoming
// a tip during stable pruning. Right liveness is needed only at a candidate tip.
#[inline]
fn keep_value<const SUBTRACT: bool>(
    s: Summary,
    right_val: bool,
    right_live: impl FnOnce() -> bool,
) -> bool {
    if SUBTRACT {
        s.kept || (!s.live && !right_val)
    } else {
        right_val && (s.kept || (!s.live && !right_live()))
    }
}
