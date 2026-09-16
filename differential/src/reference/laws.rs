//! `Spec.lean` §2 — checkable laws.
//!
//! Metamorphic properties relating *different* API functions: "`join` is
//! commutative", "`take_map` then `graft_map` is the identity", "`drop_head`
//! undoes `insert_prefix`".
//!
//! Each returns `true` when it holds, so the same function can serve as a unit
//! test over the fixture battery *and* as a runtime assertion on every state a
//! fuzzer reaches.  A property that holds in the model but fails in `pathmap` is
//! a crate bug; one that fails in both is a spec bug.  Both are worth finding,
//! which is why the laws are kept separate from the definitions.
//!
//! The Lean model's §1 — the *proved* theorems about the cursor algebra — has no
//! counterpart here.  Those are proofs, not tests; see
//! `lean/PathMapModel/Spec.lean`.

use crate::reference::basic::{AlgStatus, ByteMask, ValOps, path};
use crate::reference::map;
use crate::reference::pathmap::{Entry, PathMap};
use crate::reference::zipper::Zip;

/// Every location carrying a value exists.
///
/// Structurally true of any [`PathMap`] — a value cannot be recorded at a
/// location that is not in the map — so a failure here means a map was built
/// by hand rather than through the constructors.
pub fn vals_exist<V: Clone>(t: &PathMap<V>) -> bool {
    t.vals().all(|(k, _)| t.path_exists(k))
}

/// The set of existing locations is closed under taking prefixes.
pub fn prefix_closed<V: Clone>(t: &PathMap<V>) -> bool {
    t.path_exists(&[]) && t.paths().all(|q| path::prefixes(q).all(|r| t.path_exists(r)))
}

/// `child_mask` lists exactly the bytes whose child location exists.
pub fn child_mask_agrees<V: Clone>(t: &PathMap<V>, p: &[u8]) -> bool {
    let m = t.child_mask(p);
    m.bytes().iter().all(|&b| t.path_exists(&path::push(p, b)))
        && t.paths().all(|q| {
            if q.len() == p.len() + 1 && q.starts_with(p) { m.contains(q[p.len()]) } else { true }
        })
}

/// `val_count` at the root counts exactly the entries of `iter`.
pub fn val_count_agrees<V: Clone>(t: &PathMap<V>) -> bool {
    t.val_count(&[]) == t.vals().count()
}

/// After `set_val` the focus is a location carrying exactly that value.
///
/// One `Entry` case, rather than "the value is `v`" and "the path exists"
/// checked separately — the second was only there because the first could not
/// say it.
pub fn set_val_then_val<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>, v: V) -> bool {
    let mut z = z.clone();
    z.set_val(v.clone());
    match z.entry() {
        Entry::Valued(w) => ops.beq(w, &v),
        Entry::Bare | Entry::Absent => false,
    }
}

/// `remove_val` clears the value but leaves the location dangling — which is
/// to say the focus ends up exactly [`Entry::Bare`].
pub fn remove_val_leaves_path<V: Clone>(z: &Zip<V>) -> bool {
    if !z.path_exists() {
        return true;
    }
    let mut z = z.clone();
    z.remove_val(false);
    z.entry().is_bare()
}

/// `create_path` makes the focus exist; a second call reports "already there".
pub fn create_path_idempotent<V: Clone>(z: &Zip<V>) -> bool {
    if z.at_root() {
        return true;
    }
    let mut z = z.clone();
    z.create_path();
    let existed = z.path_exists();
    let again = z.create_path();
    existed && !again && z.path_exists()
}

/// `prune_path` undoes a `create_path` that dangled off an existing location.
///
/// **Precondition: the location it dangles off must survive the prune.**
/// `create_path` adds one child to the deepest existing ancestor `a` of the
/// focus, and `prune_path` then walks back up to the first location that
/// carries a value, branches, or is the *map* root — it does not stop at the
/// zipper root (see [`Zip::prune_path`]).  So when `a` is itself a dangling
/// tip, the prune sweeps `a` up as well and the map does not come back.  With
/// `{[] , [2]}` and a zipper rooted at `[2]` focused at `[2,0]`, create then
/// prune leaves `{[]}`: `[2]` is gone.  Verified to hold in the Lean model
/// too, so this is the law's scope, not a divergence.
///
/// `Check.lean` never sees it because every zipper in its battery is rooted
/// at `[]`; check [`create_then_prune_applies`] before asserting this one.
pub fn create_then_prune<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    if z.at_root() || z.path_exists() {
        return true;
    }
    let mut w = z.clone();
    w.create_path();
    w.prune_path();
    w.trie.beq_t(ops, &z.trie)
}

/// Whether [`create_then_prune`]'s precondition holds: the deepest existing
/// ancestor of the focus is the map root, carries a value, or already has a
/// child — in each case it still qualifies as a stop once `create_path` has
/// hung one more child off it.
pub fn create_then_prune_applies<V: Clone>(z: &Zip<V>) -> bool {
    let f = z.focus();
    match path::deepest_proper_prefix(&f, |a| z.trie.path_exists(a)) {
        Some(a) => a.is_empty() || z.trie.val_at(a).is_some() || z.trie.child_count(a) >= 1,
        None => true,
    }
}

/// `descend_to_existing` always lands on an existing location, provided the
/// focus existed when it was called.
pub fn descend_to_existing_lands<V: Clone>(z: &Zip<V>, k: &[u8]) -> bool {
    if !z.path_exists() {
        return true;
    }
    let mut z = z.clone();
    z.descend_to_existing(k);
    z.path_exists()
}

/// `descend_indexed_byte` lands on an existing location for every valid index,
/// and the byte it reports is the byte it landed on.
pub fn descend_indexed_lands<V: Clone>(z: &Zip<V>) -> bool {
    (0..z.child_count()).all(|i| {
        let mut w = z.clone();
        match w.descend_indexed_byte(i) {
            Some(b) => w.path_exists() && w.focus_byte() == Some(b),
            None => false,
        }
    })
}

/// `to_next_sibling_byte` and `to_prev_sibling_byte` are mutually inverse —
/// **but only from an existing location**.
///
/// From an off-map focus the round trip fails, and correctly so: the sibling
/// moves are defined by the parent's `child_mask`, which does not contain the
/// current byte, so `next_bit` jumps to some larger set byte and `prev_bit`
/// comes back to a *different* one.  A caller that steps sideways from a
/// non-existent path cannot expect to step back.
pub fn sibling_round_trip<V: Clone>(z: &Zip<V>) -> bool {
    if !z.path_exists() {
        return true;
    }
    let mut w = z.clone();
    match w.to_next_sibling_byte() {
        None => true,
        Some(b) => {
            w.focus_byte() == Some(b)
                && w.to_prev_sibling_byte().is_some()
                && w.path == z.path
        }
    }
}

/// `descend_until_observed` reports exactly the bytes it descended.
///
/// A blind zipper has no `path()`, so this sequence is its only account of
/// where it went; it must equal the path delta.
#[allow(clippy::nonminimal_bool)] // stated as the Lean law is, not simplified
pub fn descend_until_observed_exact<V: Clone>(z: &Zip<V>) -> bool {
    let mut w = z.clone();
    let (moved, obs) = w.descend_until_observed();
    w.path == path::cat(&z.path, &obs) && moved == !obs.is_empty()
}

/// `ascend_until` never ascends past the zipper's root, and reports the exact
/// distance travelled.
pub fn ascend_until_accounts<V: Clone>(z: &Zip<V>) -> bool {
    let mut w = z.clone();
    let n = w.ascend_until();
    w.path.len() + n == z.path.len() && z.path.len() >= n
}

/// `to_next_val` enumerates values in strictly increasing depth-first order
/// and finishes at the root.
pub fn to_next_val_monotone<V: Clone>(z: &Zip<V>) -> bool {
    let mut w = z.clone();
    if w.to_next_val() {
        z.path < w.path && w.is_val()
    } else {
        w.at_root()
    }
}

/// `join` is commutative **on locations**, but not on values.
///
/// `pathmap`'s `u64` (and `usize`, `u32`, `u16`, `u8`) `Lattice` instances
/// define `pjoin` as `Identity(SELF_IDENT)` — a left-biased projection.  So
/// joining two maps that disagree at a key keeps whichever value belongs to
/// the receiver, and `a.join(b)` and `b.join(a)` differ.  The *set of paths*
/// is still symmetric, and that is what this law asserts.  Any test that
/// assumes value-level commutativity is asserting something the crate does not
/// promise for these value types.
pub fn join_comm_on_paths<V: Clone>(
    ops: &impl ValOps<V>,
    a: &PathMap<V>,
    b: &PathMap<V>,
) -> bool {
    let ab = PathMap::join(ops, a, b);
    let ba = PathMap::join(ops, b, a);
    ab.paths().collect::<Vec<_>>() == ba.paths().collect::<Vec<_>>()
        && ab.vals().map(|(k, _)| k).collect::<Vec<_>>()
            == ba.vals().map(|(k, _)| k).collect::<Vec<_>>()
}

/// `join` is idempotent.
pub fn join_idem<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>) -> bool {
    PathMap::join(ops, a, a).beq_t(ops, a)
}

/// `join` is associative, values included: left-biasing is itself associative.
pub fn join_assoc<V: Clone>(
    ops: &impl ValOps<V>,
    a: &PathMap<V>,
    b: &PathMap<V>,
    c: &PathMap<V>,
) -> bool {
    let l = PathMap::join(ops, &PathMap::join(ops, a, b), c);
    let r = PathMap::join(ops, a, &PathMap::join(ops, b, c));
    l.beq_t(ops, &r)
}

/// `meet` is idempotent *on values*.  It is not idempotent on locations: a
/// meet discards dangling paths, so `meet a a` keeps only the value-bearing
/// skeleton.
pub fn meet_idem_on_vals<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>) -> bool {
    PathMap::meet(ops, a, a).vals().map(|(k, _)| k.clone()).collect::<Vec<_>>()
        == a.vals().map(|(k, _)| k.clone()).collect::<Vec<_>>()
}

/// Subtracting a map from itself leaves no values.
pub fn sub_self_empty_vals<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>) -> bool {
    PathMap::sub(ops, a, a).vals().next().is_none()
}

/// `restrict a a = a`.  This is the law that caught a real `prestrict` bug —
/// see `tests/pathmap_algebra_differential.rs`.
///
/// **Precondition: every location of `a` leads to a value.**  The Lean
/// model's justification — "every path of `a` is validated by the value at
/// its own end" — assumes every path *ends* at a value, which is exactly what
/// `create_path` and `remove_val(false)` make false.  On
/// `PathMap::empty().add_path(&[0])` the law fails, in this model and in the
/// Lean one alike: `[0]` has no valued prefix, so `restrict` drops it.
/// `Check.lean`'s six fixtures all happen to satisfy the precondition, which
/// is why the `#guard` holds there; a fuzzer reaching a dangling path does
/// not, so check [`restrict_self_applies`] before asserting this one.
pub fn restrict_self<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>) -> bool {
    map::restrict(a, a).beq_t(ops, a)
}

/// Whether [`restrict_self`]'s precondition holds: every non-root location of
/// `a` has a value at or above it.
pub fn restrict_self_applies<V: Clone>(a: &PathMap<V>) -> bool {
    a.paths().all(|q| q.is_empty() || PathMap::validated_by(a, q))
}

/// `take_map` followed by `graft_map` restores the map exactly.
pub fn take_then_graft<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let mut w = z.clone();
    let m = w.take_map(false).unwrap_or_else(PathMap::empty);
    w.graft_map(&m);
    w.trie.beq_t(ops, &z.trie)
}

/// Grafting one submap into two places makes two *independent* copies:
/// writing under one leaves the other exactly as it was.
///
/// In the model this cannot fail — a [`PathMap`] is a flat map of entries, so
/// the two copies are separate elements and there is no aliasing to leak
/// through.  The law is stated anyway for two reasons: it is what the crate
/// must do (`graft` clones a refcounted pointer, so the copies really are
/// shared until copy-on-write separates them), and it would catch a model
/// that grew sharing of its own.
///
/// See FINDINGS.md #16: the crate gets this right where it completes, but
/// aborts when the shared submap contains a dangling path.
pub fn grafted_copies_independent<V: Clone>(
    ops: &impl ValOps<V>,
    s: &PathMap<V>,
    a: &[u8],
    b: &[u8],
    k: &[u8],
    v: V,
) -> bool {
    let mut z = Zip::at_path(PathMap::empty(), &[], a);
    z.graft_map(s);
    let mut z = Zip::at_path(z.trie, &[], b);
    z.graft_map(s);
    let both = z.trie.clone();
    let mut z = Zip::at_path(z.trie, &[], &path::cat(a, k));
    z.set_val(v);
    both.subtrie(b).beq_t(ops, &z.trie.subtrie(b))
}

/// `graft` copies the source submap: after grafting, `make_map` at the
/// destination equals `make_map` at the source.
pub fn graft_then_make_map<V: Clone>(
    ops: &impl ValOps<V>,
    dst: &Zip<V>,
    src: &Zip<V>,
) -> bool {
    let mut d = dst.clone();
    d.graft(src);
    d.make_map().beq_t(ops, &src.make_map())
}

/// `drop_head k` undoes `insert_prefix` of a `k`-byte prefix, as documented
/// on `ZipperWriting::insert_prefix`.
///
/// Only the *branches* are compared: `insert_prefix` does not move the focus
/// value, and `drop_head` discards values at depth exactly `k`, so the focus
/// value plays no part on either side.
pub fn drop_head_undoes_insert_prefix<V: Clone>(
    ops: &impl ValOps<V>,
    z: &Zip<V>,
    pre: &[u8],
) -> bool {
    if z.focus_node_is_empty() || pre.is_empty() {
        return true;
    }
    let mut w = z.clone();
    w.insert_prefix(pre);
    w.join_k_path_into(ops, pre.len(), false);
    w.focus_node().beq_t(ops, &z.focus_node())
}

/// `join_into` with an empty source is a no-op and reports `Identity` (or
/// `None` when the destination is empty too).
pub fn join_empty_identity<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let src = Zip::new(PathMap::empty());
    let mut w = z.clone();
    let st = w.join_into(ops, &src);
    let want = if z.focus_node_is_empty() { AlgStatus::None } else { AlgStatus::Identity };
    w.trie.beq_t(ops, &z.trie) && st == want
}

/// Joining a zipper into itself is the identity, and reports it.
pub fn join_self_identity<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let src = z.clone();
    let mut w = z.clone();
    let st = w.join_into(ops, &src);
    let want = if z.focus_node_is_empty() { AlgStatus::None } else { AlgStatus::Identity };
    w.trie.beq_t(ops, &z.trie) && st == want
}

/// `remove_branches` empties the focus but preserves its value.
pub fn remove_branches_keeps_val<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let mut w = z.clone();
    w.remove_branches(false);
    w.focus_node_is_empty()
        && match (z.val(), w.val()) {
            (None, None) => true,
            (Some(a), Some(b)) => ops.beq(a, b),
            _ => false,
        }
}

/// `remove_unmasked_branches` with a full mask changes nothing.
pub fn remove_unmasked_full_mask<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let mut w = z.clone();
    w.remove_unmasked_branches(&ByteMask::full(), false);
    w.trie.beq_t(ops, &z.trie)
}

/// `remove_unmasked_branches` with an empty mask equals `remove_branches`.
pub fn remove_unmasked_empty_mask<V: Clone>(ops: &impl ValOps<V>, z: &Zip<V>) -> bool {
    let mut a = z.clone();
    a.remove_unmasked_branches(&ByteMask::of_list([]), false);
    let mut b = z.clone();
    b.remove_branches(false);
    a.trie.beq_t(ops, &b.trie)
}
