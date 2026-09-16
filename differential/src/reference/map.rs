//! `Map.lean` — the `PathMap` surface.
//!
//! A `pathmap::PathMap` *is* a map: the value at the empty path is the map's
//! root value.  Almost every `PathMap` method is implemented in `pathmap` by
//! opening a temporary zipper at the root and delegating, and the model does the
//! same, so the two layers cannot drift apart.
//!
//! The one genuinely map-level operation is [`restrict`], which differs from
//! [`Zip::restrict`]: it consults the *root value* of the right-hand map, which a
//! node-level `prestrict` cannot see.

use crate::reference::basic::{ByteMask, ValOps};
use crate::reference::pathmap::{Entry, PathMap};
use crate::reference::zipper::Zip;

/// `PathMap::new`.
pub fn new<V: Clone>() -> PathMap<V> {
    PathMap::empty()
}

/// `PathMap::single`.
pub fn single<V: Clone>(p: &[u8], v: V) -> PathMap<V> {
    let mut t = PathMap::empty();
    t.set_val(p, v);
    t
}

/// A read/write zipper at the root of the map.
pub fn zipper<V: Clone>(t: PathMap<V>) -> Zip<V> {
    Zip::new(t)
}

/// A zipper rooted at `p` (`read_zipper_at_path` / `write_zipper_at_path`).
/// The zipper cannot ascend above `p`, and its `val()` at the root is the
/// map's value at `p`.
pub fn zipper_at<V: Clone>(t: PathMap<V>, p: &[u8]) -> Zip<V> {
    Zip::at(t, p)
}

/// `PathMap::get_val_at` / `get`.
pub fn get_val_at<'a, V: Clone>(t: &'a PathMap<V>, p: &[u8]) -> Option<&'a V> {
    t.val_at(p)
}

/// `PathMap::contains`: whether there is a **value** at `p`.
///
/// Not the same question as `path_exists_at`, and the gap between them is the
/// bare case: a path created by `create_path`, or left behind by
/// `remove_val(false)`, exists but is not contained.
pub fn contains<V: Clone>(t: &PathMap<V>, p: &[u8]) -> bool {
    match t.entry_at(p) {
        Entry::Valued(_) => true,
        Entry::Bare | Entry::Absent => false,
    }
}

/// `PathMap::path_exists_at`.
pub fn path_exists_at<V: Clone>(t: &PathMap<V>, p: &[u8]) -> bool {
    t.path_exists(p)
}

/// `PathMap::set_val_at` / `insert`.
pub fn set_val_at<V: Clone>(t: &mut PathMap<V>, p: &[u8], v: V) -> Option<V> {
    t.set_val(p, v)
}

/// `PathMap::remove_val_at` / `remove` (`remove` passes `prune = true`).
pub fn remove_val_at<V: Clone>(t: &mut PathMap<V>, p: &[u8], prune: bool) -> Option<V> {
    with_zipper_at(t, p, |z| z.remove_val(prune))
}

/// `PathMap::val_count`.
pub fn val_count<V: Clone>(t: &PathMap<V>) -> usize {
    t.val_count(&[])
}

/// `PathMap::is_empty`.
pub fn is_empty<V: Clone>(t: &PathMap<V>) -> bool {
    t.is_empty_map()
}

/// `PathMap::create_path`.
pub fn create_path<V: Clone>(t: &mut PathMap<V>, p: &[u8]) -> bool {
    with_zipper_at(t, p, |z| z.create_path())
}

/// `PathMap::prune_path`.
pub fn prune_path<V: Clone>(t: &mut PathMap<V>, p: &[u8]) -> usize {
    with_zipper_at(t, p, |z| z.prune_path())
}

/// `PathMap::remove_branches_at`.
pub fn remove_branches_at<V: Clone>(t: &mut PathMap<V>, p: &[u8], prune: bool) -> bool {
    with_zipper_at(t, p, |z| z.remove_branches(prune))
}

/// All key/value pairs, in depth-first (lexicographic) key order —
/// `PathMap::iter`.
pub fn iter<V: Clone>(t: &PathMap<V>) -> Vec<(Vec<u8>, V)> {
    t.vals().map(|(k, v)| (k.clone(), v.clone())).collect()
}

/// `PathMap::join`: union, root values included.
pub fn join<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
    PathMap::join(ops, a, b)
}

/// `PathMap::meet`: intersection, root values included.
pub fn meet<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
    PathMap::meet(ops, a, b)
}

/// `PathMap::subtract`: difference, root values included.
pub fn subtract<V: Clone>(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
    PathMap::sub(ops, a, b)
}

/// `PathMap::restrict`: keep the paths of `a` that have *some* prefix
/// carrying a value in `b`.
///
/// The empty prefix counts here, so a root value in `b` validates everything
/// and the result is `a` unchanged (root value included).  Otherwise the
/// result never has a root value, because a node-level `prestrict` has no
/// slot for one.  This is the documented behaviour of `PathMap::restrict`,
/// and it is *not* what [`Zip::restrict`] does.
pub fn restrict<V: Clone>(a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
    if b.val_at(&[]).is_some() {
        a.clone()
    } else {
        PathMap::restrict_below_root(a, b)
    }
}

/// Every `PathMap` method above that mutates is `pathmap`'s "open a temporary
/// zipper at the root, descend, delegate" — spelled out once here so the two
/// layers cannot drift apart.
fn with_zipper_at<V: Clone, R>(
    t: &mut PathMap<V>,
    p: &[u8],
    f: impl FnOnce(&mut Zip<V>) -> R,
) -> R {
    let mut z = Zip::new(std::mem::take(t));
    z.descend_to(p);
    let r = f(&mut z);
    *t = z.trie;
    r
}

/// Re-exported so callers of [`Zip::remove_unmasked_branches`] have a mask to
/// hand without reaching for the crate's own.
pub fn full_mask() -> ByteMask {
    ByteMask::full()
}
