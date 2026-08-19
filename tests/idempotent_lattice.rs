//! Tests that [`Lattice::IDEMPOTENT`] and [`DistributiveLattice::IDEMPOTENT`] are honored by the
//! node-level algebra.
//!
//! The trie shares subtries by pointer, so an algebraic operation frequently ends up with the same
//! node on both sides.  For a set-like value (including `()`) the answer can be produced without
//! descending, but for a value type that actually *combines* its operands that shortcut would skip
//! the shared branch instead of combining it.  These tests use such a value type.

use pathmap::PathMap;
use pathmap::ring::*;
use pathmap::zipper::*;

/// A multiplicity in a multiset.  Joining adds occurrences, so joining a subtrie with itself is
/// emphatically not the same as leaving it alone.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Count(u64);

impl Lattice for Count {
    const IDEMPOTENT: bool = false;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        AlgebraicResult::Element(Count(self.0 + other.0))
    }
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        AlgebraicResult::Element(Count(self.0.min(other.0)))
    }
}

impl DistributiveLattice for Count {
    const IDEMPOTENT: bool = false;
    /// Removes a single occurrence, whatever `other` holds
    fn psubtract(&self, _other: &Self) -> AlgebraicResult<Self> {
        if self.0 > 1 {
            AlgebraicResult::Element(Count(self.0 - 1))
        } else {
            AlgebraicResult::None
        }
    }
}

const PATHS: &[&[u8]] = &[b"aaa", b"aab", b"abc", b"bbb", b"bbcd"];

fn counted(n: u64) -> PathMap<Count> {
    let mut map = PathMap::new();
    for path in PATHS {
        map.set_val_at(path, Count(n));
    }
    map
}

/// Guards the premise of every test below: cloning a `PathMap` shares the root node by pointer, so
/// the operations really do see the same node on both sides.  If this ever stops being true the
/// tests below would still pass while testing nothing.
#[track_caller]
fn assert_shares_root(a: &PathMap<Count>, b: &PathMap<Count>) {
    let (za, zb) = (a.read_zipper(), b.read_zipper());
    assert!(za.is_shared() && zb.is_shared(), "test premise broken: root node is not shared");
    assert_eq!(za.shared_node_id(), zb.shared_node_id(), "test premise broken: roots are different nodes");
}

#[test]
fn non_idempotent_pjoin_descends_shared_subtries() {
    let a = counted(1);
    let b = a.clone();
    assert_shares_root(&a, &b);

    let joined = a.join(&b);
    for path in PATHS {
        assert_eq!(joined.get_val_at(path), Some(&Count(2)), "at {path:?}");
    }
}

#[test]
fn non_idempotent_join_into_descends_shared_subtries() {
    let mut a = counted(1);
    let b = a.clone();
    assert_shares_root(&a, &b);

    a.join_into(b);
    for path in PATHS {
        assert_eq!(a.get_val_at(path), Some(&Count(2)), "at {path:?}");
    }
}

#[test]
fn non_idempotent_write_zipper_join_into_descends_shared_subtries() {
    let mut dst = counted(1);
    let src = dst.clone();
    assert_shares_root(&dst, &src);

    let mut wz = dst.write_zipper();
    wz.join_into(&src.read_zipper());
    drop(wz);

    for path in PATHS {
        assert_eq!(dst.get_val_at(path), Some(&Count(2)), "at {path:?}");
    }
}

#[test]
fn non_idempotent_psubtract_descends_shared_subtries() {
    let a = counted(3);
    let b = a.clone();
    assert_shares_root(&a, &b);

    //One occurrence comes off each path; the paths survive
    let once = a.subtract(&b);
    for path in PATHS {
        assert_eq!(once.get_val_at(path), Some(&Count(2)), "at {path:?}");
    }

    //Repeat until the multiplicities run out, at which point the paths do go away
    let twice = once.subtract(&a);
    let thrice = twice.subtract(&a);
    for path in PATHS {
        assert_eq!(twice.get_val_at(path), Some(&Count(1)), "at {path:?}");
        assert_eq!(thrice.get_val_at(path), None, "at {path:?}");
    }
    assert!(thrice.is_empty());
}

#[test]
fn idempotent_default_still_short_circuits_correctly() {
    //`()` and other set-like values keep the default `IDEMPOTENT = true`, and joining or
    //subtracting a shared subtrie against itself must still give set semantics
    let a: PathMap<()> = PATHS.iter().copied().collect();
    let b = a.clone();

    let joined = a.join(&b);
    assert_eq!(joined.val_count(), PATHS.len());
    for path in PATHS {
        assert_eq!(joined.get_val_at(path), Some(&()), "at {path:?}");
    }

    let met = a.meet(&b);
    assert_eq!(met.val_count(), PATHS.len());

    assert!(a.subtract(&b).is_empty());
}
