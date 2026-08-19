//! Tests that skipping the value-drop arms in the node drop paths (for value types that need no
//! drop work) doesn't skip drops for value types that do.
//!
//! Two cases matter, and they are distinguished by different halves of the predicate:
//!   * a value with drop glue of its own
//!   * a value with *no* drop glue that is nonetheless too large to live inline in a node slot, and
//!     is therefore boxed on the heap.  Nothing here can observe that leak directly; run this under
//!     `cargo miri test` to check it.

use std::sync::atomic::{AtomicIsize, Ordering::SeqCst};

use pathmap::PathMap;
use pathmap::zipper::{ZipperMoving, ZipperWriting};

static LIVE: AtomicIsize = AtomicIsize::new(0);

/// A value that keeps count of how many instances are alive
#[derive(Debug)]
struct Tracked(#[allow(dead_code)] u64);

impl Tracked {
    fn new(n: u64) -> Self {
        LIVE.fetch_add(1, SeqCst);
        Self(n)
    }
}
impl Clone for Tracked {
    fn clone(&self) -> Self {
        Self::new(self.0)
    }
}
impl Drop for Tracked {
    fn drop(&mut self) {
        LIVE.fetch_sub(1, SeqCst);
    }
}

/// No drop glue, but 64 bytes is far past what a node slot stores inline, so it is heap-allocated
#[derive(Clone, Copy, PartialEq, Debug)]
struct Big([u8; 64]);

/// Paths chosen to produce a mix of node shapes: leaves holding one and two values, values sitting
/// above branches, and a fan-out wide enough to force a dense node
fn paths() -> Vec<Vec<u8>> {
    let mut paths: Vec<Vec<u8>> = vec![
        b"a".to_vec(),
        b"ab".to_vec(),
        b"abc".to_vec(),
        b"abd".to_vec(),
        b"az".to_vec(),
        b"a-very-long-path-that-will-not-fit-inside-a-single-list-node-key".to_vec(),
    ];
    for byte in 0u8..=255 {
        paths.push(vec![b'w', byte]);
    }
    paths
}

#[test]
fn values_with_drop_glue_are_still_dropped() {
    assert_eq!(LIVE.load(SeqCst), 0, "another test leaked into this one");

    let mut map: PathMap<Tracked> = PathMap::new();
    for (i, path) in paths().iter().enumerate() {
        map.set_val_at(path, Tracked::new(i as u64));
    }
    assert!(LIVE.load(SeqCst) > 0);

    //Exercise the paths that drop a value without dropping the whole node
    let mut wz = map.write_zipper();
    wz.descend_to(b"abc");
    assert!(wz.remove_val(false).is_some());
    wz.reset();
    wz.descend_to(b"abd");
    assert!(wz.remove_val(true).is_some());
    wz.reset();
    wz.descend_to(b"w");
    assert!(wz.remove_branches(true));
    drop(wz);

    //And a clone, so the node drop paths run against a shared trie too
    let copy = map.clone();
    drop(map);
    drop(copy);

    assert_eq!(LIVE.load(SeqCst), 0, "values were leaked");
}

#[test]
fn large_values_without_drop_glue_round_trip() {
    let mut map: PathMap<Big> = PathMap::new();
    for (i, path) in paths().iter().enumerate() {
        map.set_val_at(path, Big([i as u8; 64]));
    }
    for (i, path) in paths().iter().enumerate() {
        assert_eq!(map.get_val_at(path), Some(&Big([i as u8; 64])), "at {path:?}");
    }

    let copy = map.clone();
    drop(map);
    for (i, path) in paths().iter().enumerate() {
        assert_eq!(copy.get_val_at(path), Some(&Big([i as u8; 64])), "at {path:?}");
    }
    //The heap allocations behind these values are freed here; miri checks it
    drop(copy);
}

#[test]
fn trivial_values_round_trip_with_the_drop_arms_elided() {
    let all = paths();

    let mut unit: PathMap<()> = PathMap::new();
    let mut small: PathMap<u32> = PathMap::new();
    for (i, path) in all.iter().enumerate() {
        unit.set_val_at(path, ());
        small.set_val_at(path, i as u32);
    }

    assert_eq!(unit.val_count(), all.len());
    assert_eq!(small.val_count(), all.len());
    for (i, path) in all.iter().enumerate() {
        assert_eq!(unit.get_val_at(path), Some(&()), "at {path:?}");
        assert_eq!(small.get_val_at(path), Some(&(i as u32)), "at {path:?}");
    }

    //Removing values leaves the paths dangling when `prune` is false; the node still has to be
    //dropped correctly afterwards
    let mut wz = small.write_zipper();
    wz.descend_to(b"abc");
    assert_eq!(wz.remove_val(false), Some(2));
    drop(wz);
    assert!(small.path_exists_at(b"abc"));
    assert_eq!(small.get_val_at(b"abc"), None);
}
