//! Exercises the copy-on-write counters in isolation (an integration test binary runs as its own
//! process, so the process-wide counters see only this test's writes).
#![cfg(feature = "counters")]

use pathmap::counters::{cow_counters, reset_cow_counters};
use pathmap::PathMap;

#[test]
fn cow_counters_split_unshared_and_shared_writes() {
    reset_cow_counters();

    // Writes into an unshared trie never clone: every make_unique call finds a unique node.
    let mut map: PathMap<usize> = PathMap::new();
    for (i, key) in [&b"romane"[..], b"romanus", b"romulus", b"rubens"].iter().enumerate() {
        map.set_val_at(key, i);
    }
    let unshared = cow_counters();
    assert!(unshared.make_unique_calls > 0, "writes must route through make_unique");
    assert_eq!(unshared.cow_clones, 0, "an unshared trie must never clone on write");

    // Once another handle aliases the trie, a write must clone every shared node on its path.
    let shared_handle = map.clone();
    map.set_val_at(b"romanes", 4);
    let shared = cow_counters();
    assert!(shared.cow_clones >= 1, "writing an aliased trie must record at least one clone");
    assert!(shared.cow_clones <= shared.make_unique_calls);
    assert_eq!(shared_handle.get_val_at(b"romane"), Some(&0), "the aliased handle is unaffected");
    assert_eq!(shared_handle.get_val_at(b"romanes"), None);

    // After the aliasing handle is gone, fresh writes stop cloning.
    drop(shared_handle);
    map.set_val_at(b"ruber", 5);
    let reunified = cow_counters();
    assert_eq!(
        reunified.cow_clones, shared.cow_clones,
        "writes after the alias is dropped must not clone (the path was already un-shared by the previous write, and sole ownership needs no copies)"
    );

    reset_cow_counters();
    let zeroed = cow_counters();
    assert_eq!((zeroed.make_unique_calls, zeroed.cow_clones), (0, 0));
}
