//! Tests that a value on a path which is a *proper prefix* of other paths survives structural
//! mutation of the trie.
//!
//! These slots -- the ones holding both a value and a child link -- are where value loss hides.  A
//! slot with only one of the two cannot lose anything, so bugs in copy-on-write, node upgrades and
//! grafting show up here and nowhere else.  The suite was written while packing the value-presence
//! flag into the child pointer (see the `experiment/cofree-pointer-packing` branch), which broke
//! six existing tests and one case no existing test covered; it is kept on the main line because
//! the property it checks is worth pinning down whatever the representation.

use pathmap::PathMap;
use pathmap::ring::{Lattice, DistributiveLattice};
use pathmap::zipper::{ZipperMoving, ZipperWriting, ZipperValues, ZipperIteration};

/// Paths chosen so that many are proper prefixes of others, and so the trie is wide enough at the
/// root to force dense nodes
fn prefix_heavy() -> Vec<Vec<u8>> {
    let mut paths = vec![];
    for b in 0u8..64 {
        paths.push(vec![b]);
        paths.push(vec![b, b]);
        paths.push(vec![b, b, b]);
        paths.push(vec![b, b, b, 0]);
    }
    paths
}

fn build(paths: &[Vec<u8>]) -> PathMap<u64> {
    let mut m = PathMap::new();
    for (i, p) in paths.iter().enumerate() { m.set_val_at(&p[..], i as u64); }
    m
}

#[track_caller]
fn assert_intact(m: &PathMap<u64>, paths: &[Vec<u8>], extra: usize, what: &str) {
    for (i, p) in paths.iter().enumerate() {
        assert_eq!(m.get_val_at(&p[..]), Some(&(i as u64)), "{what}: lost the value at {p:?}");
    }
    assert_eq!(m.val_count(), paths.len() + extra, "{what}: value count changed");
}

#[test]
fn values_survive_copy_on_write_of_a_shared_trie() {
    let paths = prefix_heavy();
    let original = build(&paths);

    //Aliasing the trie means every write below has to clone the nodes on its path, replacing
    //child links in slots that also hold values
    let alias = original.clone();
    let mut copy = original.clone();
    for b in 0u8..64 {
        copy.set_val_at(&[b, b, b, 1][..], 9999);
    }

    assert_intact(&alias, &paths, 0, "aliased handle");
    assert_intact(&original, &paths, 0, "original");
    for b in 0u8..64 {
        assert_eq!(copy.get_val_at(&[b, b, b, 1][..]), Some(&9999));
    }
}

#[test]
fn values_survive_node_upgrades_under_a_write_zipper() {
    let paths = prefix_heavy();
    let mut m = build(&paths);

    //Fanning out under an existing prefix forces list nodes to grow into dense nodes while their
    //slots still hold values
    {
        let mut wz = m.write_zipper_at_path(b"\x00");
        //bytes 64.. are untouched by the fixture, so nothing existing is overwritten
        for b in 64u8..=255 { wz.descend_to(&[b][..]); wz.set_val(7); wz.reset(); }
    }
    for b in 64u8..=255 {
        assert_eq!(m.get_val_at(&[0u8, b][..]), Some(&7), "the newly written value at [0,{b}] is there");
    }
    assert_intact(&m, &paths, 192, "after node upgrades");
}

#[test]
fn values_survive_grafting_over_a_slot_that_has_one() {
    let paths = prefix_heavy();
    let mut m = build(&paths);
    let donor: PathMap<u64> = build(&[b"zz".to_vec(), b"zzz".to_vec()]);

    //Grafting replaces the child link of a slot that already holds a value
    {
        let mut wz = m.write_zipper_at_path(b"\x01\x01");
        wz.graft(&donor.read_zipper());
    }
    //NOTE: with the default `graft_root_vals` feature the value *at* the focus is part of the
    //graft, so [1,1] takes the donor's (absent) root value.  The value above it must be untouched.
    assert_eq!(m.get_val_at(&[1u8][..]), Some(&4), "the value above the graft point survived");
    assert!(m.get_val_at(&[1u8, 1, b'z', b'z'][..]).is_some(), "the grafted subtrie is present");
    //and every other prefix value in the trie is unaffected
    for b in 2u8..64 {
        assert_eq!(m.get_val_at(&[b][..]), Some(&((b as u64)*4)), "value at [{b}]");
        assert_eq!(m.get_val_at(&[b, b][..]), Some(&((b as u64)*4 + 1)), "value at [{b},{b}]");
    }
}

#[test]
fn values_survive_algebra_on_prefix_heavy_tries() {
    let paths = prefix_heavy();
    let a = build(&paths);
    let b = build(&paths);

    let joined = a.join(&b);
    assert_intact(&joined, &paths, 0, "join");
    let met = a.meet(&b);
    assert_eq!(met.val_count(), paths.len(), "meet");
    assert!(a.subtract(&b).is_empty(), "subtract of equals");

    //And the values must still be reachable by iteration, not just by lookup
    let mut z = joined.read_zipper();
    let mut seen = 0;
    while z.to_next_val() { assert!(z.val().is_some()); seen += 1; }
    assert_eq!(seen, paths.len());
}

#[test]
fn a_slot_with_both_value_and_child_round_trips_through_removal() {
    let paths = prefix_heavy();
    let mut m = build(&paths);

    //Removing the value from a slot that also has a child must leave the child alone, and vice versa
    for b in 0u8..64 {
        let path = [b];
        let mut wz = m.write_zipper_at_path(&path[..]);
        assert!(wz.remove_val(false).is_some(), "value at [{b}] was already gone");
    }
    for b in 0u8..64 {
        assert_eq!(m.get_val_at(&[b][..]), None);
        assert_eq!(m.get_val_at(&[b, b][..]), Some(&((b as u64)*4 + 1)), "child subtrie of [{b}] survived");
        assert_eq!(m.get_val_at(&[b, b, b, 0][..]), Some(&((b as u64)*4 + 3)));
    }
}
