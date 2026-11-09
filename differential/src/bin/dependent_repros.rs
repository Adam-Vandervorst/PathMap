//! Standalone reproducers for the `DependentProductZipperG` findings in
//! `lean/findings/dependent.md`.  Each prints what it observes and what would
//! hold if the zipper presented a fixed trie.
//!
//! `cargo run --release -p differential --bin dependent_repros`

use pathmap::zipper::*;
use pathmap::PathMap;

fn d1_root_joint() {
    // A primary rooted at a leaf (here: an empty map), and a closure that
    // returns a factor there.
    let primary = PathMap::<u64>::new();
    let mut factor = PathMap::<u64>::new();
    factor.set_val_at([1u8], 7);
    let enroll = |_: (), _p: &[u8], n: usize| ((), if n == 0 { Some(factor.read_zipper()) } else { None });
    let mut z = DependentProductZipperG::new_enroll(primary.read_zipper(), (), enroll);
    let fresh = (z.child_count(), z.clone().to_next_val());
    z.descend_to(&[] as &[u8]);
    let after_empty_descend = (z.child_count(), z.clone().to_next_val());
    z.reset();
    let after_reset = z.child_count();
    println!("D1 root joint: (child_count, to_next_val) fresh {fresh:?}, after descend_to([]) \
              {after_empty_descend:?}, child_count after reset {after_reset}");
    println!("   expected: the same at all three (the root has not moved)");
}

fn d2_empty_factor() {
    // At the joint [0] the closure returns an empty factor, then (asked again,
    // since the joint is still a leaf) one holding [2].
    let mut a = PathMap::<u64>::new();
    a.set_val_at([0u8], 1);
    let empty = PathMap::<u64>::new();
    let mut b = PathMap::<u64>::new();
    b.set_val_at([2u8], 2);
    let enroll = |_: (), _p: &[u8], n: usize| {
        ((), match n { 0 => Some(empty.read_zipper()), 1 => Some(b.read_zipper()), _ => None })
    };
    let mut z = DependentProductZipperG::new_enroll(a.read_zipper(), (), enroll);
    z.descend_to_byte(0);
    let before = z.child_count();
    z.descend_to(&[] as &[u8]);
    let after = z.child_count();
    let mut z = DependentProductZipperG::new_enroll(a.read_zipper(), (), enroll);
    let mut vals = vec![];
    while z.to_next_val() {
        vals.push((z.path().to_vec(), z.val().copied()));
    }
    println!("D2 empty factor: child_count at [0] {before}, after descend_to([]) {after}; \
              to_next_val walk {vals:?}");
    println!("   expected: child_count 1 both times; walk [([0], Some(1)), ([0, 2], Some(2))]");
}

fn d3_val_at() {
    // Primary {[0]: 0}; at the joint [0] the factor is the primary again.
    let mut a = PathMap::<u64>::new();
    a.set_val_at([0u8], 0);
    let enroll = |_: (), _p: &[u8], n: usize| ((), if n == 0 { Some(a.read_zipper()) } else { None });
    let z = DependentProductZipperG::new_enroll(a.read_zipper(), (), enroll);
    let at = z.val_at([0u8, 0]).copied();
    let get_at = z.get_val_at([0u8, 0]).copied();
    let mut moved = z.clone();
    moved.descend_to([0u8, 0]);
    let mut joint = z.clone();
    joint.descend_to_byte(0);
    println!("D3 val_at across a joint: val_at([0,0]) {at:?}, get_val_at([0,0]) {get_at:?}, \
              descend_to([0,0]) then val() {:?}; from [0], val_at([0]) {:?}",
             moved.val().copied(), joint.val_at([0u8]).copied());
    println!("   expected: all four Some(0)");
}

fn d4_path_indices() {
    let mut a = PathMap::<u64>::new();
    a.set_val_at([0u8], 0);
    let enroll = |_: (), _p: &[u8], n: usize| ((), if n == 0 { Some(a.read_zipper()) } else { None });
    let mut z = DependentProductZipperG::new_enroll(a.read_zipper(), (), enroll);
    z.descend_to_byte(0);
    println!("D4 at the joint [0]: focus_factor {}, path_indices {:?}", z.focus_factor(), z.path_indices());
    println!("   documented: path_indices().len() == focus_factor()");
}

fn main() {
    d1_root_joint();
    d2_empty_factor();
    d3_val_at();
    d4_path_indices();
}
