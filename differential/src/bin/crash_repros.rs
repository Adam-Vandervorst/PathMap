//! Minimal reproducers for failures `crash_fuzz` turned up.  See
//! `differential/CRASH_FINDINGS.md` for the write-up.
//!
//!     cargo run -p differential --bin crash_repros -- --list
//!     cargo run -p differential --bin crash_repros -- <name>
//!
//! Each case ends the process (panic, abort or segfault), so run them one at a
//! time.  Where a debug build fails earlier on an assertion, the case says so.

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

fn sample() -> PathMap<u64> {
    let mut m = PathMap::new();
    for p in [&[1u8, 2, 1][..], &[1, 2, 1, 0], &[1, 2, 1, 3, 3], &[0], &[2, 2]] {
        m.set_val_at(p, 7);
    }
    m
}

fn owned_head_second_exclusive_path() {
    let zh = sample().into_zipper_head(&[1u8]);
    drop(zh.write_zipper_at_exclusive_path(&[]));
    let _ = zh.write_zipper_at_exclusive_path(&[9u8]); // UB: segfault / unreachable_unchecked
}
fn write_zipper_head_second_exclusive_path() {
    let mut map = sample();
    let mut wz = map.write_zipper_at_path(&[1u8]);
    let zh = wz.zipper_head();
    drop(zh.write_zipper_at_exclusive_path(&[]));
    let _ = zh.write_zipper_at_exclusive_path(&[]); // zipper_head.rs:347
}
fn head_read_zipper_get_trie_ref() {
    let mut map = sample();
    let zh = map.zipper_head();
    let rz = zh.read_zipper_at_path(&[1u8]).unwrap();
    let _ = rz.get_trie_ref(); // zipper.rs:1871
}
fn product_zipper_is_shared() {
    let (a, b) = (sample(), sample());
    let mut z = ProductZipper::new(a.read_zipper_at_path(&[1u8, 2, 1]), [b.read_zipper()]);
    while z.to_next_step() {
        let _ = z.is_shared(); // zipper.rs:2644 once the focus is in the second factor
    }
}
fn product_zipper_val_count() {
    let mut a = PathMap::<u64>::new();
    a.set_val_at([1u8, 2], 1);
    let mut b = PathMap::<u64>::new();
    b.set_val_at([3u8, 4], 1);
    let mut z = ProductZipper::new(a.read_zipper(), [b.read_zipper()]);
    loop {
        let _ = z.val_count(); // zipper.rs:3048 (debug: product_zipper.rs:178)
        if !z.to_next_step() { break }
    }
}
fn graft_child_maps_long_root() {
    let mut map = PathMap::<u64>::new();
    let mut wz = map.write_zipper_at_path(&[0u8; 48]);
    wz.graft_child_maps(ByteMask::from_iter([1u8]), [PathMap::single([2u8], 5)], false); // write_zipper.rs:2557/2560
}
fn owned_read_zipper_witness() {
    let mut map = PathMap::<u64>::new();
    map.set_val_at([1u8], 1);
    let z = map.into_read_zipper(&[]);
    let w = z.witness();
    let _ = z.get_val_with_witness(&w); // zipper.rs:3332 (debug: zipper.rs:3328)
}
fn prefix_zipper_k0_after_last_path() {
    let mut map = PathMap::<u64>::new();
    map.set_val_at([0x22u8], 1);
    let mut z = PrefixZipper::new(&[2u8, 3][..], map.read_zipper());
    z.descend_to_byte(2);
    z.descend_last_path();
    z.descend_last_path();
    z.descend_first_k_path(0); // prefix_zipper.rs:571
}

const CASES: &[(&str, fn(), &str)] = &[
    ("owned_head_second_exclusive_path", owned_head_second_exclusive_path, "undefined behaviour: segfault in release, unreachable_unchecked in debug"),
    ("write_zipper_head_second_exclusive_path", write_zipper_head_second_exclusive_path, "zipper_head.rs:347 unwrap (debug: write_zipper.rs:1337 assertion)"),
    ("head_read_zipper_get_trie_ref", head_read_zipper_get_trie_ref, "zipper.rs:1871 explicit panic"),
    ("product_zipper_is_shared", product_zipper_is_shared, "zipper.rs:2644 unwrap"),
    ("product_zipper_val_count", product_zipper_val_count, "zipper.rs:3048 unwrap (debug: product_zipper.rs:178 assertion)"),
    ("graft_child_maps_long_root", graft_child_maps_long_root, "write_zipper.rs:2560 slice out of range"),
    ("owned_read_zipper_witness", owned_read_zipper_witness, "zipper.rs:3332 slice out of range (debug: zipper.rs:3328 assertion)"),
    ("prefix_zipper_k0_after_last_path", prefix_zipper_k0_after_last_path, "prefix_zipper.rs:571 slice out of range"),
];

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "--list".into());
    if arg == "--list" {
        for (name, _, what) in CASES {
            println!("{name:40} {what}");
        }
        return;
    }
    match CASES.iter().find(|(name, _, _)| *name == arg) {
        Some((_, case, _)) => {
            case();
            println!("{arg}: no failure (fixed?)");
        }
        None => {
            eprintln!("unknown case {arg}; see --list");
            std::process::exit(2);
        }
    }
}
