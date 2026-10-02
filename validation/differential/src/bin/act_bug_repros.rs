//! Minimal reproducers for the `ArenaCompactTree` defects the Lean differential
//! model turned up.  See `lean/FINDINGS.md`.
//!
//!     cargo run -p differential --bin act_bug_repros -- --list
//!     cargo run -p differential --bin act_bug_repros -- <name>
//!     cargo run -p differential --bin act_bug_repros -- --all

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::zipper::*;

const CASES: &[(&str, &str)] = &[
    ("val_count_ignores_focus", "ACTZipper::val_count() counts from the zipper root, not the focus"),
    ("first_k_path_no_backtrack", "ACTZipper::descend_first_k_path() only walks the leftmost chain"),
    ("last_path_overshoots", "ACTZipper::descend_last_path() runs one byte past the end of the trie"),
    ("roundtrip", "from_zipper round-trips values, root values and dangling paths (this one passes)"),
];

fn src() -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    m.insert(b"aa", 1);
    m.insert(b"ab", 2);
    m.insert(b"b", 3);
    m
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args[0] == "--list" {
        for (n, d) in CASES { println!("{n:26} {d}"); }
        return;
    }
    let names: Vec<&str> = if args[0] == "--all" {
        CASES.iter().map(|(n, _)| *n).collect()
    } else {
        args.iter().map(|s| s.as_str()).collect()
    };
    for n in names {
        println!("### {n}");
        run(n);
    }
}

fn run(name: &str) {
    match name {
        // `val_count` is documented as "the total number of values contained at
        // and below the zipper's focus".  ACT's implementation clones the zipper,
        // calls `reset()` -- moving to the zipper's root -- and counts from there,
        // so the focus is ignored entirely.
        "val_count_ignores_focus" => {
            let m = src();
            let t = ArenaCompactTree::from_zipper(m.read_zipper(), |&v| v);
            for path in [&b""[..], b"a", b"aa", b"b", b"zz"] {
                let mut az = t.read_zipper_u64();
                let mut pz = m.read_zipper();
                az.descend_to(path);
                pz.descend_to(path);
                println!(
                    "  focus {:8?}: exists={:<5} PathMap val_count={}  ACT val_count={}{}",
                    String::from_utf8_lossy(path), pz.path_exists(),
                    pz.val_count(), az.val_count(),
                    if pz.val_count() == az.val_count() { "" } else { "   <-- differs" },
                );
            }
        }

        // The trait specifies a depth-first search for *any* path `k` bytes below
        // the focus.  ACT descends the first child `k` times and gives up if that
        // chain runs out, never trying the other branches.
        "first_k_path_no_backtrack" => {
            let mut m = PathMap::<u64>::new();
            m.insert(b"a", 1);       // leftmost branch is only 1 byte deep
            m.insert(b"bxy", 2);     // this one reaches depth 3
            let t = ArenaCompactTree::from_zipper(m.read_zipper(), |&v| v);
            for k in 1..=3 {
                let mut az = t.read_zipper_u64();
                let mut pz = m.read_zipper();
                let a = az.descend_first_k_path(k);
                let p = pz.descend_first_k_path(k);
                println!(
                    "  k={k}: PathMap -> {p} at {:?}   ACT -> {a} at {:?}{}",
                    pz.path(), az.path(),
                    if a == p { "" } else { "   <-- differs" },
                );
            }
        }

        // `descend_last_path` should stop at the end of the deepest path.  On ACT
        // it takes one step too many, and the position it lands on reports that
        // it exists and holds a value.
        "last_path_overshoots" => {
            let mut m = PathMap::<u64>::new();
            { let mut w = m.write_zipper(); w.set_val(0); }
            m.insert(&[1u8, 0, 0, 0], 5);
            let t = ArenaCompactTree::from_zipper(m.read_zipper(), |&v| v);
            let root = &[1u8, 0][..];
            let mut pz = m.read_zipper_at_path(root);
            let mut az = t.read_zipper_at_path_u64(root);
            // The trigger is a preceding `ascend_until()` at the root.  It is a
            // no-op that returns 0, but it leaves ACT's internal state such that
            // the following `descend_last_path` takes one step too many.  Without
            // it the two agree.
            pz.ascend_until();
            az.ascend_until();
            let p = pz.descend_last_path();
            let a = az.descend_last_path();
            println!("  deepest path in the trie is {:?}", &[1u8, 0, 0, 0]);
            println!("  PathMap -> {p} at {:?} (origin {:?}) exists={} val={:?}",
                     pz.path(), pz.origin_path(), pz.path_exists(), pz.val());
            println!("  ACT     -> {a} at {:?} (origin {:?}) exists={} val={:?}",
                     az.path(), az.origin_path(), az.path_exists(), az.val());
            if az.path().len() > pz.path().len() {
                println!("  <-- ACT descended {} byte(s) past the end, and claims the location exists",
                         az.path().len() - pz.path().len());
            }
        }

        "roundtrip" => {
            let mut m = PathMap::<u64>::new();
            { let mut w = m.write_zipper(); w.set_val(7); }   // root value
            m.insert(b"ab", 1);
            m.create_path(b"zz");                            // dangling path
            let t = ArenaCompactTree::from_zipper(m.read_zipper(), |&v| v);
            let dump = |mut z: Box<dyn FnMut() -> Vec<String>>| z();
            let _ = dump;
            let mut pz = m.read_zipper();
            let mut a = vec![format!("_:{:?}", pz.val())];
            while pz.to_next_step() { a.push(format!("{:?}:{:?}", pz.path(), pz.val())); }
            let mut az = t.read_zipper_u64();
            let mut b = vec![format!("_:{:?}", az.val())];
            while az.to_next_step() { b.push(format!("{:?}:{:?}", az.path(), az.val())); }
            println!("  PathMap: {}", a.join(" "));
            println!("  ACT    : {}", b.join(" "));
            println!("  identical: {}", a == b);
        }

        other => println!("  unknown case {other:?}; try --list"),
    }
}
