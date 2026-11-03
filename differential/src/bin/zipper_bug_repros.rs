//! Minimal reproducers for the zipper-API defects the Lean differential model
//! turned up.  See `lean/FINDINGS.md` for the write-up.
//!
//!     cargo run -p differential --bin zipper_bug_repros -- --list
//!     cargo run -p differential --bin zipper_bug_repros -- <name>
//!     cargo run -p differential --bin zipper_bug_repros -- --all       # skips the hang
//!
//! Several cases abort in a debug build (debug assertions / overflow checks) and
//! misbehave silently in release, so each one is selectable individually.

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

fn vals(m: &PathMap<u64>) -> String {
    let v: Vec<String> = m.iter().map(|(k, x)| format!("{k:?}={x}")).collect();
    if v.is_empty() { "<no values>".into() } else { v.join(" ") }
}

fn paths(m: &PathMap<u64>) -> String {
    let mut rz = m.read_zipper();
    let mut v = vec![format!("_{}", mark(rz.val()))];
    while rz.to_next_step() {
        v.push(format!("{:?}{}", rz.path(), mark(rz.val())));
    }
    v.join(" ")
}

fn mark(v: Option<&u64>) -> String {
    match v { Some(x) => format!("={x}"), None => String::new() }
}


const CASES: &[(&str, &str)] = &[
    ("join_into_empty_dst", "join_into silently drops the source when the destination map is empty"),
    ("to_next_val_after_step", "to_next_val misses every downstream value after descend_first_byte / to_next_step / descend_first_k_path"),
    ("sibling_after_iteration", "to_next_sibling_byte fails after the focus was reached by to_next_val"),
    ("root_escape", "a read zipper whose root does not exist walks out of its own root"),
    ("insert_prefix_empty", "insert_prefix(b\"\") destroys the subtrie instead of doing nothing"),
    ("drop_head_zero", "join_k_path_into(0) destroys the subtrie instead of doing nothing"),
    ("prune_reach", "prune_path's depth and reported byte count depend on internal node layout"),
    ("empty_node_leak", "remove_branches / take_map report on node materialisation, not trie state"),
    ("ascend_until_wz", "ascend_until corrupts a write zipper rooted at a node boundary"),
    ("to_next_k_path_borrowed", "to_next_k_path underflows path_len on a borrowed-path zipper"),
    ("prev_sibling_missing", "to_prev_sibling_byte asserts path_exists on a non-existent focus"),
    ("remove_unmasked_dangling", "remove_unmasked_branches asserts inside a dangling line node"),
    ("graft_ambiguous_node", "graft corrupts the destination node when it holds a single line (PANICS)"),
    ("graft_child_maps_dense", "graft_child_maps panics whenever the destination focus is a dense node"),
    ("merkleize_dangling", "merkleize aborts on two identical dangling subtries"),
    ("shared_dangling_cow", "writing into a shared subtrie that holds a dangling path aborts"),
    ("meet_k_path_hang", "meet_k_path_into loops forever when the focus has no children (HANGS)"),
];

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args[0] == "--list" {
        for (name, desc) in CASES {
            println!("{name:26} {desc}");
        }
        return;
    }
    if args[0] == "--all" {
        for (name, _) in CASES {
            if *name == "meet_k_path_hang" {
                println!("\n### meet_k_path_hang: skipped (it does not terminate)");
                continue;
            }
            println!("\n### {name}");
            run(name);
        }
        return;
    }
    for a in &args {
        println!("### {a}");
        run(a);
    }
}

fn run(name: &str) {
    match name {
        // `join_into` reports Identity and writes nothing when the destination
        // map is empty, even though the source subtrie is not.  `graft` from the
        // same read zipper copies it correctly, so the data is reachable; the
        // join just discards it.
        "join_into_empty_dst" => {
            let mut src = PathMap::<u64>::new();
            src.insert(&[0u8, 0, 0, 0], 7);
            let mut rz = src.read_zipper();
            rz.descend_to(&[0u8]);
            println!("  source at [0]: child_count={} val_count={} make_map={}",
                     rz.child_count(), rz.val_count(), vals(&rz.make_map()));

            let mut empty = PathMap::<u64>::new();
            let st = { let mut w = empty.write_zipper(); w.join_into(&rz) };
            println!("  into EMPTY dst    -> {st:?}; dst = {}   <-- source lost", vals(&empty));

            let mut nonempty = PathMap::<u64>::new();
            nonempty.insert(&[9u8], 5);
            let st = { let mut w = nonempty.write_zipper(); w.join_into(&rz) };
            println!("  into NONEMPTY dst -> {st:?}; dst = {}", vals(&nonempty));

            let mut grafted = PathMap::<u64>::new();
            { let mut w = grafted.write_zipper(); w.graft(&rz); }
            println!("  graft into EMPTY  -> dst = {}", vals(&grafted));
        }

        // Three movement operations leave iteration state that makes the next
        // `to_next_val` give up immediately.  Every route below lands the zipper
        // on exactly the same location; only *how it got there* differs.
        "to_next_val_after_step" => {
            let mut map = PathMap::<u64>::new();
            { let mut w = map.write_zipper(); w.set_val(0); }
            map.insert(&[0u8, 0], 7);
            println!("  trie: {}   ([0] exists but holds no value)", paths(&map));
            println!("  each route lands on [0]; to_next_val() should then reach [0,0]");

            type Rz<'a> = pathmap::zipper::ReadZipperUntracked<'a, 'static, u64>;
            let ways: Vec<(&str, Box<dyn Fn(&mut Rz)>)> = vec![
                ("descend_to([0])", Box::new(|z: &mut Rz| { z.descend_to(&[0u8]); })),
                ("descend_to_byte(0)", Box::new(|z: &mut Rz| { z.descend_to_byte(0); })),
                ("descend_indexed_byte(0)", Box::new(|z: &mut Rz| { z.descend_indexed_byte(0); })),
                ("descend_last_byte()", Box::new(|z: &mut Rz| { z.descend_last_byte(); })),
                ("descend_to_existing_byte(0)", Box::new(|z: &mut Rz| { z.descend_to_existing_byte(0); })),
                ("move_to_path([0])", Box::new(|z: &mut Rz| { z.move_to_path(&[0u8]); })),
                ("descend_first_byte()", Box::new(|z: &mut Rz| { z.descend_first_byte(); })),
                ("to_next_step()", Box::new(|z: &mut Rz| { z.to_next_step(); })),
                ("descend_first_k_path(1)", Box::new(|z: &mut Rz| { z.descend_first_k_path(1); })),
            ];
            for (label, f) in &ways {
                let mut z = map.read_zipper();
                f(&mut z);
                assert_eq!(z.path(), &[0u8], "{label} did not land on [0]");
                let r = z.to_next_val();
                println!("    {label:28} -> to_next_val = {r:<5} at {:?}{}",
                         z.path(), if r { "" } else { "   <-- BROKEN" });
            }
            println!("  note descend_first_byte() is documented as having \"identical behavior\"");
            println!("  to descend_indexed_byte(0), yet only the former breaks the iteration.");
            println!("  to_next_get_val() fails identically, since it delegates to to_next_val().");
        }

        // The same stale iteration state as the previous case, with a different
        // victim: here it is `to_next_sibling_byte` that fails, on a sibling that
        // plainly exists.  So the defect is not "to_next_val gives up" -- it is
        // that a token-maintaining move leaves the zipper navigating wrongly.
        "sibling_after_iteration" => {
            let mut m = PathMap::<u64>::new();
            { let mut w = m.write_zipper(); w.set_val(0); }
            m.insert(&[0u8, 0], 0);
            m.insert(&[1u8], 0);
            println!("  trie: {}   (root children are 0 and 1)", paths(&m));

            let mut a = m.read_zipper();
            a.to_next_val();          // -> [0,0]
            a.to_next_val();          // -> [1]
            let ap = a.to_prev_sibling_byte();
            let an = a.to_next_sibling_byte();
            println!("  reached [1] by to_next_val:   prev -> {ap:?}, then next -> {an:?} at {:?}{}",
                     a.path(), if an.is_none() { "   <-- BROKEN" } else { "" });

            let mut b = m.read_zipper();
            b.descend_to(&[1u8]);
            let bp = b.to_prev_sibling_byte();
            let bn = b.to_next_sibling_byte();
            println!("  reached [1] by descend_to:    prev -> {bp:?}, then next -> {bn:?} at {:?}",
                     b.path());
        }

        // `path()` and `at_root()` still say "at my root" while `origin_path()`
        // has moved outside the subtrie the zipper was granted.  A ZipperHead
        // hands out zippers on the assumption that this cannot happen.
        "root_escape" => {
            let mut map = PathMap::<u64>::new();
            map.insert(&[0u8, 0, 3], 161);
            let mut rz = map.read_zipper_at_path(&[0u8, 0, 1]);
            println!("  root=[0,0,1] exists={} origin={:?}", rz.path_exists(), rz.origin_path());
            let moved = rz.to_next_sibling_byte();
            println!("  to_next_sibling_byte->{moved:?} at_root={} path={:?} origin={:?} val={:?}",
                     rz.at_root(), rz.path(), rz.origin_path(), rz.val());
            println!("  <-- the zipper is reading [0,0,3], outside its own root");
        }

        // Documented as the inverse of `drop_head`; with an empty prefix it must
        // be the identity.
        "insert_prefix_empty" => {
            let mut map = PathMap::<u64>::new();
            map.insert(b"ab", 1);
            println!("  before: {}", vals(&map));
            let r = { let mut w = map.write_zipper(); w.insert_prefix(b"") };
            println!("  insert_prefix(b\"\")->{r}; after: {}   <-- expected unchanged", vals(&map));
        }

        // Dropping zero leading bytes must be the identity.
        "drop_head_zero" => {
            let mut map = PathMap::<u64>::new();
            { let mut w = map.write_zipper(); w.set_val(0); }
            for k in [&[0u8][..], &[0, 0], &[1, 0]] { map.insert(k, 0u64); }
            println!("  before: {}", vals(&map));
            let r = { let mut w = map.write_zipper(); w.join_k_path_into(0, false) };
            println!("  join_k_path_into(0)->{r}; after: {}   <-- expected unchanged", vals(&map));
        }

        // `prune_path` is documented not to prune above the zipper's root, and to
        // return the number of bytes removed.  It does prune above the root, and
        // the count it returns switches between absolute and relative depending
        // on where the internal node holding the focus begins.
        "prune_reach" => {
            for len in [8usize, 100] {
                for rootlen in [0usize, 5] {
                    let key: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
                    let mut map = PathMap::<u64>::new();
                    map.insert(&key, 1);
                    let (root, rest) = key.split_at(rootlen);
                    let mut wz = map.write_zipper_at_path(root);
                    wz.descend_to(rest);
                    wz.remove_val(false);
                    let n = wz.prune_path();
                    drop(wz);
                    println!("  chain len={len:3} zipper root depth={rootlen}: prune_path->{n:3} \
                              (absolute={len}, relative={}), map now empty={}",
                             len - rootlen, map.read_zipper().child_count() == 0);
                }
            }
        }

        // Whether an *empty node* happens to be materialised at the focus is
        // representation state, not trie state -- but several return values
        // report on it.
        "empty_node_leak" => {
            let mut map = PathMap::<u64>::new();
            let mut wz = map.write_zipper();
            wz.descend_to(&[0u8]);
            println!("  create_path->{}", wz.create_path());
            println!("  focus: exists={} child_count={} val={:?}",
                     wz.path_exists(), wz.child_count(), wz.val());
            println!("  remove_branches(false)->{}   <-- nothing was removed", wz.remove_branches(false));
            match wz.take_map(false) {
                Some(m) => println!("  take_map->Some(is_empty={})   <-- expected None", m.is_empty()),
                None => println!("  take_map->None"),
            }
        }

        // Panics in debug; in release the write zipper's node stack is left
        // inconsistent and later reads through it are wrong.
        "ascend_until_wz" => {
            let mut src = PathMap::<u64>::new();
            { let mut w = src.write_zipper(); w.set_val(10); }
            src.insert(&[0u8, 0, 0, 0], 11);
            let mut map = PathMap::<u64>::new();
            { let mut w = map.write_zipper_at_path(&[0u8]); w.graft(&src.read_zipper()); }
            println!("  trie: {}", paths(&map));
            let mut wz = map.write_zipper_at_path(&[0u8]);
            println!("  at root: val_count={}", wz.val_count());
            println!("  descend_last_byte->{:?}", wz.descend_last_byte());
            println!("  ascend_until->{}  val_count={} (expected 2)", wz.ascend_until(), wz.val_count());
        }

        // `path_len()` computes `prefix_buf.len() - origin_path.len()` before the
        // path buffer exists.  Debug: overflow panic.  Release: wraps to a huge
        // usize and takes the wrong branch.
        "to_next_k_path_borrowed" => {
            let mut map = PathMap::<u64>::new();
            map.insert(b"ab", 1u64);
            let mut rz = map.read_zipper_at_borrowed_path(b"ab");
            println!("  to_next_k_path(1) on a borrowed-path zipper -> {}", rz.to_next_k_path(1));
        }

        // The default implementation's `debug_assert!(self.path_exists())` fires
        // when the focus never existed to begin with.
        "prev_sibling_missing" => {
            let mut map = PathMap::<u64>::new();
            let mut wz = map.write_zipper();
            wz.descend_to_byte(0);
            println!("  focus exists={}", wz.path_exists());
            println!("  to_prev_sibling_byte -> {:?}", wz.to_prev_sibling_byte());
        }

        "remove_unmasked_dangling" => {
            let mut map = PathMap::<u64>::new();
            map.create_path(&[0u8]);
            let mut wz = map.write_zipper_at_path(&[0u8]);
            println!("  focus exists={} child_count={}", wz.path_exists(), wz.child_count());
            wz.remove_unmasked_branches(ByteMask::EMPTY, false);
            println!("  remove_unmasked_branches(EMPTY) returned");
        }

        // `graft` over a destination whose node holds exactly one line produces a
        // node with both a child at key "\0" and a value at key "\0\0" -- an
        // ambiguous path -- and the node validator aborts.  Grafting a subtrie
        // over an *identical* one is enough to trigger it.
        "graft_ambiguous_node" => {
            std::panic::set_hook(Box::new(|_| {}));
            let go = |dstk: &[&[u8]], srck: &[&[u8]], at: &[u8]| {
                let mut dst = PathMap::<u64>::new();
                for k in dstk { dst.insert(k, 1); }
                let mut src = PathMap::<u64>::new();
                for k in srck { src.insert(k, 8); }
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut d = dst.clone();
                    {
                        let mut wz = d.write_zipper_at_path(at);
                        let mut rz = src.read_zipper();
                        rz.descend_to(at);
                        wz.graft(&rz);
                    }
                    d.iter().map(|(k, v)| (k, *v)).collect::<Vec<(Vec<u8>, u64)>>()
                }))
                .map_err(|_| "PANIC")
            };
            println!("  grafting src's subtrie at `at` over dst's subtrie at the same `at`:");
            for (label, dstk, srck, at) in [
                ("dst={[0,0]} src={[0,3]}   at=[0]", &[&[0u8, 0][..]][..], &[&[0u8, 3][..]][..], &[0u8][..]),
                ("dst={[0,0]} src={[0,0]}   at=[0]", &[&[0u8, 0][..]][..], &[&[0u8, 0][..]][..], &[0u8][..]),
                ("dst={[1,1]} src={[1,3]}   at=[1]", &[&[1u8, 1][..]][..], &[&[1u8, 3][..]][..], &[1u8][..]),
                ("dst={[0]}   src={[0,3]}   at=[0]", &[&[0u8][..]][..], &[&[0u8, 3][..]][..], &[0u8][..]),
                ("dst={[0,0],[9]} src={[0,3]} at=[0]", &[&[0u8, 0][..], &[9u8][..]][..], &[&[0u8, 3][..]][..], &[0u8][..]),
            ] {
                println!("    {label:36} -> {:?}", go(dstk, srck, at));
            }
            println!("  the second line is a graft of a subtrie over an identical one.");
            println!("  a destination with any second branch takes a different node type and survives;");
            println!("  so does calling remove_branches(false) before the graft.");
            let _ = std::panic::take_hook();
        }

        // `graft_child_maps` reaches `node_get_child_mut` with an empty key.
        // That method guards with `debug_assert!(key.len() > 0)` and then indexes
        // `key[0]`, so debug builds trip the assertion and release builds panic
        // on the bounds check.  It fires as soon as the destination's focus node
        // is a `DenseByteNode`, which is any trie with a handful of branches --
        // so the method is unusable on realistic data.
        "graft_child_maps_dense" => {
            std::panic::set_hook(Box::new(|_| {}));
            println!("  destination is a fresh map with N single-byte branches at the root;");
            println!("  grafting one child map over byte 0, remove_unset = false:");
            for n in [1usize, 2, 3, 4, 8] {
                for (rv, br) in [(true, false), (false, true)] {
                    let mut dst = PathMap::<u64>::new();
                    for i in 0..n { dst.insert(&[i as u8, 0], 1); }
                    let mut child = PathMap::<u64>::new();
                    if rv { let mut w = child.write_zipper(); w.set_val(7); }
                    if br { child.insert(&[3u8], 8); }

                    let masked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        let mut d2 = dst.clone();
                        let mut src = PathMap::<u64>::new();
                        { let mut w = src.write_zipper_at_path(&[0u8]); w.graft_map(child.clone()); }
                        let mut wz = d2.write_zipper();
                        wz.graft_masked_branches(&src.read_zipper(), ByteMask::from_iter([0u8]), false);
                    }));
                    let childmaps = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        let mut wz = dst.write_zipper();
                        wz.graft_child_maps(ByteMask::from_iter([0u8]), vec![child], false);
                    }));
                    println!("    root branches={n}  child_root_val={rv:<5} child_branch={br:<5} \
graft_masked_branches={:<5} graft_child_maps={}",
                             if masked.is_ok() { "ok" } else { "PANIC" },
                             if childmaps.is_ok() { "ok" } else { "PANIC" });
                }
            }
            let _ = std::panic::take_hook();
            println!("  (a DenseByteNode is used from ~3 branches up)");

            // Second symptom: grafting *empty* maps.  Grafting nothing must
            // neither create nor destroy a location.  A debug build trips
            // `assertion failed: !src.as_tagged().node_is_empty()`; a release
            // build silently creates the focus as a dangling path.
            println!("\n  empty map, focus descended to the non-existent [0,0],");
            println!("  then graft_child_maps of three EMPTY maps:");
            std::panic::set_hook(Box::new(|_| {}));
            let r = std::panic::catch_unwind(|| {
                let mut m = PathMap::<u64>::new();
                {
                    let mut wz = m.write_zipper();
                    wz.descend_to(&[0u8, 0]);
                    assert!(!wz.path_exists());
                    let maps: Vec<PathMap<u64>> = (0..3).map(|_| PathMap::<u64>::new()).collect();
                    wz.graft_child_maps(ByteMask::from_iter([0u8, 1, 3]), maps, true);
                    wz.path_exists()
                }
            });
            let _ = std::panic::take_hook();
            match r {
                Ok(exists) => println!("    focus exists afterwards = {exists}   <-- expected false"),
                Err(_) => println!("    PANIC (debug assertion !src.node_is_empty()); \
a release build instead creates the path"),
            }
        }

        // `merkleize` replaces identical subtries with references to one copy.
        // Two dangling paths are identical subtries -- both empty -- and it
        // aborts trying to share them.
        "merkleize_dangling" => {
            let mut m = PathMap::<u64>::new();
            m.create_path(&[9u8]);
            m.create_path(&[8u8]);
            println!("  a map holding nothing but two dangling paths, [9] and [8]");
            std::panic::set_hook(Box::new(|_| {}));
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| m.merkleize().reused));
            let _ = std::panic::take_hook();
            match r {
                Ok(n) => println!("  merkleize -> reused {n}"),
                Err(_) => println!("  merkleize -> PANIC (line_list_node.rs, node_replace_child \
unwraps a child that is not there)"),
            }
            println!("  one dangling path alone is fine; it takes two identical ones.");
        }

        // `create_path` leaves an empty node.  Sharing one by grafting and then
        // writing under it puts copy-on-write in the position of having to make
        // an empty sentinel unique, which it asserts against.
        "shared_dangling_cow" => {
            let mut src = PathMap::<u64>::new();
            src.insert(&[1u8], 63);
            src.insert(&[1u8, 2, 0], 45);
            src.create_path(&[3u8]);
            println!("  source: {}   ([3] is dangling)", vals(&src));
            let mut m = PathMap::<u64>::new();
            for spot in [&[0u8][..], &[1u8][..], &[2u8, 2][..]] {
                let mut wz = m.write_zipper_at_path(spot);
                wz.graft(&src.read_zipper());
            }
            println!("  grafted into [0], [1] and [2,2], so the dangling node is shared");
            std::panic::set_hook(Box::new(|_| {}));
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut wz = m.write_zipper_at_path(&[0u8]);
                wz.descend_to(&[3u8, 3]);
                wz.set_val(999);
            }));
            let _ = std::panic::take_hook();
            match r {
                Ok(()) => println!("  writing under [0] -> ok"),
                Err(_) => println!("  writing under [0] -> PANIC (make_unique on an empty sentinel node)"),
            }
        }

        // Does not terminate: `descend_first_k_path`'s default loop cannot make
        // progress when the focus has no children.
        "meet_k_path_hang" => {
            let mut map = PathMap::<u64>::new();
            map.insert(b"ab", 1u64);
            let mut wz = map.write_zipper();
            wz.descend_to(b"ab");
            println!("  focus child_count={} -- calling meet_k_path_into(1, false), which hangs",
                     wz.child_count());
            let r = wz.meet_k_path_into(1, false);
            println!("  returned {r} (unreachable)");
        }

        other => println!("  unknown case {other:?}; try --list"),
    }
}
