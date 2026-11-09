//! Standalone reproducers for the `ProductZipper` / `ProductZipperG` findings
//! in `lean/findings/product.md`.  Each prints what the crate does and what the
//! model (`lean/PathMapModel/Sources/Product.lean`) says it should do.
//!
//! `cargo run --release -p differential --bin product_repros`

use pathmap::zipper::*;
use pathmap::PathMap;

fn m(ps: &[&[u8]]) -> PathMap<u64> {
    let mut m = PathMap::new();
    for p in ps {
        m.set_val_at(p, 1);
    }
    m
}

fn mask<Z: Zipper>(z: &Z) -> Vec<u8> {
    z.child_mask().iter().collect()
}

fn report(name: &str, ok: bool, got: String, want: &str) {
    println!("{} {name}\n    crate: {got}\n    model: {want}", if ok { "ok  " } else { "BUG " });
}

fn main() {
    let empty = PathMap::<u64>::new();
    let x = m(&[b"x"]);
    let a = m(&[b"a"]);
    let c = m(&[b"c"]);
    let bc = m(&[b"bc"]);

    // P1: a childless primary root is a joint, but neither type enters the
    // next factor on construction; ProductZipper enters it as a side effect of
    // a failed descend_first_byte, and reset forgets it again.
    {
        let mut z = ProductZipper::new(empty.read_zipper(), [x.read_zipper()]);
        let before = mask(&z);
        let d = z.descend_first_byte();
        let after = mask(&z);
        z.reset();
        let reset = mask(&z);
        report("P1 ProductZipper: childless primary root",
            before == [b'x'] && after == [b'x'] && reset == [b'x'],
            format!("root mask {before:?}; descend_first_byte() = {d:?}, then mask {after:?}; after reset {reset:?}"),
            "root mask [120] throughout; descend_first_byte() = Some(120)");
    }
    {
        let mut z = ProductZipperG::new(empty.read_zipper(), [x.read_zipper()]);
        let before = mask(&z);
        z.descend_to(b"x");
        let exists = z.path_exists();
        report("P1 ProductZipperG: childless primary root",
            before == [b'x'],
            format!("root mask {before:?}, yet descend_to(x) gives path_exists = {exists}"),
            "root mask [120]; descend_to(x) exists");
    }

    // P2: a factor with no children at its root is transparent in the model;
    // ProductZipper never enters the factor after it, ProductZipperG only on a
    // later call at the same place.
    {
        let mut z = ProductZipper::new(a.read_zipper(), [empty.read_zipper(), c.read_zipper()]);
        z.descend_to(b"a");
        let mk = mask(&z);
        z.descend_to(b"c");
        let e = z.path_exists();
        report("P2 ProductZipper: empty middle factor", mk == [b'c'] && e,
            format!("at a: mask {mk:?}; descend_to(c) exists = {e}"),
            "at a: mask [99]; descend_to(c) exists");
    }
    {
        let mut z = ProductZipperG::new(a.read_zipper(), [empty.read_zipper(), c.read_zipper()]);
        z.descend_to(b"a");
        let mk = mask(&z);
        z.descend_to(b"c");
        let e = z.path_exists();
        report("P2 ProductZipperG: empty middle factor", mk == [b'c'],
            format!("at a: mask {mk:?}, yet descend_to(c) exists = {e}"),
            "at a: mask [99]; descend_to(c) exists");
    }

    // P3: val_at does not follow a path across a joint.
    {
        let mut z = ProductZipperG::new(a.read_zipper(), [bc.read_zipper()]);
        let va = z.val_at(b"abc").copied();
        z.descend_to(b"abc");
        let v = z.val().copied();
        report("P3 ProductZipperG: val_at across a joint", va == v,
            format!("val_at(abc) = {va:?}, descend_to(abc); val() = {v:?}"), "both Some(1)");
        let mut z = ProductZipper::new(a.read_zipper(), [bc.read_zipper()]);
        let va = z.val_at(b"abc").copied();
        z.descend_to(b"abc");
        let v = z.val().copied();
        report("P3 ProductZipper: val_at across a joint", va == v,
            format!("val_at(abc) = {va:?}, descend_to(abc); val() = {v:?}"), "both Some(1)");
    }

    // P4: ProductZipper::val_at panics with the focus at a joint or inside the
    // first node of a secondary factor.
    {
        let b2 = m(&[b"bcd", b"bce"]);
        for path in [&b"a"[..], b"ab"] {
            let mut z = ProductZipper::new(a.read_zipper(), [b2.read_zipper()]);
            z.descend_to(path);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| z.val_at(b"").copied()));
            let want = z.val().copied();
            report(&format!("P4 ProductZipper: val_at([]) at {:?}", std::str::from_utf8(path).unwrap()),
                matches!(r, Ok(v) if v == want),
                match r { Ok(v) => format!("{v:?}"), Err(_) => "panic (focus_parent unwrap)".to_string() },
                &format!("{want:?} (= val())"));
        }
    }

    // P5: ProductZipper::descend_to_check(&[]) at a missing focus.
    {
        let mut z = ProductZipper::new(a.read_zipper(), [bc.read_zipper()]);
        z.descend_to(b"q");
        let r = z.descend_to_check(b"");
        report("P5 ProductZipper: descend_to_check([]) at a missing focus", !r,
            format!("{r} (path_exists = {})", z.path_exists()), "false, as the native read zipper");
    }

    // P6: path_indices() at a joint has one more entry than focus_factor().
    {
        let mut z = ProductZipper::new(a.read_zipper(), [bc.read_zipper()]);
        z.descend_to(b"a");
        let (ff, pi) = (z.focus_factor(), z.path_indices().to_vec());
        report("P6 ProductZipper: path_indices at a joint", pi.len() == ff,
            format!("focus_factor = {ff}, path_indices = {pi:?}"), "path_indices().len() == focus_factor() (trait doc)");
        let mut z = ProductZipperG::new(a.read_zipper(), [bc.read_zipper()]);
        z.descend_to(b"a");
        let (ff, pi) = (z.focus_factor(), z.path_indices().to_vec());
        report("P6 ProductZipperG: path_indices at a joint", pi.len() == ff,
            format!("focus_factor = {ff}, path_indices = {pi:?}"), "path_indices().len() == focus_factor() (trait doc)");
    }
}
