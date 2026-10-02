//! Standalone reproducers for what `bin/alg_fuzz` found on `master`.
//!
//! Same role as `bin/zipper_bug_repros.rs`: each case is a dozen lines of
//! ordinary `pathmap` calls with no fuzzer, no harness and no decoder, so it
//! can be pasted into a test or stepped through in a debugger.  The signatures
//! these correspond to are listed in `algebraic::KNOWN`.
//!
//! ```sh
//! cargo run --release -p differential --bin alg_bug_repros
//! ```
//!
//! Exit status is 1 while any of them still reproduces.  Case 7 is an unsettled
//! question rather than a defect and never counts as a failure.

use pathmap::PathMap;
use pathmap::experimental::zipper_algebra::{zipper_join, zipper_meet, zipper_sym_diff};
use pathmap::zipper::{ZipperMoving, ZipperPath, ZipperValues, ZipperWriting};

/// A trie holding only dangling paths: structure written with `create_path`
/// and no value anywhere.
fn dangling(paths: &[&[u8]]) -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    let mut wz = m.write_zipper();
    for p in paths {
        wz.reset();
        wz.descend_to(*p);
        wz.create_path();
    }
    drop(wz);
    m
}

fn with_val(path: &[u8], v: u64) -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    m.write_zipper_at_path(path).set_val(v);
    m
}

fn val_at(m: &PathMap<u64>, path: &[u8]) -> Option<u64> {
    m.read_zipper_at_path(path).val().copied()
}

/// Every path in a trie, with `=v` on the ones carrying a value, so a
/// dangling-path difference is visible.
fn shape(m: &PathMap<u64>) -> Vec<String> {
    let mut z = m.read_zipper();
    let mut out = Vec::new();
    z.reset();
    while z.to_next_step() {
        out.push(format!(
            "{}{}",
            z.path().iter().map(|b| format!("{b}")).collect::<String>(),
            if z.val().is_some() { "=v" } else { "" }
        ));
    }
    out
}

struct Report {
    failed: usize,
}

impl Report {
    fn case(&mut self, n: &str, what: &str, want: String, got: String) {
        let ok = want == got;
        if !ok {
            self.failed += 1;
        }
        println!("\n{n}. {what}");
        println!("   expected: {want}");
        println!("   got:      {got}");
        println!("   => {}", if ok { "fixed" } else { "REPRODUCES" });
    }
}

fn main() {
    let mut r = Report { failed: 0 };

    // ---------------------------------------------------------------- 1
    // `join_into` is the write-zipper spelling of `join`, so joining a source
    // into an empty destination has to be the same as joining the empty map
    // with it.  The root value does not survive the write-zipper form.
    {
        let src = with_val(&[], 1);
        let eager = PathMap::<u64>::new().join(&src);

        let mut out = PathMap::<u64>::new();
        {
            let mut wz = out.write_zipper();
            wz.join_into(&src.read_zipper());
        }
        r.case(
            "1",
            "join_into on an empty destination: empty | {_:1}",
            format!("root value {:?} (PathMap::join)", val_at(&eager, &[])),
            format!("root value {:?} (join_into)", val_at(&out, &[])),
        );
    }

    // ---------------------------------------------------------------- 2
    // `meet_2` writes the intersection of two sources into a fresh
    // destination.  Two maps whose only content is a root value intersect to
    // that root value; `meet_2` produces nothing at all.
    {
        let a = with_val(&[], 1);
        let b = with_val(&[], 2);
        let eager = b.meet(&a);

        let mut out = PathMap::<u64>::new();
        {
            let mut wz = out.write_zipper();
            wz.meet_2(&b.read_zipper(), &a.read_zipper());
        }
        r.case(
            "2",
            "meet_2 with root values only: {_:2} & {_:1}",
            format!("root value {:?} (PathMap::meet)", val_at(&eager, &[])),
            format!("root value {:?} (meet_2)", val_at(&out, &[])),
        );
    }

    // ---------------------------------------------------------------- 3
    // `pjoin` on `u64` is `left_biased_pjoin` and `pmeet` is
    // `Identity(SELF_IDENT)`, so where both operands have a value at a path the
    // result must carry the *left* one.  It carries the right one when the two
    // operands' nodes are laid out differently -- here because `a` has a chain
    // of dangling descendants below the shared path and `c` does not.
    //
    // Every zipper route gets this right; `PathMap::join` and `PathMap::meet`
    // do not, which is why it surfaces as failing laws rather than as one
    // route disagreeing with the rest.
    {
        let mut a = dangling(&[&[0, 0, 0, 0], &[1]]);
        a.write_zipper_at_path(&[0]).set_val(1);
        let c = with_val(&[0], 2);

        r.case(
            "3a",
            "join value bias: {00:2} | {00:1, dangling below} at [0]",
            "Some(2), the left operand's value".to_string(),
            format!("{:?}", val_at(&c.join(&a), &[0])),
        );
        r.case(
            "3b",
            "meet value bias: {00:1, dangling below} & {00:2} at [0]",
            "Some(1), the left operand's value".to_string(),
            format!("{:?}", val_at(&a.meet(&c), &[0])),
        );
    }

    // ---------------------------------------------------------------- 4
    // The worst of them: a join *loses a value*.  Not a bias about which of two
    // values wins -- only one operand has a value at all, and the result has
    // none.
    //
    // `b` is a clone of `a` with one value added, so the two tries share nodes.
    // Joining in the order `a | b` drops `b`'s value; `b | a` keeps it.  A
    // join is a least upper bound, so no ordering of the operands may lose a
    // path, which makes this the one finding here that is unambiguous without
    // any appeal to value bias.
    //
    // The sharing is essential: rebuilding `b`'s entries into a fresh map
    // instead of cloning `a` makes it go away.
    {
        let a = dangling(&[&[0, 0, 0, 0, 0], &[1, 0, 1], &[1, 0, 3]]);
        let mut b = a.clone();
        b.write_zipper_at_path(&[1, 0, 0, 0]).set_val(1);

        let ab = a.join(&b);
        let ba = b.join(&a);
        r.case(
            "4",
            "join drops a value across clone-shared structure, at [1,0,0,0]",
            format!("a|b == b|a == Some(1); b|a gives {:?}", val_at(&ba, &[1, 0, 0, 0])),
            format!("a|b gives {:?}", val_at(&ab, &[1, 0, 0, 0])),
        );
    }

    // ---------------------------------------------------------------- 5
    // Not an algebraic defect: `merkleize` panics outright on a trie that holds
    // structure but no values.  It is in this list because the fuzzer's operand
    // generator reaches it -- `merkleize` is how it builds operands with shared
    // subtries, which is what case 4 needs.
    {
        let mut m = dangling(&[&[0, 0], &[0, 1, 0, 0]]);
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| m.merkleize()));
        std::panic::set_hook(hook);
        r.case(
            "5",
            "merkleize over dangling-only structure",
            "no panic".to_string(),
            if res.is_ok() { "no panic".to_string() } else { "panic".to_string() },
        );
    }

    // ---------------------------------------------------------------- 6
    // Finding 6 has no standalone reproducer: it is three `debug_assert!`s
    // inside the merge primitives, so there is nothing to compare and nothing
    // to print -- the assertion either fires or it does not.  Build with
    // `-C debug-assertions=yes` and replay the three `panic-eval-*` inputs in
    // `algebraic-corpus/`.
    println!(
        "\n6. join reporting an empty result from non-empty nodes\n            => debug-assertions only; replay algebraic-corpus/panic-eval-*.bin"
    );

    // ---------------------------------------------------------------- 7
    // The `shape` class, which is the largest one the fuzzer reports and had no
    // reproducer until now.
    //
    // Not a defect: whether a dangling path -- structure written with
    // `create_path`, carrying no value and with nothing below it -- survives an
    // operation is unsettled in the crate.  What the fuzzer establishes is that
    // the two families answer differently and consistently so:
    //
    //   * the lockstep traversals in `experimental::zipper_algebra` **discard**
    //     dangling structure;
    //   * `PathMap`'s whole-map operations and the write-zipper forms
    //     (`join_into`, `meet_into`, `subtract_into`) **preserve** it.
    //
    // Worth having concretely, because whichever way the question is settled, one
    // of those two families has to change, and this says which operations are on
    // each side.
    {
        let d2 = dangling(&[&[0], &[1]]);
        let dv = {
            let mut m = dangling(&[&[0, 0]]);
            m.write_zipper_at_path(&[1]).set_val(7);
            m
        };

        println!("\n7. dangling paths: the zipper traversals drop them, the map operations keep them");
        println!("   operands: d2 = {{dangling 0, 1}}, dv = {{dangling 0, 00; value at 1}}");

        let mut zj = PathMap::<u64>::new();
        {
            let (mut a, mut b) = (d2.read_zipper(), dv.read_zipper());
            let mut wz = zj.write_zipper();
            zipper_join(&mut a, &mut b, &mut wz);
        }
        println!("   d2 | dv    zipper_join {:?}", shape(&zj));
        println!("              PathMap::join {:?}", shape(&d2.join(&dv)));

        let mut zm = PathMap::<u64>::new();
        {
            let (mut a, mut b) = (d2.read_zipper(), dv.read_zipper());
            let mut wz = zm.write_zipper();
            zipper_meet(&mut a, &mut b, &mut wz);
        }
        println!("   d2 & dv    zipper_meet {:?}", shape(&zm));
        println!("              PathMap::meet {:?}", shape(&d2.meet(&dv)));

        // The sharpest form: symmetric difference with the empty trie should be
        // the identity, and for structure it is not.
        let d = dangling(&[&[0]]);
        let empty = PathMap::<u64>::new();
        let mut zx = PathMap::<u64>::new();
        {
            let (mut a, mut b) = (d.read_zipper(), empty.read_zipper());
            let mut wz = zx.write_zipper();
            zipper_sym_diff(&mut a, &mut b, &mut wz);
        }
        println!("   d ^ {{}}     zipper_sym_diff {:?}", shape(&zx));
        println!(
            "              (d|e)-(d&e)    {:?}",
            shape(&d.join(&empty).subtract(&d.meet(&empty)))
        );
        println!("   => not counted as a failure; the crate has not settled this");
    }

    println!("\n{} of 6 still reproduce", r.failed);
    if r.failed > 0 {
        std::process::exit(1);
    }
}
