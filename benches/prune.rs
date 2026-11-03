use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    Divan::from_args().main();
}

#[divan::bench]
fn prune_path(bencher: Bencher) {
    bencher.with_inputs(|| {
        let mut map = PathMap::<u64>::new();
        map.create_path(b"abcd");
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper_at_path(b"ab");
        wz.descend_to(b"cd");
        black_box(wz.prune_path());
    });
}

#[divan::bench(args = [false, true])]
fn remove_val(bencher: Bencher, prune: bool) {
    bencher.with_inputs(|| {
        let mut map = PathMap::<u64>::new();
        map.set_val_at(b"abcd", 1);
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper_at_path(b"ab");
        wz.descend_to(b"cd");
        black_box(wz.remove_val(prune));
    });
}

#[divan::bench(args = [false, true])]
fn remove_branches(bencher: Bencher, prune: bool) {
    bencher.with_inputs(|| {
        let mut map = PathMap::<u64>::new();
        map.set_val_at(b"abcd", 1);
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper_at_path(b"ab");
        wz.descend_to(b"c");
        black_box(wz.remove_branches(prune));
    });
}

#[divan::bench(args = [false, true])]
fn take_map(bencher: Bencher, prune: bool) {
    bencher.with_inputs(|| {
        let mut map = PathMap::<u64>::new();
        map.set_val_at(b"a", 1);
        map.set_val_at(b"ab", 2);
        map.set_val_at(b"ac", 3);
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper();
        wz.descend_to(b"a");
        black_box(wz.take_map(prune));
    });
}
