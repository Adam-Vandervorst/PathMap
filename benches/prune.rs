use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    Divan::from_args().main();
}

fn fixture(path: &[u8]) -> PathMap<u64> {
    let mut map = PathMap::new();
    map.set_val_at(path, 1);
    map
}

fn run_remove_val(bencher: Bencher, path: &[u8], root_len: usize, prune: bool) {
    bencher.with_inputs(|| fixture(path)).bench_local_values(|mut map| {
        let mut wz = map.write_zipper_at_path(&path[..root_len]);
        wz.descend_to(&path[root_len..]);
        black_box(wz.remove_val(prune));
    });
}

fn run_remove_branches(bencher: Bencher, path: &[u8], root_len: usize, prune: bool) {
    bencher.with_inputs(|| fixture(path)).bench_local_values(|mut map| {
        let focus = &path[..path.len() - 1];
        let mut wz = map.write_zipper_at_path(&path[..root_len]);
        wz.descend_to(&focus[root_len..]);
        black_box(wz.remove_branches(prune));
    });
}

fn run_prune_path(bencher: Bencher, path: &[u8], root_len: usize) {
    bencher.with_inputs(|| {
        let mut map = PathMap::<u64>::new();
        map.create_path(path);
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper_at_path(&path[..root_len]);
        wz.descend_to(&path[root_len..]);
        black_box(wz.prune_path());
    });
}

#[divan::bench]
fn prune_path_short_root_at_map_root(bencher: Bencher) {
    run_prune_path(bencher, b"abcd", 0);
}

#[divan::bench]
fn prune_path_short_root_inside_node(bencher: Bencher) {
    run_prune_path(bencher, b"abcd", 2);
}

#[divan::bench]
fn prune_path_long_root_inside_node(bencher: Bencher) {
    let path: Vec<u8> = (0..100).collect();
    run_prune_path(bencher, &path, 95);
}

#[divan::bench(args = [false, true])]
fn remove_val_short(bencher: Bencher, prune: bool) {
    run_remove_val(bencher, b"abcd", 2, prune);
}

#[divan::bench(args = [false, true])]
fn remove_val_long_root_above_node(bencher: Bencher, prune: bool) {
    let path: Vec<u8> = (0..100).collect();
    run_remove_val(bencher, &path, 5, prune);
}

#[divan::bench(args = [false, true])]
fn remove_val_long_root_inside_node(bencher: Bencher, prune: bool) {
    let path: Vec<u8> = (0..100).collect();
    run_remove_val(bencher, &path, 95, prune);
}

#[divan::bench(args = [false, true])]
fn remove_branches_short(bencher: Bencher, prune: bool) {
    run_remove_branches(bencher, b"abcd", 2, prune);
}

#[divan::bench(args = [false, true])]
fn remove_branches_long_root_above_node(bencher: Bencher, prune: bool) {
    let path: Vec<u8> = (0..100).collect();
    run_remove_branches(bencher, &path, 5, prune);
}

#[divan::bench(args = [false, true])]
fn remove_branches_long_root_inside_node(bencher: Bencher, prune: bool) {
    let path: Vec<u8> = (0..100).collect();
    run_remove_branches(bencher, &path, 95, prune);
}
