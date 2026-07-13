use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    Divan::from_args().sample_count(100).main();
}

fn zipper_head_fixture() -> PathMap<usize> {
    let mut map = PathMap::new();
    for group in 0..16u8 {
        for leaf in 0..16u8 {
            map.set_val_at([group, leaf], ((group as usize) << 8) | leaf as usize);
        }
    }
    map
}

fn bench_read_creation<F>(bencher: Bencher, repeats: usize, mut read_child_count: F)
where
    F: FnMut() -> usize,
{
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for _ in 0..repeats {
            observed += read_child_count();
        }
        black_box(observed);
    });
}

fn bench_write_creation_cleanup<F>(bencher: Bencher, repeats: usize, mut create_and_cleanup: F)
where
    F: FnMut([u8; 2]) -> usize,
{
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for i in 0..repeats {
            observed += create_and_cleanup([240u8, i as u8]);
        }
        black_box(observed);
    });
}

fn bench_head_read_creation<'trie, H>(bencher: Bencher, repeats: usize, head: &H)
where
    H: ZipperCreation<'trie, usize>,
{
    let path = [7u8];

    bench_read_creation(bencher, repeats, || {
        let reader = head.read_zipper_at_borrowed_path(black_box(&path)).unwrap();
        reader.child_count()
    });
}

fn bench_head_write_creation_cleanup<'trie, H>(bencher: Bencher, repeats: usize, head: &H)
where
    H: ZipperCreation<'trie, usize>,
{
    bench_write_creation_cleanup(bencher, repeats, |path| {
        let writer = head
            .write_zipper_at_exclusive_path(black_box(path))
            .unwrap();
        let observed = writer.path_exists() as usize;
        head.cleanup_write_zipper(writer);
        observed
    });
}

#[divan::bench(args = [1usize, 10, 100])]
fn borrowed_head_read_creation(bencher: Bencher, repeats: usize) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    bench_head_read_creation(bencher, repeats, &head);
}

#[divan::bench(args = [1usize, 10, 100])]
fn owned_head_read_creation(bencher: Bencher, repeats: usize) {
    let map = zipper_head_fixture();
    let head = black_box(map).into_zipper_head([]);
    bench_head_read_creation(bencher, repeats, &head);
}

#[divan::bench(args = [1usize, 10, 100])]
fn borrowed_head_write_creation_cleanup(bencher: Bencher, repeats: usize) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    bench_head_write_creation_cleanup(bencher, repeats, &head);
}

#[divan::bench(args = [1usize, 10, 100])]
fn owned_head_write_creation_cleanup(bencher: Bencher, repeats: usize) {
    let map = zipper_head_fixture();
    let head = black_box(map).into_zipper_head([]);
    bench_head_write_creation_cleanup(bencher, repeats, &head);
}
