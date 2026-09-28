use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;

const REPEATS: usize = 100;

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

fn bench_head_read_creation<'trie, H>(bencher: Bencher, head: &H)
where
    H: ZipperCreation<'trie, usize>,
{
    let path = [7u8];
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for _ in 0..REPEATS {
            let reader = head.read_zipper_at_borrowed_path(black_box(&path)).unwrap();
            observed += reader.child_count();
        }
        black_box(observed);
    });
}

fn bench_head_write_creation_cleanup<'trie, H, const CHECKED: bool>(bencher: Bencher, head: &H)
where
    H: ZipperCreation<'trie, usize>,
{
    bencher.bench_local(|| {
        let mut writers = Vec::with_capacity(REPEATS);
        let mut observed = 0usize;
        for i in 0..REPEATS {
            let path = black_box([240u8, i as u8]);
            // The paths are disjoint. All writers stay live until cleanup below.
            let writer = if CHECKED {
                head.write_zipper_at_exclusive_path(path).unwrap()
            } else {
                unsafe { head.write_zipper_at_exclusive_path_unchecked(path) }
            };
            observed += writer.path_exists() as usize;
            writers.push(writer);
        }
        for writer in writers {
            head.cleanup_write_zipper(writer);
        }
        black_box(observed);
    });
}

#[divan::bench]
fn borrowed_head_read_creation(bencher: Bencher) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    bench_head_read_creation(bencher, &head);
}

#[divan::bench]
fn owned_head_read_creation(bencher: Bencher) {
    let map = zipper_head_fixture();
    let head = black_box(map).into_zipper_head([]);
    bench_head_read_creation(bencher, &head);
}

#[divan::bench]
fn borrowed_head_write_creation_cleanup(bencher: Bencher) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    bench_head_write_creation_cleanup::<_, true>(bencher, &head);
}

#[divan::bench]
fn owned_head_write_creation_cleanup(bencher: Bencher) {
    let map = zipper_head_fixture();
    let head = black_box(map).into_zipper_head([]);
    bench_head_write_creation_cleanup::<_, true>(bencher, &head);
}

#[divan::bench]
fn borrowed_head_write_creation_cleanup_unchecked(bencher: Bencher) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    bench_head_write_creation_cleanup::<_, false>(bencher, &head);
}

#[divan::bench]
fn owned_head_write_creation_cleanup_unchecked(bencher: Bencher) {
    let map = zipper_head_fixture();
    let head = black_box(map).into_zipper_head([]);
    bench_head_write_creation_cleanup::<_, false>(bencher, &head);
}
