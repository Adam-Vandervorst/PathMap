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

fn bench_head_read_at_path<'trie, H>(bencher: Bencher, head: &H, path: &[u8])
where
    H: ZipperCreation<'trie, usize>,
{
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for _ in 0..REPEATS {
            let reader = head.read_zipper_at_borrowed_path(black_box(path)).unwrap();
            observed += reader.val().copied().unwrap_or_default();
            observed += reader.child_count();
            drop(reader);
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
fn borrowed_head_read_value_in_shared_parent(bencher: Bencher) {
    let mut map = PathMap::<usize>::new();
    map.set_val_at([0x22u8], 22);
    map.set_val_at([0x22u8, 0x01], 1);
    let head = black_box(&mut map).zipper_head();
    let _writer = head.write_zipper_at_exclusive_path([0x11u8]).unwrap();
    bench_head_read_at_path(bencher, &head, &[0x22]);
}

#[divan::bench]
fn borrowed_head_read_missing_path(bencher: Bencher) {
    let mut map = zipper_head_fixture();
    let head = black_box(&mut map).zipper_head();
    let _writer = head.write_zipper_at_exclusive_path([0x11u8]).unwrap();
    bench_head_read_at_path(bencher, &head, &[0xee, 0x00]);
}

const READ_ACCESS_REPEATS: usize = 1000;

fn bench_shared_parent_reader_access<const OP: u8>(bencher: Bencher) {
    let mut map = PathMap::<usize>::new();
    map.set_val_at([0x22u8], 22);
    map.set_val_at([0x22u8, 0x01], 1);
    let head = black_box(&mut map).zipper_head();
    let _writer = head.write_zipper_at_exclusive_path([0x11u8]).unwrap();
    let reader = head.read_zipper_at_borrowed_path(&[0x22u8]).unwrap();
    assert_eq!(reader.val(), Some(&22));
    assert_eq!(reader.child_count(), 1);
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for _ in 0..READ_ACCESS_REPEATS {
            let reader = black_box(&reader);
            if OP == 0 {
                observed += reader.val().copied().unwrap_or_default();
            } else if OP == 1 {
                observed += reader.is_val() as usize;
            } else if OP == 2 {
                observed += reader.is_shared() as usize;
            } else {
                black_box(reader.get_focus());
            }
        }
        black_box(observed);
    });
}

#[divan::bench]
fn shared_parent_reader_val(bencher: Bencher) {
    bench_shared_parent_reader_access::<0>(bencher);
}

#[divan::bench]
fn shared_parent_reader_is_val(bencher: Bencher) {
    bench_shared_parent_reader_access::<1>(bencher);
}

#[divan::bench]
fn shared_parent_reader_is_shared(bencher: Bencher) {
    bench_shared_parent_reader_access::<2>(bencher);
}

#[divan::bench]
fn shared_parent_reader_get_focus(bencher: Bencher) {
    bench_shared_parent_reader_access::<3>(bencher);
}

fn bench_map_reader_access<const OP: u8>(bencher: Bencher) {
    let mut map = PathMap::<usize>::new();
    map.set_val_at([0x22u8], 22);
    map.set_val_at([0x22u8, 0x01], 1);
    let reader = map.read_zipper_at_path([0x22u8]);
    assert_eq!(reader.val(), Some(&22));
    assert_eq!(reader.child_count(), 1);
    bencher.bench_local(|| {
        let mut observed = 0usize;
        for _ in 0..READ_ACCESS_REPEATS {
            let reader = black_box(&reader);
            if OP == 0 {
                observed += reader.val().copied().unwrap_or_default();
            } else if OP == 1 {
                observed += reader.is_val() as usize;
            } else if OP == 2 {
                observed += reader.is_shared() as usize;
            } else {
                black_box(reader.get_focus());
            }
        }
        black_box(observed);
    });
}

#[divan::bench]
fn map_reader_val(bencher: Bencher) {
    bench_map_reader_access::<0>(bencher);
}

#[divan::bench]
fn map_reader_is_val(bencher: Bencher) {
    bench_map_reader_access::<1>(bencher);
}

#[divan::bench]
fn map_reader_is_shared(bencher: Bencher) {
    bench_map_reader_access::<2>(bencher);
}

#[divan::bench]
fn map_reader_get_focus(bencher: Bencher) {
    bench_map_reader_access::<3>(bencher);
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
