use divan::{black_box, Bencher, Divan};

use pathmap::utils::ByteMask;

fn main() {
    let divan = Divan::from_args().sample_count(4000);

    divan.main();
}

fn spread_mask(on_bits: usize) -> ByteMask {
    debug_assert!(on_bits <= 256);

    (0..on_bits)
        .map(|idx| ((idx * 73 + 19) & 0xFF) as u8)
        .collect()
}

fn iter_mask(mask: ByteMask) -> u64 {
    let mut acc = 0u64;
    let mut count = 0u64;
    for byte in black_box(mask).iter() {
        let byte = black_box(byte) as u64;
        acc = acc.wrapping_mul(257).wrapping_add(byte + count);
        count += 1;
    }
    black_box(acc ^ count)
}

#[divan::bench(args = [0, 1, 2, 4, 8, 16, 150, 200, 256])]
fn bytemask_iter(bencher: Bencher, on_bits: usize) {
    let mask = spread_mask(on_bits);
    let mut sink = 0u64;

    bencher.bench_local(|| {
        sink = sink.wrapping_add(iter_mask(mask));
        black_box(sink);
    });
}

fn recursive_masks(depth: usize, on_bits: usize) -> Vec<ByteMask> {
    debug_assert!(on_bits <= 2);

    (0..depth)
        .map(|level| {
            (0..on_bits)
                .map(|idx| ((level * 37 + idx * 131 + 11) & 0xFF) as u8)
                .collect()
        })
        .collect()
}

fn recursive_iter(masks: &[ByteMask], level: usize, acc: u64) -> u64 {
    if level == masks.len() {
        return black_box(acc);
    }

    let mut out = acc;
    let mut iter = black_box(masks[level]).iter();
    if let Some(byte) = iter.next() {
        out = out.wrapping_add(recursive_iter(masks, level + 1, acc.wrapping_mul(257).wrapping_add(black_box(byte) as u64)));
    }
    if let Some(byte) = iter.next() {
        out = out.wrapping_add(black_box(byte) as u64);
    }
    black_box(&mut iter);
    black_box(out)
}

#[divan::bench(args = [1, 2])]
fn bytemask_iter_recursive_stack(bencher: Bencher, on_bits: usize) {
    const DEPTH: usize = 50;

    let masks = recursive_masks(DEPTH, on_bits);
    let mut sink = 0u64;

    bencher.bench_local(|| {
        sink = sink.wrapping_add(recursive_iter(&masks, 0, 0));
        black_box(sink);
    });
}
