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

fn repeat_iter_mask(mask: ByteMask, repeats: usize) -> u64 {
    let mut acc = 0u64;
    for repeat in 0..repeats {
        acc = acc.wrapping_add(iter_mask(mask).wrapping_add(black_box(repeat as u64)));
    }
    black_box(acc)
}

#[divan::bench(args = [0, 1, 2])]
fn bytemask_iter_small(bencher: Bencher, on_bits: usize) {
    let mask = spread_mask(on_bits);
    let mut sink = 0u64;

    bencher.bench_local(|| {
        sink = sink.wrapping_add(repeat_iter_mask(mask, 1024));
        black_box(sink);
    });
}

#[divan::bench(args = [4, 8, 16])]
fn bytemask_iter_medium(bencher: Bencher, on_bits: usize) {
    let mask = spread_mask(on_bits);
    let mut sink = 0u64;

    bencher.bench_local(|| {
        sink = sink.wrapping_add(repeat_iter_mask(mask, 256));
        black_box(sink);
    });
}

#[divan::bench(args = [150, 200, 256])]
fn bytemask_iter_large(bencher: Bencher, on_bits: usize) {
    let mask = spread_mask(on_bits);
    let mut sink = 0u64;

    bencher.bench_local(|| {
        sink = sink.wrapping_add(iter_mask(mask));
        black_box(sink);
    });
}
