#![cfg_attr(feature = "nightly", feature(core_intrinsics))]
#![cfg_attr(feature = "nightly", feature(portable_simd))]
#![cfg_attr(all(feature = "nightly", target_feature = "avx512f"), feature(stdarch_x86_avx512))]

use divan::{Bencher, Divan};
use pathmap::utils::find_prefix_overlap;
use rand::prelude::StdRng;
use rand_distr::{Exp, Triangular};
use pathmap::fuzzer::*;
use rand::SeedableRng;
use rand_distr::Distribution;
use std::marker::PhantomData;
use std::process::Termination;


const PAGE_SIZE: usize = 4096;
const TO_TEST: usize = 1000000;

#[cfg(not(feature = "nightly"))]
#[allow(unused)]
use core::convert::{identity as likely, identity as unlikely};
#[cfg(feature = "nightly")]
#[allow(unused)]
use core::intrinsics::{likely, unlikely};

#[inline(always)]
unsafe fn same_page<const VECTOR_SIZE: usize>(slice: &[u8]) -> bool {
    let address = slice.as_ptr() as usize;
    // Mask to keep only the last 12 bits
    let offset_within_page = address & (PAGE_SIZE - 1);
    // Check if the 16/32/64th byte from the current offset exceeds the page boundary
    offset_within_page < PAGE_SIZE - VECTOR_SIZE
}

#[cold]
fn count_shared_cold(a: &[u8], b: &[u8]) -> usize {
    count_shared_reference(a, b)
}

fn setup() -> Vec<(*const [u8], *const [u8])> {
    let max_len_sqrt = 20;
    let rng = StdRng::from_seed([0; 32]);
    let rng_ = StdRng::from_seed([!0; 32]);
    let path_fuzzer = Repeated {
        lengthd: Mapped{ d: Triangular::new(0f32, max_len_sqrt as f32,  8f32).unwrap(), f: |x| (x*x) as usize, pd: PhantomData::default() },
        itemd: Categorical { elements: { let mut v = vec![]; for i in 0..256 { v.push(i as u8) }; v },
            ed: Mapped { d: Exp::new(0.9f32).unwrap(), f: |x| (x as usize).min(255), pd: PhantomData::default() } }, pd: Default::default() };

    // let pairs = path_fuzzer.clone().sample_iter(rng).zip(path_fuzzer.clone().sample_iter(rng_)).take(TO_TEST).map(|(x, y)| (x.leak() as *const [u8], y.leak() as *const [u8])).collect::<Vec<_>>();
    let mut vec = Vec::with_capacity(TO_TEST*(max_len_sqrt*max_len_sqrt + 1));
    let pairs = path_fuzzer.clone().sample_iter(rng).zip(path_fuzzer.clone().sample_iter(rng_)).take(TO_TEST).map(|(x, y)| {
        let vl0 = vec.len();
        vec.extend_from_slice(&x[..]);
        let vl1 = vec.len();
        vec.extend_from_slice(&x[..]);
        let vl2 = vec.len();
        (&vec[vl0..vl1] as *const [u8], &vec[vl1..vl2] as *const [u8])
    }).collect::<Vec<_>>();
    std::hint::black_box(vec.leak());
    pairs
}

// ****************************************************************************************************
// Benchmark the `find_prefix_overlap` function exported publicly by the pathmap crate for the current config
// Should exactly match one of the other benchmarks that is running here
// ****************************************************************************************************

#[divan::bench()]
fn common_prefix_default(bencher: Bencher) {
    let pairs = setup();

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = find_prefix_overlap(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(find_prefix_overlap(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// reference scalar implementation
// Works everywhere.  Is the fastest nowhere.
// ****************************************************************************************************

fn count_shared_reference(p: &[u8], q: &[u8]) -> usize {
    p.iter().zip(q)
        .take_while(|(x, y)| x == y).count()
}

#[divan::bench()]
fn common_prefix_reference(bencher: Bencher) {
    let pairs = setup(); 

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = count_shared_reference(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(count_shared_reference(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// SSE2 implementation
// The fastest path on vanilla x86 using the stable tool chain
// ****************************************************************************************************

#[cfg(target_feature="sse2")]
fn count_shared_sse2(p: &[u8], q: &[u8]) -> usize {
    use std::arch::x86_64::*;
    unsafe {
        let pl = p.len();
        let ql = q.len();
        let max_shared = pl.min(ql);
        if max_shared == 0 { return 0 }
        if same_page::<16>(p) && same_page::<16>(q) {
            let pv = _mm_loadu_si128(p.as_ptr() as _);
            let qv = _mm_loadu_si128(q.as_ptr() as _);
            let ev = _mm_cmpeq_epi8(pv, qv);
            let ne = (!_mm_movemask_epi8(ev)) as u16;
            if ne == 0 && max_shared > 16 {
                let new_len = max_shared-16;
                16 + count_shared_sse2(core::slice::from_raw_parts(p.as_ptr().add(16), new_len), core::slice::from_raw_parts(q.as_ptr().add(16), new_len))
            } else {
                (_tzcnt_u16(ne) as usize).min(max_shared)
            }
        } else {
            count_shared_cold(p, q)
        }
    }
}

#[cfg(target_feature = "sse2")]
#[divan::bench()]
fn common_prefix_sse2(bencher: Bencher) {
    let pairs = setup();

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = count_shared_sse2(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(count_shared_sse2(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// AVX2 implementation
// The fastest path on most x86 machines using the stable tool chain
// ****************************************************************************************************

#[cfg(target_feature="avx2")]
#[inline(always)]
fn count_shared_avx2(p: &[u8], q: &[u8]) -> usize {
    use core::arch::x86_64::*;
    unsafe {
        let pl = p.len();
        let ql = q.len();
        let max_shared = pl.min(ql);
        if unlikely(max_shared == 0) { return 0 }
        if likely(same_page::<32>(p) && same_page::<32>(q)) {
            let pv = _mm256_loadu_si256(p.as_ptr() as _);
            let qv = _mm256_loadu_si256(q.as_ptr() as _);
            let ev = _mm256_cmpeq_epi8(pv, qv);
            let ne = !(_mm256_movemask_epi8(ev) as u32);
            let count = _tzcnt_u32(ne);
            if count != 32 || max_shared < 33 {
                (count as usize).min(max_shared)
            } else {
                let new_len = max_shared-32;
                32 + count_shared_avx2(core::slice::from_raw_parts(p.as_ptr().add(32), new_len), core::slice::from_raw_parts(q.as_ptr().add(32), new_len))
            }
        } else {
            count_shared_cold(p, q)
        }
    }
}

#[cfg(target_feature = "avx2")]
#[divan::bench()]
fn common_prefix_avx2(bencher: Bencher) {
    let pairs = setup();

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = count_shared_avx2(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(count_shared_avx2(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// AVX512 implementation
// The fastest path, period, if the hardware supports it
// ****************************************************************************************************

// Only takes 59% the time to run compared to count_shared_avx2
#[cfg(target_feature = "avx512f")]
fn count_shared_avx512<'a, 'b>(p: &'a [u8], q: &'b [u8]) -> usize {
    use core::arch::x86_64::*;
    unsafe {
        let pl = p.len();
        let ql = q.len();
        let max_shared = pl.min(ql);
        if unlikely(max_shared == 0) { return 0 }
        if unlikely(same_page::<64>(p) && same_page::<64>(q)) {
            let pv = _mm512_loadu_si512(p.as_ptr() as _);
            let qv = _mm512_loadu_si512(q.as_ptr() as _);
            let ne = !_mm512_cmpeq_epi8_mask(pv, qv);
            let count = _tzcnt_u64(ne);
            if count != 64 || max_shared < 65 {
                (count as usize).min(max_shared)
            } else {
                let new_len = max_shared-64;
                64 + count_shared_avx512(core::slice::from_raw_parts(p.as_ptr().add(64), new_len), core::slice::from_raw_parts(q.as_ptr().add(64), new_len))
            }
        } else {
            count_shared_cold(p, q)
        }
    }
}

#[cfg(target_feature = "avx512f")]
#[divan::bench()]
fn common_prefix_avx512(bencher: Bencher) {
    let pairs = setup();

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = count_shared_avx512(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(count_shared_avx512(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// `portable_simd`, depends on nightly tool chain
// Currently the winner on ARM, tied on AVX2, but loses to AVX512
// ****************************************************************************************************
//
// On neon it's ~15% faster than the native neon version!?
// Adam: On x86 it matches AVX2, but falls behind ~40% on AVX512 with the full datapath
#[cfg(feature = "nightly")]
#[inline(always)]
fn count_shared_simd(p: &[u8], q: &[u8]) -> usize {
    use std::simd::{u8x32, cmp::SimdPartialEq};
    unsafe {
        let pl = p.len();
        let ql = q.len();
        let max_shared = pl.min(ql);
        if unlikely(max_shared == 0) { return 0 }

        if same_page::<32>(p) && same_page::<32>(q) {
            let mut p_array = [core::mem::MaybeUninit::<u8>::uninit(); 32];
            core::ptr::copy_nonoverlapping(p.as_ptr().cast(), (&mut p_array).as_mut_ptr(), 32);
            let pv = u8x32::from_array(core::mem::transmute(p_array));
            let mut q_array = [core::mem::MaybeUninit::<u8>::uninit(); 32];
            core::ptr::copy_nonoverlapping(q.as_ptr().cast(), (&mut q_array).as_mut_ptr(), 32);
            let qv = u8x32::from_array(core::mem::transmute(q_array));
            let ev = pv.simd_eq(qv);

            let mask = ev.to_bitmask();
            let count = mask.trailing_ones();

            if count != 32 || max_shared < 33 {
                (count as usize).min(max_shared)
            } else {
                let new_len = max_shared-32;
                32 + count_shared_simd(core::slice::from_raw_parts(p.as_ptr().add(32), new_len), core::slice::from_raw_parts(q.as_ptr().add(32), new_len))
            }

        } else {
            return count_shared_cold(p, q);
        }
    }
}

#[cfg(feature = "nightly")]
#[divan::bench()]
fn common_prefix_simd(bencher: Bencher) {
    let pairs = setup();

    pairs.iter().for_each(|(l, r)| {
        let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
        let cnt = count_shared_simd(l, r);
        assert_eq!(&l[..cnt], &r[..cnt]);
        assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
    });

    bencher.bench_local(|| {
        pairs.iter().for_each(|(l, r)| {
            let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
            std::hint::black_box(count_shared_simd(&l[..], &r[..]));
        });
    });
}

// ****************************************************************************************************
// `wide` crate, by lokathor
// removed from build because it was the winner in none of the benchmarks on none of the architectures
// ****************************************************************************************************
//
// // LP: uses Lokathor's `wide` crate.  Perf on neon is *identical* to the native neon version above
// // We could make this the default code path depending on perf on x86, which I have yet to measure.
// // Adam: Performance on x86 is poor, but the std::simd version is on par with AVX2
// #[inline(always)]
// fn count_shared_wide(p: &[u8], q: &[u8]) -> usize {
//     use wide::u8x16;
//     unsafe {
//         let pl = p.len();
//         let ql = q.len();
//         let max_shared = pl.min(ql);
//         if unlikely(max_shared == 0) { return 0 }

//         if same_page::<16>(p) && same_page::<16>(q) {
//             let mut p_array = [core::mem::MaybeUninit::<u8>::uninit(); 16];
//             core::ptr::copy_nonoverlapping(p.as_ptr().cast(), (&mut p_array).as_mut_ptr(), 16);
//             let pv = u8x16::from(core::mem::transmute::<_, [u8; 16]>(p_array));
//             let mut q_array = [core::mem::MaybeUninit::<u8>::uninit(); 16];
//             core::ptr::copy_nonoverlapping(q.as_ptr().cast(), (&mut q_array).as_mut_ptr(), 16);
//             let qv = u8x16::from(core::mem::transmute::<_, [u8; 16]>(q_array));
//             let ev = pv.cmp_eq(qv);

//             let eq_arr = ev.to_array();
//             let eq_u128: u128 = core::mem::transmute(eq_arr);

//             let count = eq_u128.trailing_ones() / 8;

//             if count != 16 || max_shared < 17 {
//                 (count as usize).min(max_shared)
//             } else {
//                 let new_len = max_shared-16;
//                 16 + count_shared_wide(core::slice::from_raw_parts(p.as_ptr().add(16), new_len), core::slice::from_raw_parts(q.as_ptr().add(16), new_len))
//             }

//         } else {
//             return count_shared_cold(p, q);
//         }
//     }
// }

// #[divan::bench()]
// fn common_prefix_wide(bencher: Bencher) {
//     let pairs = setup();

//     pairs.iter().for_each(|(l, r)| {
//         let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
//         let cnt = count_shared_wide(l, r);
//         assert_eq!(&l[..cnt], &r[..cnt]);
//         assert!(l.len() <= cnt || r.len() <= cnt || l[cnt] != r[cnt], "{l:?} {r:?} {:?}", cnt);
//     });

//     bencher.bench_local(|| {
//         pairs.iter().for_each(|(l, r)| {
//             let l = unsafe { l.as_ref().unwrap() }; let r = unsafe { r.as_ref().unwrap() };
//             std::hint::black_box(count_shared_wide(&l[..], &r[..]));
//         });
//     });
// }

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(100);

    divan.main();
}
