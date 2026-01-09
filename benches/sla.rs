use std::collections::HashSet;
use std::hash::Hasher;
use std::time::Instant;
use num_traits::Zero;
use rand::distr::Uniform;
use rand::prelude::StdRng;
use rand::{Rng, SeedableRng};
use rand_distr::Distribution;
use pathmap::*;
use pathmap::morphisms::Catamorphism;
use pathmap::ring::{AlgebraicResult, Lattice};
use pathmap::utils::{BitMask, ByteMask, ints::{indices_to_weave, weave_to_indices, indices_to_bob, bob_to_indices}};
use pathmap::viz::{DrawConfig, VizMode};
use pathmap::zipper::{ReadZipperUntracked, WriteZipperUntracked, Zipper, ZipperMoving, ZipperValues, ZipperWriting};

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct FAddMul(f32);
impl std::ops::Deref for FAddMul { type Target = f32; fn deref(&self) -> &Self::Target { &self.0 } }
impl std::hash::Hash for FAddMul { fn hash<H: Hasher>(&self, state: &mut H) { self.0.to_bits().hash(state); } }

// Note FAddMul is *not* a valid lattice under pjoin, but until we have bitraversal policies, this will have to do
impl Lattice for FAddMul {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        if self.0.is_zero() { return AlgebraicResult::Identity(1) }
        if other.0.is_zero() { return AlgebraicResult::Identity(2) }
        let s = self.0 + other.0;
        // make sparse if the dense sides had opposite signs and nearly cancelled out
        if self.0 * other.0 < 0f32 && s.abs() < 1e-9 { return AlgebraicResult::None }
        AlgebraicResult::Element(FAddMul(s))
    }

    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        let s = self.0*other.0;
        if s.abs() < 1e-9 { return AlgebraicResult::None }
        AlgebraicResult::Element(FAddMul(s))
    }
}

struct DenseTensorFRef {
    m: Vec<f32>,
    d: Vec<usize>
}

impl DenseTensorFRef {
    fn new(d: Vec<usize>) -> Self {
        let n: usize = d.iter().product();
        Self { m: vec![0.0; n], d }
    }

    fn linear_index(&self, ix: &[usize]) -> usize {
        assert_eq!(ix.len(), self.d.len(), "rank mismatch");

        let mut idx: usize = 0;
        let mut stride: usize = 1;

        for (&k, &dim) in ix.iter().rev().zip(self.d.iter().rev()) {
            assert!(k < dim, "index out of bounds");
            idx += k * stride;
            stride *= dim;
        }

        idx
    }
    pub fn get(&self, ix: &[usize]) -> f32 {
        let i = self.linear_index(ix);
        self.m[i]
    }

    pub fn set(&mut self, ix: &[usize], v: f32) {
        let i = self.linear_index(ix);
        self.m[i] = v;
    }

    fn add(&self, other: &Self) -> Self {
        assert_eq!(self.d, other.d, "shape mismatch");
        assert_eq!(self.m.len(), other.m.len(), "storage mismatch");

        let m = self
            .m
            .iter()
            .zip(other.m.iter())
            .map(|(&a, &b)| a + b)
            .collect();

        Self { m, d: self.d.clone() }
    }
}

struct SparseTensorFBOB {
    m: PathMap<f32>,
    d: usize,
    p: Vec<u8>
}

impl SparseTensorFBOB {
    fn set(&mut self, ix: &[usize], v: f32) {
        self.p.clear();
        let len = indices_to_bob(ix, &mut vec![]);
        self.p.extend(std::iter::repeat_n(0u8, 64 - len));
        indices_to_bob(ix, &mut self.p);
        self.m.insert(&self.p[..], v);
    }
    fn add(&self, other: &Self) -> Self { Self::vf32(self.vF().join(other.vF()), self.d) }
    fn mul(&self, other: &Self) -> Self { Self::vf32(self.vF().meet(other.vF()), self.d) }
    // Safety: F has the same layout as f32 (but exposes a different set of traits)
    fn vF(&self) -> &PathMap<FAddMul> { unsafe { (&self.m as *const PathMap<f32> as *const PathMap<FAddMul>).as_ref().unwrap_unchecked() } }
    fn vF_mut(&mut self) -> &mut PathMap<FAddMul> { unsafe { (&mut self.m as *mut PathMap<f32> as *mut PathMap<FAddMul>).as_mut().unwrap_unchecked() } }
    fn vf32(m: PathMap<FAddMul>, d: usize) -> Self { unsafe { Self{ m: std::mem::transmute::<PathMap::<FAddMul>, PathMap::<f32>>(m), d: d, p: Vec::new() } } }
    fn new(dimensions: usize) -> Self { Self { m: PathMap::new(), d: dimensions, p: Vec::new() } }
}


struct SparseTensorFWeave {
    m: PathMap<f32>,
    d: usize,
    p: Vec<u8>
}

impl SparseTensorFWeave {
    fn set(&mut self, ix: &[usize], v: f32) {
        self.p.clear();
        indices_to_weave::<8, usize>(ix, &mut self.p);
        self.m.insert(&self.p[..], v);
    }
    fn add(&self, other: &Self) -> Self { Self::vf32(self.vF().join(other.vF()), self.d) }
    fn mul(&self, other: &Self) -> Self { Self::vf32(self.vF().meet(other.vF()), self.d) }
    // Safety: F has the same layout as f32 (but exposes a different set of traits)
    fn vF(&self) -> &PathMap<FAddMul> { unsafe { (&self.m as *const PathMap<f32> as *const PathMap<FAddMul>).as_ref().unwrap_unchecked() } }
    fn vF_mut(&mut self) -> &mut PathMap<FAddMul> { unsafe { (&mut self.m as *mut PathMap<f32> as *mut PathMap<FAddMul>).as_mut().unwrap_unchecked() } }
    fn vf32(m: PathMap<FAddMul>, d: usize) -> Self { unsafe { Self{ m: std::mem::transmute::<PathMap::<FAddMul>, PathMap::<f32>>(m), d: d, p: Vec::new() } } }
    fn new(dimensions: usize) -> Self { Self { m: PathMap::new(), d: dimensions, p: Vec::new() } }
}

/// bhqd,bhkd->bhqk
static mut count: usize = 0;
fn bob_attention(Q: &mut ReadZipperUntracked<f32>, K: &mut ReadZipperUntracked<f32>, out: &mut WriteZipperUntracked<f32>, depth: usize) {
    let QF = 0b00001011u8; let QB = 0b00000111u8;
    let KF = 0b00001011u8; let KB = 0b00000100u8;
    let qm = Q.child_mask();
    let km = K.child_mask();

    for i in qm.iter() {
        let mut rkm: ByteMask = km; // k_must_on | k_must_off;
        let Q_proj_out: u8 = QB & i; // permute (now hardcoded)
        for j in rkm.iter() {
            let K_proj_out: u8 = (KB & j) << 1; // permute (now hardcoded)
            let out_b: u8 = Q_proj_out | K_proj_out;
            if QF & i != KF & j { continue }

            Q.descend_to_byte(i);
            K.descend_to_byte(j);
            out.descend_to_byte(out_b);
            if depth == 63 {
                let total = out.get_val_or_set_mut(0f32);
                *total += unsafe { *Q.val().unwrap_unchecked() * *K.val().unwrap_unchecked() };
                unsafe { count += 1; }
            } else {
                bob_attention(Q, K, out, depth + 1);
            }
            Q.ascend_byte();
            K.ascend_byte();
            out.ascend_byte();
        }
    }
}

/// bhqd,bhkd->bhqk
fn weave_attention(Q: &mut ReadZipperUntracked<f32>, K: &mut ReadZipperUntracked<f32>, out: &mut WriteZipperUntracked<f32>) {
    let bm = Q.child_mask().and(&K.child_mask());
    for b in bm.iter() {
        Q.descend_to_byte(b);
        K.descend_to_byte(b);
        out.descend_to_byte(b);
        let hm = Q.child_mask().and(&K.child_mask());
        for h in hm.iter() {
            Q.descend_to_byte(h);
            K.descend_to_byte(h);
            out.descend_to_byte(h);
            let qm = Q.child_mask();
            for q in qm.iter() {
                Q.descend_to_byte(q);
                out.descend_to_byte(q);
                let km = K.child_mask();
                for k in km.iter() {
                    K.descend_to_byte(k);
                    out.descend_to_byte(k);
                    let mut acc = 0f32;
                    let dm = Q.child_mask().and(&K.child_mask());
                    for d in dm.iter() {
                        Q.descend_to_byte(d);
                        K.descend_to_byte(d);
                        acc += unsafe { *Q.val().unwrap() * *K.val().unwrap() };
                        unsafe { count += 1 };
                        Q.ascend_byte();
                        K.ascend_byte();
                    }
                    out.set_val(acc);
                    K.ascend_byte();
                    out.ascend_byte();
                }
                Q.ascend_byte();
                out.ascend_byte();
            }
            Q.ascend_byte();
            K.ascend_byte();
            out.ascend_byte();
        }
        Q.ascend_byte();
        K.ascend_byte();
        out.ascend_byte();
    }
}

static mut rcount: usize = 0;
/// bhqd,bhkd->bhqk
fn reference_attention(Q: &DenseTensorFRef, K: &DenseTensorFRef, out: &mut DenseTensorFRef) {
    assert_eq!(Q.d[0], K.d[0]);
    for b in 0..Q.d[0] {
        assert_eq!(Q.d[1], K.d[1]);
        for h in 0..Q.d[1] {
            for q in 0..Q.d[2] {
                for k in 0..K.d[2] {
                    let mut acc = 0f32;
                    assert_eq!(Q.d[3], K.d[3]);
                    for d in 0..Q.d[3] {
                        let qv = Q.get(&[b, h, q, d]);
                        let kv = K.get(&[b, h, k, d]);
                        acc += qv*kv;
                        unsafe { rcount += 1; }
                    }
                    out.set(&[b, h, q, k], acc);
                }
            }
        }
    }
}

fn random_index<R : Rng>(size: &[usize], rng: &mut R, idx: &mut [usize]) {
    assert_eq!(size.len(), idx.len());
    for d in 0..size.len() {
        let g = Uniform::new(0, size[d]).unwrap();
        idx[d] = g.sample(rng);
    }
}

fn sparse_dimensionwise() {
    let mut t0 = SparseTensorFBOB::new(4);
    t0.set(&[3, 1, 6, 6], 0.5);
    t0.set(&[3, 2, 6, 6], 1.0);
    let mut t1 = SparseTensorFBOB::new(4);
    t1.set(&[3, 1, 6, 6], 0.2);
    t1.set(&[3, 1, 6, 7], 0.2);
    t1.set(&[5, 0, 0, 1], 10.0);
    t1.set(&[5, 0, 0, 2], 20.0);
    t1.set(&[5, 0, 0, 3], 30.0);
    let t1p2 = t0.add(&t1);
    let t1m2 = t0.mul(&t1);

    use pathmap::viz::{viz_maps, DrawConfig};
    let mut v = vec![];
    let dc = DrawConfig{ mode: VizMode::Ascii, ascii_path: false, hide_value_paths: false, minimize_values: false, logical: true, color: false };
    viz_maps(&&[t0, t1, t1p2, t1m2].into_iter().map(|t| t.vF().clone()).collect::<Vec<_>>()[..], &dc, &mut v).unwrap();
    println!("{}", str::from_utf8(&v[..]).unwrap());

}

fn tipover_attention_bob() {
    let mut rng = StdRng::from_seed([0; 32]);
    // let (batch_size, sequence_length, n_heads, embedding_dim) = (2, 3, 4, 8); // shakespeare-char
    // let (batch_size, sequence_length, n_heads, embedding_dim) = (8, 5, 12, 384); // shakespeare-char
    let (batch_size, sequence_length, n_heads, embedding_dim) = (8, 256, 25, 1600); // GPT-2 xl
    let mut rtq = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, embedding_dim/n_heads]);
    let mut rtk = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, embedding_dim/n_heads]);
    let mut rtr = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, n_heads]);
    let mut c = 0f32;
    for b in 0..batch_size {
        for h in 0..sequence_length {
            for k in 0..n_heads {
                for d in 0..embedding_dim/n_heads {
                    c += 1f32;
                    rtq.set(&[b, h, k, d], c);
                    rtk.set(&[b, h, k, d], -c);
                }
            }
        }
    }
    let n_weights = rtq.m.len();
    let t0 = Instant::now();
    reference_attention(&rtq, &rtk, &mut rtr);
    println!("ref {} µs ({n_weights} weights)", t0.elapsed().as_micros());
    println!("rcount {}", unsafe{ rcount });

    let mut rtr_ = SparseTensorFBOB::new(4);
    for b in 0..batch_size {
        for h in 0..sequence_length {
            for k in 0..n_heads {
                for q in 0..n_heads {
                    rtr_.set(&[b, h, k, q], rtr.get(&[b, h, k, q]));
                }
            }
        }
    }

    let mut rtq = SparseTensorFBOB::new(4);
    let mut rtk = SparseTensorFBOB::new(4);
    let mut rtr = SparseTensorFBOB::new(4);
    let mut c = 0f32;
    for b in 0..batch_size {
        for h in 0..sequence_length {
            for k in 0..n_heads {
                for d in 0..embedding_dim/n_heads {
                    c += 1f32;
                    rtq.set(&[b, h, k, d], c);
                    rtk.set(&[b, h, k, d], -c);
                }
            }
        }
    }
    let q_nz = rtq.m.val_count();
    let k_nz = rtk.m.val_count();
    // rtq.vF_mut().merkleize();
    // rtk.vF_mut().merkleize();
    let t0 = Instant::now();
    bob_attention(&mut rtq.m.read_zipper(), &mut rtk.m.read_zipper(), &mut rtr.m.write_zipper(), 0);
    println!("bob {} µs ({n_weights} weights, {q_nz} Q nz, {k_nz} K nz)", t0.elapsed().as_micros());
    println!(" count {}", unsafe{ count });
    unsafe{ count = 0 };

    assert_eq!(rtr.m.hash(|v| *v as u32 as u128), rtr_.m.hash(|v| *v as u32 as u128));

    // use pathmap::viz::{viz_maps, DrawConfig};
    // let mut v = vec![];
    // let dc = DrawConfig{ mode: VizMode::Ascii, ascii_path: false, hide_value_paths: false, minimize_values: false, logical: true, color: false };
    // viz_maps(&&[rtq, rtk, rtr, rtr_].into_iter().map(|t| t.vF().clone()).collect::<Vec<_>>()[..], &dc, &mut v).unwrap();
    // println!("{}", str::from_utf8(&v[..]).unwrap());

    // return;

    let mut rtq = SparseTensorFBOB::new(4);
    let mut rtk = SparseTensorFBOB::new(4);
    let mut rtr = SparseTensorFBOB::new(4);
    let mut idx = vec![0; 4];
    // in completely unstructured sparsity, at 2% PathMap outperforms the naive dense implementation
    for i in 0..(n_weights as f64*0.02) as usize {
        random_index(&[batch_size, sequence_length, n_heads, embedding_dim/n_heads], &mut rng, &mut idx[..]);
        rtq.set(&idx[..], i as f32);
        rtk.set(&idx[..], -(i as f32));
    }
    let q_nz = rtq.m.val_count();
    let k_nz = rtk.m.val_count();
    // rtq.vF_mut().merkleize();
    // rtk.vF_mut().merkleize();
    let t0 = Instant::now();
    bob_attention(&mut rtq.m.read_zipper(), &mut rtk.m.read_zipper(), &mut rtr.m.write_zipper(), 0);
    println!("bob {} µs ({n_weights} weights, {q_nz} Q nz, {k_nz} K nz)", t0.elapsed().as_micros());
    println!("count {}", unsafe{ count });
}

fn tipover_attention_weave() {
    let mut rng = StdRng::from_seed([0; 32]);
    // let (batch_size, sequence_length, n_heads, embedding_dim) = (32, 512, 12, 384); // shakespeare-char
    let (batch_size, sequence_length, n_heads, embedding_dim) = (8, 1024, 25, 1600); // GPT-2 xl
    let mut rtq = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, embedding_dim/n_heads]);
    let mut rtk = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, embedding_dim/n_heads]);
    let mut rtr = DenseTensorFRef::new(vec![batch_size, sequence_length, n_heads, n_heads]);
    let n_weights = rtq.m.len();
    let t0 = Instant::now();
    reference_attention(&rtq, &rtk, &mut rtr);
    println!("ref {} µs ({n_weights} weights)", t0.elapsed().as_micros());
    println!("rcount {}", unsafe{ rcount });

    let mut rtk = SparseTensorFWeave::new(4);
    let mut rtq = SparseTensorFWeave::new(4);
    let mut rtr = SparseTensorFWeave::new(4);
    for b in 0..batch_size {
        for h in 0..sequence_length {
            for k in 0..n_heads {
                for d in 0..embedding_dim/n_heads {
                    rtq.set(&[b, h, k, d], 1.0f32);
                    rtk.set(&[b, h, k, d], 1.0f32);
                }
            }
        }
    }
    let q_nz = rtq.m.val_count();
    let k_nz = rtk.m.val_count();
    // let res = rtq.vF_mut().merkleize();
    // println!("{:?}", res.hash);
    let t0 = Instant::now();
    // println!("{:?} {:?}", rtq.vF().read_zipper().into_cata_cached(morphisms::alg::hash), t0.elapsed().as_micros());
    return;

    // rtk.vF_mut().merkleize();
    let t0 = Instant::now();
    weave_attention(&mut rtq.m.read_zipper(), &mut rtk.m.read_zipper(), &mut rtr.m.write_zipper());
    println!("weave {} µs ({n_weights} weights, {q_nz} Q nz, {k_nz} K nz)", t0.elapsed().as_micros());
    println!("count {}", unsafe{ count });
    unsafe{ count = 0 };

    let mut rtq = SparseTensorFWeave::new(4);
    let mut rtk = SparseTensorFWeave::new(4);
    let mut rtr = SparseTensorFWeave::new(4);
    let mut idx = vec![0; 4];
    for i in 0..100000 {
        random_index(&[batch_size, sequence_length, n_heads, embedding_dim/n_heads], &mut rng, &mut idx[..]);
        rtq.set(&idx[..], 1.0);
        rtk.set(&idx[..], 1.0);
    }
    let q_nz = rtq.m.val_count();
    let k_nz = rtk.m.val_count();
    // rtq.vF_mut().merkleize();
    // rtk.vF_mut().merkleize();
    let t0 = Instant::now();
    weave_attention(&mut rtq.m.read_zipper(), &mut rtk.m.read_zipper(), &mut rtr.m.write_zipper());
    println!("weave {} µs ({n_weights} weights, {q_nz} Q nz, {k_nz} K nz)", t0.elapsed().as_micros());
    println!("count {}", unsafe{ count });
}

fn main() {
    // show sharing between pointwise operations:
    // sparse_dimensionwise();

    tipover_attention_bob();
    // tipover_attention_weave();

}