use std::collections::hash_map::Entry;
use crate::trie_map::BytesTrieMap;
use rand::Rng;
use rand_distr::{Pert, Distribution};
use std::marker::PhantomData;
use std::ptr::null;
use rand::distr::{Iter, Uniform};
use crate::TrieValue;
use crate::utils::{BitMask, ByteMask};
use crate::zipper::{ReadZipperUntracked, Zipper, ZipperReadOnlyIteration, ZipperMoving, ZipperReadOnlyValues};

#[cfg(not(miri))]
use gxhash::{GxHasher, HashMap, HashMapExt};

#[cfg(miri)]
use std::collections::HashMap;

#[derive(Debug)]
pub struct Histogram<T : std::cmp::Eq + std::hash::Hash> {
  pub counts: Vec<usize>,
  pub lookup: HashMap<T, usize>
}
impl <T : std::cmp::Eq + std::hash::Hash> Histogram<T> {
  pub fn from(iter: impl IntoIterator<Item=T>) -> Self {
    let mut counts = vec![];
    let mut lookup = HashMap::new();
    iter.into_iter().for_each(|t| {
      match lookup.entry(t) {
        Entry::Occupied(i) => { counts[*i.get()] += 1; }
        Entry::Vacant(i) => { i.insert(counts.len()); counts.push(1) }
      }
    });
    let mut indices: Vec<usize> = (0..counts.len()).collect();
    indices.sort_by_key(|i| counts[*i]);
    counts.sort(); // this is wasteful, can use argsort
    for (_, v) in lookup.iter_mut() { *v = indices[*v]; }
    Histogram { counts, lookup }
  }

  pub fn table(&self) -> Vec<(&T, usize)> {
    // this is wasteful, perhaps we should use a deconstructed hashmap so &[(T, usize)] coincides with our internal representation
    let mut v = vec![(null(), 0usize); self.counts.len()];
    for (t, i) in self.lookup.iter() {
      v[*i] = (t, self.counts[*i])
    }
    unsafe { std::mem::transmute(v) }
  }
}

#[derive(Clone)]
pub struct Filtered<T, D : Distribution<T> + Clone, P : Fn(&T) -> bool> { pub d: D, pub p: P, pub pd: PhantomData<T> }
impl <T, D : Distribution<T> + Clone, P : Fn(&T) -> bool> Distribution<T> for Filtered<T, D, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    loop {
      let s = self.d.sample(rng);
      if (self.p)(&s) { return s }
    }
  }
}

#[derive(Clone)]
pub struct Mapped<T, S, D : Distribution<T> + Clone, F : Fn(T) -> S + Clone> { pub d: D, pub f: F, pub pd: PhantomData<(T, S)> }
impl <T, S, D : Distribution<T> + Clone, F : Fn(T) -> S + Clone> Distribution<S> for Mapped<T, S, D, F> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> S {
    (self.f)(self.d.sample(rng))
  }
}

#[derive(Clone)]
pub struct Collected<T, S, D : Distribution<T> + Clone, P : Fn(T) -> Option<S> + Clone> { pub d: D, pub pf: P, pub pd: PhantomData<(T, S)> }
impl <T, S, D : Distribution<T> + Clone, P : Fn(T) -> Option<S> + Clone> Distribution<S> for Collected<T, S, D, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> S {
    loop {
      let t = self.d.sample(rng);
      match (self.pf)(t) {
        None => {}
        Some(s) => { return s }
      }
    }
  }
}

#[derive(Clone)]
pub struct Product2<X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, Z, F : Fn(X, Y) -> Z + Clone> { pub dx: DX, pub dy: DY, pub f: F,
  pub pd: PhantomData<(X, Y, Z)> }
impl <X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, Z, F : Fn(X, Y) -> Z + Clone> Distribution<Z> for Product2<X, DX, Y, DY, Z, F> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Z {
    (self.f)(self.dx.sample(rng), self.dy.sample(rng))
  }
}

#[derive(Clone)]
pub struct Choice2<X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, DB : Distribution<bool> + Clone> { pub dx: DX, pub dy: DY, pub db: DB,
  pub pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, DB : Distribution<bool> + Clone> Distribution<Result<X, Y>> for Choice2<X, DX, Y, DY, DB> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Result<X, Y> {
    if self.db.sample(rng) { Ok(self.dx.sample(rng)) }
    else { Err(self.dy.sample(rng)) }
  }
}

#[derive(Clone)]
pub struct Dependent2<X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, FDY : Fn(X) -> DY + Clone> { pub dx: DX, pub fdy: FDY,
  pub pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X> + Clone, Y, DY : Distribution<Y> + Clone, FDY : Fn(X) -> DY + Clone> Distribution<Y> for Dependent2<X, DX, Y, DY, FDY> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    (self.fdy)(self.dx.sample(rng)).sample(rng)
  }
}

#[derive(Clone)]
pub struct Concentrated<X, DX : Distribution<X> + Clone, A : Clone, Y, FA : Fn(&mut A, X) -> Option<Y>> { pub dx: DX, pub z: A, pub fa: FA,
  pub pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X> + Clone, A : Clone, Y, FA : Fn(&mut A, X) -> Option<Y>> Distribution<Y> for Concentrated<X, DX, A, Y, FA> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    let mut a = self.z.clone();
    loop {
      match (self.fa)(&mut a, self.dx.sample(rng)) {
        None => {}
        Some(y) => { return y }
      }
    }
  }
}

#[derive(Clone)]
pub struct Diluted<X, DX : Distribution<X> + Clone, A : Clone, Y, FA : Fn(X) -> A, FAY : Fn(&mut A) -> Option<Y>> { pub dx: DX, pub fa: FA, pub fay: FAY,
  pub pd: PhantomData<(X, A, Y)> }
impl <X, DX : Distribution<X> + Clone, A : Clone, Y, FA : Fn(X) -> A, FAY : Fn(&mut A) -> Option<Y>> Distribution<Y> for Diluted<X, DX, A, Y, FA, FAY> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    let mut a = (self.fa)(self.dx.sample(rng));
    (self.fay)(&mut a).expect("fay returns at least once per fa call")
  }

  fn sample_iter<R>(self, rng: R) -> Iter<Self, R, Y> where R : Rng, Self : Sized {
    panic!("This function returning a concrete object makes it impossible to override the iterator behavior")
  }
}

#[derive(Clone)]
pub struct Degenerate<T : Clone> { pub element: T }
impl <T : Clone> Distribution<T> for Degenerate<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    self.element.clone()
  }
}

#[derive(Clone)]
pub struct Categorical<T : Clone, ElemD : Distribution<usize> + Clone> { pub elements: Vec<T>, pub ed: ElemD }
impl <T : Clone, ElemD : Distribution<usize> + Clone> Distribution<T> for Categorical<T, ElemD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    self.elements[self.ed.sample(rng)].clone()
  }
}
pub fn ratios<T : Clone>(ep: impl IntoIterator<Item=(T, usize)>) -> Categorical<T, Mapped<usize, usize, Uniform<usize>, impl Fn(usize) -> usize + Clone>> {
  let mut elements = vec![];
  let mut cdf = vec![];
  let mut sum = 0;
  for (e, r) in ep.into_iter() {
    elements.push(e);
    cdf.push(sum);
    sum += r;
  }
  let us = Uniform::try_from(0..sum).unwrap();
  Categorical {
    elements,
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    ed: Mapped{ d: us, f: move |x| { match cdf.binary_search(&x) {
      Ok(i) => { i }
      Err(i) => { i - 1 }
    }}, pd: PhantomData::default() }
  }
}

#[derive(Clone)]
pub struct Repeated<T, LengthD : Distribution<usize>, ItemD : Distribution<T>> { pub lengthd: LengthD, pub itemd: ItemD, pub pd: PhantomData<T> }
impl <T, LengthD : Distribution<usize>, ItemD : Distribution<T>> Distribution<Vec<T>> for Repeated<T, LengthD, ItemD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<T> {
    let l = self.lengthd.sample(rng);
    Vec::from_iter(std::iter::repeat_with(|| self.itemd.sample(rng)).take(l))
  }
}

#[derive(Clone)]
pub struct Sentinel<MByteD : Distribution<Option<u8>> + Clone> { pub mbd: MByteD }
impl <MByteD : Distribution<Option<u8>> + Clone> Distribution<Vec<u8>> for Sentinel<MByteD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<u8> {
    let mut v = vec![];
    while let Some(e) = self.mbd.sample(rng) {
      v.push(e)
    }
    v
  }
}

#[derive(Clone)]
pub struct UniformTrie<T : TrieValue, PathD : Distribution<Vec<u8>> + Clone, ValueD : Distribution<T> + Clone> { pub size: usize, pub pd: PathD, pub vd: ValueD, pub ph: PhantomData<T> }
impl <T : TrieValue, PathD : Distribution<Vec<u8>> + Clone, ValueD : Distribution<T> + Clone> Distribution<BytesTrieMap<T>> for UniformTrie<T, PathD, ValueD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BytesTrieMap<T> {
    let mut btm = BytesTrieMap::new();
    for i in 0..self.size {
      btm.insert(&self.pd.sample(rng)[..], self.vd.sample(rng));
    }
    btm
  }
}

/*
// fancier Trie Distributions WIP
pub struct GrowTrie<T, SproutD : Fn(&BytesTrieMap<T>) -> Distribution<BytesTrieMap<T>>> { seed: BytesTrieMap<T>, sd: SproutD }
impl <T, SproutD : Fn(T) -> Distribution<&BytesTrieMap<T>>> Distribution<BytesTrieMap<T>> for GrowTrie<T, SproutD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BytesTrieMap<T> {
    let mut btm = BytesTrieMap::new();
    for i in 0..self.size {
      btm.insert(&self.pd.sample(rng)[..], self.vd.sample(rng));
    }
    btm
  }
}*/

#[derive(Clone)]
pub struct FairTrieValue<T : TrieValue> { pub source: BytesTrieMap<T> }
impl <T : TrieValue> Distribution<(Vec<u8>, T)> for FairTrieValue<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, T) {
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    let mut rz = self.source.read_zipper();
    let size = rz.val_count();
    let target = rng.random_range(0..size);
    let mut i = 0;
    while let Some(t) = rz.to_next_get_value() {
      if i == target { return (rz.path().to_vec(), t.clone()) }
      i += 1;
    }
    unreachable!();
  }
}

#[derive(Clone)]
pub struct DescendFirstTrieValue<T : TrieValue, ByteD : Distribution<u8> + Clone, P : Fn(&ReadZipperUntracked<T>) -> ByteD> { pub source: BytesTrieMap<T>, pub policy: P }
impl <T : TrieValue, ByteD : Distribution<u8> + Clone, P : Fn(&ReadZipperUntracked<T>) -> ByteD> Distribution<(Vec<u8>, T)> for DescendFirstTrieValue<T, ByteD, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, T) {
    let mut rz = self.source.read_zipper();
    while !rz.is_value() {
      let b = (self.policy)(&rz).sample(rng);
      rz.descend_to_byte(b);
    }
    (rz.path().to_vec(), rz.get_value().unwrap().clone())
  }
}
fn unbiased_descend_first_policy<T : TrieValue>(rz: &ReadZipperUntracked<T>) -> Categorical<u8, Uniform<usize>> {
  let bm = rz.child_mask();
  Categorical{ elements: bm.iter().collect(), ed: Uniform::try_from(0..bm.count_bits()).unwrap() }
}

#[derive(Clone)]
pub struct FairTriePath<T : TrieValue> { pub source: BytesTrieMap<T> }
impl <T : TrieValue> Distribution<(Vec<u8>, Option<T>)> for FairTriePath<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, Option<T>) {
    use crate::morphisms::Catamorphism;
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    let size = Catamorphism::into_cata_cached(self.source.clone(), |_: &ByteMask, ws: &mut [usize], mv: Option<&T>, path: &[u8]| {
      ws.iter().sum::<usize>() + 1
    });
    let target = rng.random_range(0..size);
    let mut i = 0;
    Catamorphism::into_cata_side_effect_fallible(self.source.clone(), |_: &ByteMask, _, mv: Option<&T>, path: &[u8]| {
      if i == target { Err((path.to_vec(), mv.cloned())) } else { i += 1; Ok(()) }
    }).unwrap_err()
  }
}

#[derive(Clone)]
pub struct DescendTriePath<T : TrieValue, S, SByteD : Distribution<Result<u8, S>> + Clone, P : Fn(&ReadZipperUntracked<T>) -> SByteD> { pub source: BytesTrieMap<T>, pub policy: P, pub ph: PhantomData<S> }
impl <T : TrieValue, S, SByteD : Distribution<Result<u8, S>> + Clone, P : Fn(&ReadZipperUntracked<T>) -> SByteD> Distribution<(Vec<u8>, S)> for DescendTriePath<T, S, SByteD, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, S) {
    let mut rz = self.source.read_zipper();
    loop {
      match (self.policy)(&rz).sample(rng) {
        Ok(b) => { rz.descend_to_byte(b); }
        Err(s) => { return (rz.path().to_vec(), s) }
      }
    }
    unreachable!()
  }
}
fn unbiased_descend_last_policy<T : TrieValue>(rz: &ReadZipperUntracked<T>) -> Choice2<u8, Categorical<u8, Uniform<usize>>, T, Degenerate<T>, Degenerate<bool>> {
  let bm = rz.child_mask();
  let options: Vec<u8> = bm.iter().collect();
  let noptions = options.len();

  //GOAT!!  The `std::mem::MaybeUninit::uninit().assume_init()` is guaranteed to be UB, and it was here was causing a SIGTRAP.
  // I am guessing we probably want to return a degenerate distribution from this entire function if we can't
  // compose one of the arguments to the Choice2 distribution.  If that's not possible, then the Choice2 could
  // be modified to hold options for the downstream distributions.
  //
  //A third option is to bound `T` by `Default`
  Choice2 {
    db: Degenerate{ element: noptions > 0 },
    dx: Categorical{ elements: options, ed: Uniform::try_from(0..noptions).unwrap() },
    dy: Degenerate{ element: rz.get_value().cloned().unwrap() },
    pd: PhantomData::default()
  }
}


#[cfg(test)]
mod tests {
  use std::hint::black_box;
  use std::time::Instant;
  use rand::rngs::StdRng;
  use rand::SeedableRng;
  use rand_distr::{Exp, Normal, Triangular, Uniform};
  use crate::fuzzer::*;
  use crate::ring::Lattice;
  use crate::zipper::{ZipperWriting, ZipperSubtries};

  #[test]
  fn fixed_length() {
    let mut rng = StdRng::from_seed([0; 32]);
    let path_fuzzer = Repeated { lengthd: Degenerate{ element: 3 }, itemd: Categorical { elements: "abcd".as_bytes().to_vec(),
      ed: Uniform::try_from(0..4).unwrap() }, pd: PhantomData::default() };
    let trie_fuzzer = UniformTrie { size: 10, pd: path_fuzzer, vd: Degenerate{ element: () }, ph: PhantomData::default() };
    let trie = trie_fuzzer.sample(&mut rng);
    let res = ["aaa", "aac", "bba", "bdd", "cbb", "cbd", "dab", "dac", "dca"];
    trie.iter().zip(res).for_each(|(x, y)| assert_eq!(x.0.as_slice(), y.as_bytes()));
  }

  #[test]
  fn variable_length() {
    let mut rng = StdRng::from_seed([0; 32]);
    let path_fuzzer = Filtered{ d: Sentinel { mbd: Mapped{ d: Categorical { elements: "abcd\0".as_bytes().to_vec(),
      ed: Uniform::try_from(0..5).unwrap() }, f: |x| if x == b'\0' { None } else { Some(x) }, pd: PhantomData::default() } }, p: |x| !x.is_empty(), pd: PhantomData::default() };
    let trie_fuzzer = UniformTrie { size: 10, pd: path_fuzzer, vd: Degenerate{ element: () }, ph: PhantomData::default() };
    let trie = trie_fuzzer.sample(&mut rng);
    // println!("{:?}", trie.iter().map(|(p, _)| String::from_utf8(p).unwrap()).collect::<Vec<_>>());
    let res = ["aa", "acbdddacbcbdbad", "bbddad", "bd", "caccb", "cba", "cbcdbccb", "dadbcdbcaaadb", "dbabbdaabc", "dbb"];
    trie.iter().zip(res).for_each(|(x, y)| assert_eq!(x.0.as_slice(), y.as_bytes()));
  }

  #[test]
  fn fair_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = FairTrieValue{ source: btm };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| v).take(6*samples));
    let achieved: Vec<usize> = hist.table().into_iter().map(|(k, c)|
      ((c as f64)/((samples/100) as f64)).round() as usize).collect();
    achieved.into_iter().for_each(|c| assert_eq!(c, 100));
  }

  #[test]
  fn descend_first_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abcd", 10), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = DescendFirstTrieValue{ source: btm, policy: unbiased_descend_first_policy };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| *v).take(6*samples));
    // println!("{:?}", hist.table());
    let achieved: Vec<(i32, i32)> = hist.table().into_iter().map(|(k, c)|
      (*k, ((c as f64)/((samples/10) as f64)).round() as i32)).collect();
    assert_eq!(&achieved[..], &[(3, 5), (2, 5), (5, 10), (4, 10), (0, 15), (1, 15)]);
  }

  #[test]
  fn descend_last_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abcd", 10), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = DescendTriePath{ source: btm, policy: unbiased_descend_last_policy, ph: Default::default() };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| *v).take(6*samples));
    // println!("{:?}", hist.table());
    let achieved: Vec<(i32, i32)> = hist.table().into_iter().map(|(k, c)|
        (*k, ((c as f64)/((samples/10) as f64)).round() as i32)).collect();
    assert_eq!(&achieved[..], &[(3, 5), (2, 5), (5, 10), (4, 10), (10, 15), (1, 15)]);
  }

  #[test]
  fn fair_trie_path() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = FairTriePath{ source: btm };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(p, _)| p).take(10*samples));
    let achieved: Vec<usize> = hist.table().into_iter().map(|(k, c)|
      ((c as f64)/((samples/100) as f64)).round() as usize).collect();
    achieved.into_iter().for_each(|c| assert_eq!(c, 100));
  }

  #[test]
  fn resample_trie() {
    const samples: usize = 10;
    let mut rng = StdRng::from_seed([0; 32]);
    let mut btm = BytesTrieMap::new();
    let rs = ["Abbotsford", "Abbottabad", "Abcoude", "Abdul Hakim", "Abdulino", "Abdullahnagar", "Abdurahmoni Jomi", "Abejorral", "Abelardo Luz",
      "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
    rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });
    let lengths = Triangular::new(1f32, 5., 1.5).unwrap();
    let submaps = Collected {
      d: Product2 {
        dx: FairTriePath { source: btm.clone() },
        dy: lengths,
        f: |(path, v), l| if v.is_none() && path.len() == l.round() as usize { Some(path) } else { None }, pd: PhantomData::default() },
      pf: |mp| mp.map(|p| btm.read_zipper_at_path(p).make_map().unwrap()), pd: PhantomData::default()};

    // println!("{:?}", submap.iter().map(|(p, v)| (String::from_utf8(p).unwrap(), v)).collect::<Vec<_>>())
    assert_eq!(submaps.clone().sample_iter(rng.clone()).map(|x| x.iter().map(|(p, v)| (String::from_utf8(p).unwrap(), *v)).collect::<Vec<_>>()).take(4).collect::<Vec<_>>(), vec![
      vec![("otsford".to_string(), 0), ("ottabad".to_string(), 1)],
      vec![("bbotsford".to_string(), 0), ("bbottabad".to_string(), 1), ("bcoude".to_string(), 2), ("bdul Hakim".to_string(), 3), ("bdulino".to_string(), 4), ("bdullahnagar".to_string(), 5), ("bdurahmoni Jomi".to_string(), 6), ("bejorral".to_string(), 7), ("belardo Luz".to_string(), 8)],
      vec![("'i".to_string(), 17), ("an".to_string(), 9), ("ane".to_string(), 10), ("anus".to_string(), 11), ("ulus".to_string(), 12)],
      vec![("oude".to_string(), 2)]]);

    let resampled = Concentrated {
      dx: Product2{ dx: FairTriePath{ source: btm.clone() }, dy: submaps, f: |(p, _), sm| {
        let mut r = BytesTrieMap::new();
        r.write_zipper_at_path(&p[..]).graft_map(sm);
        r
      }, pd: PhantomData::default() },
      z: (BytesTrieMap::new(), 0),
      fa: |(a, c), sm| {
        a.join_into(sm);
        *c += 1;
        if *c == samples { Some(std::mem::take(a)) } else { None }
      }, pd: PhantomData::default()
    };

    let resampled10 = resampled.sample(&mut rng);
    assert_eq!(["Abbotsahmoni Jomi", "Abbottabens", "Abbottaber", "Abbottabicon", "Abbottabicundus",
                "Abdul Hakimm'i", "Abdul Hakimman", "Abdul Hakimmane", "Abdul Hakimmanus",
                "Abdul Hakimmulus", "Abdurahens", "Abduraher", "Abdurahicon", "Abdurahicundus",
                "Abdurahmoni Jom'i", "Abdurahmoni Joman", "Abdurahmoni Jomane",
                "Abdurahmoni Jomanus", "Abdurahmoni Jomulus", "Abdurahmoni jorral",
                "Abdurahmoni lardo Luz", "Abdurahmoniens", "Abdurahmonier", "Abdurahmoniicon",
                "Abdurahmoniicundus", "Abdurahmonoude", "Abelus", "romuoude"][..],
               resampled10.iter().map(|(p, _)| String::from_utf8(p).unwrap()).collect::<Vec<_>>());
  }

  #[test]
  fn remove_bug_reproduction() {
    const ntries: usize = 10;
    const npaths: usize = 10;
    const nremoves: usize = 10;
    let rng = StdRng::from_seed([0; 32]);
    let path_fuzzer = Filtered{ d: Sentinel { mbd: Mapped{ d: Categorical { elements: "abcd\0".as_bytes().to_vec(),
      ed: Uniform::try_from(0..5).unwrap() }, f: |x| if x == b'\0' { None } else { Some(x) }, pd: PhantomData::default()} }, p: |x| !x.is_empty(), pd: PhantomData::default() };
    let trie_fuzzer = UniformTrie { size: npaths, pd: path_fuzzer.clone(), vd: Degenerate{ element: () }, ph: PhantomData::default() };

    trie_fuzzer.sample_iter(rng.clone()).take(ntries).for_each(|mut trie| {
      // println!("let mut btm = BytesTrieMap::from_iter({:?}.iter().map(|(p, v)| (p.as_bytes(), v)));", trie.iter().map(|(p, v)| (String::from_utf8(p).unwrap(), v)).collect::<Vec<_>>());
      path_fuzzer.clone().sample_iter(rng.clone()).take(nremoves).for_each(|path| {
        // println!("btm.remove({:?}.as_bytes());", String::from_utf8(path.clone()).unwrap());
        trie.remove(path);
      });
      black_box(trie);
    })
  }

  #[test]
  fn monte_carlo_pi() {
    const samples: usize = 100000;
    let rng = StdRng::from_seed([0; 32]);
    let sx = Uniform::new(0.0, 1.0).unwrap();
    let sy = Uniform::new(0.0, 1.0).unwrap();
    let sxy = Product2 { dx: sx, dy: sy, f: |x, y| (x, y), pd: PhantomData::default() };
    let spi = Concentrated { dx: sxy, z: (0, 0), fa: |i_o, (x, y)| {
      if x*x + y*y < 1.0 { i_o.0 += 1 } else { i_o.1 += 1 }
      if i_o.0 + i_o.1 > samples { Some(4f64*(i_o.0 as f64/(i_o.0 + i_o.1) as f64)) } else { None }
    }, pd: Default::default() };

    spi.sample_iter(rng).take(10).for_each(|api| assert!(3.13 < api && api < 3.15) );
  }

  #[test]
  fn categorical_samples() {
    const samples: usize = 1000;
    let rng = StdRng::from_seed([0; 32]);
    let expected = [('b', 2usize), ('a', 10), ('c', 29), ('d', 100)];
    let cd = ratios(expected.into_iter());
    let hist = Histogram::from(cd.sample_iter(rng).take(samples*(10+2+29+100)));
    let achieved: Vec<(char, usize)> = hist.table().into_iter().map(|(k, c)|
      (*k, ((c as f64)/(samples as f64)).round() as usize)).collect();
    assert_eq!(&expected[..], &achieved[..]);
  }

  #[test]
  fn zipper_basic_0() {
    const ntries: usize = 100;
    const npaths: usize = 100;
    const ndescends: usize = 100;
    let rng = StdRng::from_seed([0; 32]);
    let rng_ = StdRng::from_seed([!0; 32]);
    let path_fuzzer = Filtered{ d: Sentinel { mbd: Mapped{ d: Categorical { elements: "abcd\0".as_bytes().to_vec(),
      ed: Uniform::try_from(0..5).unwrap() }, f: |x| if x == b'\0' { None } else { Some(x) }, pd: PhantomData::default()} }, p: |x| !x.is_empty(), pd: PhantomData::default() };
    let trie_fuzzer = UniformTrie { size: npaths, pd: path_fuzzer.clone(), vd: Degenerate{ element: () }, ph: PhantomData::default() };

    // ACTION := DESCEND_TO p | ASCEND i
    // { RZ.descend_to(p); RZ.ascend(p.len()) } =:= {}  
    // { RZ.descend_to(p1); RZ.descend_to(p2) } =:= { RZ.descend_to(p1.concat(p2)) } 
    // { RZ.ascend(i); RZ.ascend(j) } =:= { RZ.ascend(i+j) } 
    // { RZ = TRIE.read_zipper(); RZ.ascend(k) } =:= { RZ = TRIE.read_zipper(); } 
    // { RZ = TRIE.read_zipper(); ACT(RZ); RZ.reset() } =:= { RZ = TRIE.read_zipper(); } 
    // { RZ = TRIE.read_zipper(); ACT(RZ); RZ.reset() } =:= { RZ = TRIE.read_zipper(); } 
    // { RZ.reset(); RZ.descend_to(p) } =:= { RZ.move_to(p); } 

    trie_fuzzer.sample_iter(rng.clone()).take(ntries).for_each(|mut trie| {
      // println!("let mut btm = BytesTrieMap::from_iter({:?}.iter().map(|(p, v)| (p.as_bytes(), v)));", trie.iter().map(|(p, v)| (String::from_utf8(p).unwrap(), v)).collect::<Vec<_>>());
      let mut rz = trie.read_zipper();
      path_fuzzer.clone().sample_iter(rng.clone()).take(ndescends).for_each(|path| {
        rz.descend_to(&path[..]);
        assert_eq!(rz.get_value(), trie.get(&path[..]));
        path_fuzzer.clone().sample_iter(rng_.clone()).take(ndescends).for_each(|path| {
          rz.descend_to(&path[..]);
          rz.ascend(path.len());
        });
        assert_eq!(rz.path(), &path[..]);
        assert_eq!(rz.get_value(), trie.get(&path[..]));
        path_fuzzer.clone().sample_iter(rng_.clone()).take(ndescends).for_each(|path| {
          println!("prev {:?}", rz.path());
          rz.move_to_path(&path[..]);
          assert_eq!(rz.path(), &path[..]);
          assert_eq!(rz.get_value(), trie.get(&path[..]));
        });
        rz.reset();

      });
      drop(rz);
      black_box(trie);
    })
  }
}
