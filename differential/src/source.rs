//! Where fuzzer inputs come from, shared by `in_process` and `crash_fuzz`.

/// Where inputs come from.
///
/// `get` is deterministic in `idx` and holds no state between calls, so which
/// thread runs an input cannot change it and a failing input can be re-derived
/// from its index alone.  Mirrors `InputSource` in `lean/differential.py`; a
/// queue-backed source drops in here the same way.
pub enum Source {
    Random { seed: u64, count: usize, maxlen: usize },
    Files(Vec<String>),
}

impl Source {
    pub fn len(&self) -> usize {
        match self {
            Source::Random { count, .. } => *count,
            Source::Files(v) => v.len(),
        }
    }

    pub fn name(&self, idx: usize) -> String {
        match self {
            Source::Random { .. } => format!("random#{idx:06}"),
            Source::Files(v) => v[idx].clone(),
        }
    }

    pub fn get(&self, idx: usize) -> Vec<u8> {
        match *self {
            Source::Random { seed, maxlen, .. } => {
                // splitmix64, seeded per index so generation parallelises without
                // changing what gets tested.
                let mut s = seed.wrapping_mul(0x9E3779B97F4A7C15)
                    ^ (idx as u64).wrapping_mul(0xBF58476D1CE4E5B9);
                let mut next = || {
                    s = s.wrapping_add(0x9E3779B97F4A7C15);
                    let mut z = s;
                    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
                    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
                    z ^ (z >> 31)
                };
                // The same *distribution* as `RandomInputs.get` in
                // `lean/differential.py` -- `randrange(8, maxlen)`, i.e. uniform
                // on `[8, maxlen)` -- so a divergence rate measured here is
                // directly comparable to one measured there.  The bit stream
                // differs (splitmix64 against Python's Mersenne Twister) and is
                // meant to: two independent samples of the same population.
                let span = maxlen.saturating_sub(8).max(1);
                let n = 8 + (next() as usize) % span;
                (0..n).map(|_| next() as u8).collect()
            }
            Source::Files(ref v) => std::fs::read(&v[idx]).expect("cannot read input"),
        }
    }
}
