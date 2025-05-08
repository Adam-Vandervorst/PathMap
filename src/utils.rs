
use crate::ring::*;

/// A 256-bit type containing a bit for every possible value in a byte
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct ByteMask(pub [u64; 4]);

impl ByteMask {
    pub const EMPTY: ByteMask = Self(empty_mask());

    /// Create a new empty ByteMask
    #[inline]
    pub const fn new() -> Self {
        Self(empty_mask())
    }
    /// Unwraps the `ByteMask` type to yield the inner array
    #[inline]
    pub fn into_inner(self) -> [u64; 4] {
        self.0
    }
    /// Create an iterator over every byte, in ascending order
    #[inline]
    pub fn iter(&self) -> ByteMaskIter {
        self.byte_mask_iter()
    }

    /// Returns how many set bits precede the requested bit
    pub fn index_of(&self, byte: u8) -> u8 {
        if byte == 0 {
            return 0;
        }
        let mut count = 0;
        let mut active;
        let mask = !0u64 >> (63 - ((byte - 1) & 0b00111111));
        active = self.0[0];
        'unroll: {
            if byte <= 0x40 { break 'unroll }
            count += active.count_ones();
            active = self.0[1];
            if byte <= 0x80 { break 'unroll }
            count += active.count_ones();
            active = self.0[2];
            if byte <= 0xc0 { break 'unroll }
            count += active.count_ones();
            active = self.0[3];
        }
        count += (active & mask).count_ones();
        count as u8
    }

    /// Returns the byte corresponding to the `nth` set bit in the mask, counting forwards or backwards
    pub fn indexed_bit<const FORWARD: bool>(&self, idx: usize) -> Option<u8> {
        let mut i = if FORWARD { 0 } else { 3 };
        let mut m = self.0[i];
        let mut c = 0;
        let mut c_ahead = m.count_ones() as usize;
        loop {
            if idx < c_ahead { break; }
            if FORWARD { i += 1} else { i -= 1 };
            if i > 3 { return None }
            m = self.0[i];
            c = c_ahead;
            c_ahead += m.count_ones() as usize;
        }

        let mut loc;
        if !FORWARD {
            loc = 63 - m.leading_zeros();
            while c < idx {
                m ^= 1u64 << loc;
                loc = 63 - m.leading_zeros();
                c += 1;
            }
        } else {
            loc = m.trailing_zeros();
            while c < idx {
                m ^= 1u64 << loc;
                loc = m.trailing_zeros();
                c += 1;
            }
        }

        let byte = i << 6 | (loc as usize);
        // println!("{:#066b}", self.focus.mask[i]);
        // println!("{i} {loc} {byte}");
        debug_assert!(self.test_bit(byte as u8));

        Some(byte as u8)
    }
}

impl core::fmt::Debug for ByteMask {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl BitMask for ByteMask {
    #[inline]
    fn count_bits(&self) -> usize { self.0.count_bits() }
    #[inline]
    fn is_empty_mask(&self) -> bool { self.0.is_empty_mask() }
    #[inline]
    fn test_bit(&self, k: u8) -> bool { self.0.test_bit(k) }
    #[inline]
    fn set_bit(&mut self, k: u8) { self.0.set_bit(k) }
    #[inline]
    fn clear_bit(&mut self, k: u8) { self.0.clear_bit(k) }
    #[inline]
    fn make_empty(&mut self) {self.0.make_empty() }
    #[inline]
    fn or(&self, other: &Self) -> Self where Self: Sized { Self(self.0.or(&other.0)) }
    #[inline]
    fn and(&self, other: &Self) -> Self where Self: Sized { Self(self.0.and(&other.0)) }
    #[inline]
    fn xor(&self, other: &Self) -> Self where Self: Sized { Self(self.0.xor(&other.0)) }
    #[inline]
    fn andn(&self, other: &Self) -> Self where Self: Sized { Self(self.0.andn(&other.0)) }
    #[inline]
    fn not(&self) -> Self where Self: Sized { Self(self.0.not()) }
}

impl core::borrow::Borrow<[u64; 4]> for ByteMask {
    fn borrow(&self) -> &[u64; 4] {
        &self.0
    }
}

impl AsRef<[u64; 4]> for ByteMask {
    fn as_ref(&self) -> &[u64; 4] {
        &self.0
    }
}

impl From<u8> for ByteMask {
    #[inline]
    fn from(singleton_byte: u8) -> Self {
        let mut new_mask = Self::new();
        new_mask.set_bit(singleton_byte);
        new_mask
    }
}

impl From<[u64; 4]> for ByteMask {
    #[inline]
    fn from(mask: [u64; 4]) -> Self {
        Self(mask)
    }
}

impl From<ByteMask> for [u64; 4] {
    #[inline]
    fn from(mask: ByteMask) -> Self {
        mask.0
    }
}

impl IntoByteMaskIter for ByteMask {
    #[inline]
    fn byte_mask_iter(self) -> ByteMaskIter {
        self.0.byte_mask_iter()
    }
}

impl FromIterator<u8> for ByteMask {
    #[inline]
    fn from_iter<I: IntoIterator<Item=u8>>(iter: I) -> Self {
        let mut result = Self::new();
        for byte in iter.into_iter() {
            result.set_bit(byte);
        }
        result
    }
}

impl PartialEq<ByteMask> for [u64; 4] {
    #[inline]
    fn eq(&self, other: &ByteMask) -> bool {
        *self == other.0
    }
}

impl PartialEq<[u64; 4]> for ByteMask {
    #[inline]
    fn eq(&self, other: &[u64; 4]) -> bool {
        self.0 == *other
    }
}

impl core::ops::BitOr for ByteMask {
    type Output = Self;
    #[inline]
    fn bitor(self, other: Self) -> Self {
        self.or(&other)
    }
}

impl core::ops::BitOr for &ByteMask {
    type Output = ByteMask;
    #[inline]
    fn bitor(self, other: Self) -> ByteMask {
        self.or(other)
    }
}

impl core::ops::BitOrAssign for ByteMask {
    #[inline]
    fn bitor_assign(&mut self, other: Self) {
        *self = self.or(&other)
    }
}

impl core::ops::BitAnd for ByteMask {
    type Output = Self;
    #[inline]
    fn bitand(self, other: Self) -> Self {
        self.and(&other)
    }
}

impl core::ops::BitAnd for &ByteMask {
    type Output = ByteMask;
    #[inline]
    fn bitand(self, other: Self) -> ByteMask {
        self.and(other)
    }
}

impl core::ops::BitAndAssign for ByteMask {
    #[inline]
    fn bitand_assign(&mut self, other: Self) {
        *self = self.and(&other)
    }
}

impl Lattice for ByteMask {
    #[inline]
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        self.0.pjoin(&other.0).map(|mask| Self(mask))
    }
    #[inline]
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        self.0.pmeet(&other.0).map(|mask| Self(mask))
    }
    #[inline]
    fn bottom() -> Self {
        Self::new()
    }
}

impl DistributiveLattice for ByteMask {
    #[inline]
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        self.0.psubtract(&other.0).map(|mask| Self(mask))
    }
}

//GOAT, below here is functionality implemented on arrays of u64, which ought to be generalized to additional widths

/// Some useful bit-twiddling methods for working with the mask you might get from [child_mask](crate::zipper::Zipper::child_mask)
pub trait BitMask {
    /// Returns the number of set bits in `mask`
    fn count_bits(&self) -> usize;

    /// Returns `true` if all bits in `mask` are clear, otherwise returns `false`
    fn is_empty_mask(&self) -> bool;

    /// Returns `true` if the `k`th bit in `mask` is set, otherwise returns `false`
    fn test_bit(&self, k: u8) -> bool;

    /// Sets the `k`th bit in mask
    fn set_bit(&mut self, k: u8);

    /// Clears the `k`th bit in mask
    fn clear_bit(&mut self, k: u8);

    /// Clears all bits in the mask, restoring it to an empty mask
    fn make_empty(&mut self);

    /// Returns the bitwise `or` of the two masks
    ///
    /// |        |`other=0`|`other=1`
    /// |--------|---------|---------
    /// |`self=0`|    0    |    1
    /// |`self=1`|    1    |    1
    ///
    fn or(&self, other: &Self) -> Self where Self: Sized;

    /// Returns the bitwise `and` of the two masks
    ///
    /// |        |`other=0`|`other=1`
    /// |--------|---------|---------
    /// |`self=0`|    0    |    0
    /// |`self=1`|    0    |    1
    ///
    fn and(&self, other: &Self) -> Self where Self: Sized;

    /// Returns the bitwise `xor` of the two masks
    ///
    /// |        |`other=0`|`other=1`
    /// |--------|---------|---------
    /// |`self=0`|    0    |    1
    /// |`self=1`|    1    |    0
    ///
    fn xor(&self, other: &Self) -> Self where Self: Sized;

    /// Returns the bitwise `andn` (sometimes called the conditional) of the two masks
    ///
    /// |        |`other=0`|`other=1`
    /// |--------|---------|---------
    /// |`self=0`|    0    |    0
    /// |`self=1`|    1    |    0
    ///
    fn andn(&self, other: &Self) -> Self where Self: Sized;

    /// Returns the bitwise `not` of the mask
    fn not(&self) -> Self where Self: Sized;
}

impl BitMask for [u64; 4] {
    #[inline]
    fn count_bits(&self) -> usize {
        return (self[0].count_ones() + self[1].count_ones() + self[2].count_ones() + self[3].count_ones()) as usize;
    }
    #[inline]
    fn is_empty_mask(&self) -> bool {
        self[0] == 0 && self[1] == 0 && self[2] == 0 && self[3] == 0
    }
    #[inline]
    fn test_bit(&self, k: u8) -> bool {
        let idx = ((k & 0b11000000) >> 6) as usize;
        let bit_i = k & 0b00111111;
        debug_assert!(idx < 4);
        self[idx] & (1 << bit_i) > 0
    }
    #[inline]
    fn set_bit(&mut self, k: u8) {
        let idx = (k / 64) as usize;
        self[idx] |= 1 << (k % 64);
    }
    #[inline]
    fn clear_bit(&mut self, k: u8) {
        let idx = (k / 64) as usize;
        self[idx] ^= 1 << (k % 64);
    }
    #[inline]
    fn make_empty(&mut self) {
        *self = [0; 4];
    }
    #[inline]
    fn or(&self, other: &Self) -> Self where Self: Sized {
        [self[0] | other[0], self[1] | other[1], self[2] | other[2], self[3] | other[3]]
    }
    #[inline]
    fn and(&self, other: &Self) -> Self where Self: Sized {
        [self[0] & other[0], self[1] & other[1], self[2] & other[2], self[3] & other[3]]
    }
    #[inline]
    fn xor(&self, other: &Self) -> Self where Self: Sized {
        [self[0] ^ other[0], self[1] ^ other[1], self[2] ^ other[2], self[3] ^ other[3]]
    }
    #[inline]
    fn andn(&self, other: &Self) -> Self where Self: Sized {
        [self[0] & !other[0], self[1] & !other[1], self[2] & !other[2], self[3] & !other[3]]
    }
    #[inline]
    fn not(&self) -> Self where Self: Sized {
        [!self[0], !self[1], !self[2], !self[3]]
    }
}

/// An iterator to visit each byte in a byte mask in ascending order.  Useful for working with the mask
/// as you might get from [child_mask](crate::zipper::Zipper::child_mask)
pub struct ByteMaskIter {
    i: u8,
    mask: [u64; 4],
}

pub trait IntoByteMaskIter {
    fn byte_mask_iter(self) -> ByteMaskIter;
}

impl IntoByteMaskIter for [u64; 4] {
    fn byte_mask_iter(self) -> ByteMaskIter {
        ByteMaskIter::from(self)
    }
}

impl IntoByteMaskIter for &[u64; 4] {
    fn byte_mask_iter(self) -> ByteMaskIter {
        ByteMaskIter::from(*self)
    }
}

impl From<[u64; 4]> for ByteMaskIter {
    fn from(mask: [u64; 4]) -> Self {
        Self::new(mask)
    }
}

impl ByteMaskIter {
    /// Make a new `ByteMaskIter` from a mask, as you might get from [child_mask](crate::zipper::Zipper::child_mask)
    pub fn new(mask: [u64; 4]) -> Self {
        Self {
            i: 0,
            mask,
        }
    }
}

impl Iterator for ByteMaskIter {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            let w = &mut self.mask[self.i as usize];
            if *w != 0 {
                let wi = w.trailing_zeros() as u8;
                *w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some(index)
            } else if self.i < 3 {
                self.i += 1;
            } else {
                return None
            }
        }
    }
}

//GOAT, This needs to be generalized to bit sets of other widths
impl Lattice for [u64; 4] {
    #[inline]
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        let result = [self[0] | other[0], self[1] | other[1], self[2] | other[2], self[3] | other[3]];
        bitmask_algebraic_result(result, self, other)
    }
    #[inline]
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        let result = [self[0] & other[0], self[1] & other[1], self[2] & other[2], self[3] & other[3]];
        bitmask_algebraic_result(result, self, other)
    }
    #[inline]
    fn bottom() -> Self {
        empty_mask()
    }
}

//GOAT, This should be generalized to bit sets of other widths
impl DistributiveLattice for [u64; 4] {
    #[inline]
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        let result = [self[0] & !other[0], self[1] & !other[1], self[2] & !other[2], self[3] & !other[3]];
        bitmask_algebraic_result(result, self, other)
    }
}

/// Internal function to compose AlgebraicResult after algebraic operation
#[inline]
fn bitmask_algebraic_result(result: [u64; 4], self_mask: &[u64; 4], other_mask: &[u64; 4]) -> AlgebraicResult<[u64; 4]> {
    if result.is_empty() {
        return AlgebraicResult::None
    }
    let mut mask = 0;
    if result == *self_mask {
        mask  = SELF_IDENT;
    }
    if result == *other_mask {
        mask |= COUNTER_IDENT;
    }
    if mask > 0 {
        return AlgebraicResult::Identity(mask)
    } else {
        AlgebraicResult::Element(result)
    }
}

/// Returns a new empty mask
#[inline]
pub const fn empty_mask() -> [u64; 4] {
    [0; 4]
}

#[test]
fn bit_utils_test() {
    let mut mask = empty_mask();
    assert_eq!(mask.count_bits(), 0);
    assert_eq!(mask.is_empty_mask(), true);

    mask.set_bit(b'C');
    mask.set_bit(b'a');
    mask.set_bit(b't');
    assert_eq!(mask.is_empty_mask(), false);
    assert_eq!(mask.count_bits(), 3);

    mask.set_bit(b'C');
    mask.set_bit(b'a');
    mask.set_bit(b'n');
    assert_eq!(mask.count_bits(), 4);

    mask.clear_bit(b't');
    assert_eq!(mask.test_bit(b'n'), true);
    assert_eq!(mask.test_bit(b't'), false);
}

// LP: I switched `unlikely` to `count_shared_cold` I saw a 8% bump in the `common_prefix` benchmark.
// FIXME: Branch prediction hint. This is currently only available on nightly
#[cfg(not(feature = "nightly"))]
pub use core::convert::{identity as likely, identity as unlikely};
#[cfg(feature = "nightly")]
pub use core::intrinsics::{likely, unlikely};

const PAGE_SIZE: usize = 4096;

#[inline(always)]
unsafe fn same_page<const VECTOR_SIZE: usize>(slice: &[u8]) -> bool {
    let address = slice.as_ptr() as usize;
    // Mask to keep only the last 12 bits
    let offset_within_page = address & (PAGE_SIZE - 1);
    // Check if the 16/32/64th byte from the current offset exceeds the page boundary
    offset_within_page < PAGE_SIZE - VECTOR_SIZE
}

#[inline(always)]
fn count_shared_bare(a: &[u8], b: &[u8]) -> usize {
    let mut cnt = 0;
    loop {
        if unlikely(cnt == a.len()) {break}
        if unlikely(cnt == b.len()) {break}
        if unsafe{ a.get_unchecked(cnt) != b.get_unchecked(cnt) } {break}
        cnt += 1;
    }
    cnt
}

#[cold]
fn count_shared_cold(a: &[u8], b: &[u8]) -> usize {
    count_shared_bare(a, b)
}

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
            if unlikely(ne == 0 && max_shared > 32) {
                32 + count_shared_avx2(&p[32..], &q[32..])
            } else {
                (_tzcnt_u32(ne) as usize).min(max_shared)
            }
        } else {
            count_shared_cold(p, q)
        }
    }
}

/// Returns the number of characters shared between two slices
#[cfg(target_feature="avx2")]
#[inline]
pub fn find_prefix_overlap(a: &[u8], b: &[u8]) -> usize {
    count_shared_avx2(a, b)
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn count_shared_neon(p: &[u8], q: &[u8]) -> usize {
    use core::arch::aarch64::*;
    unsafe {
        let pl = p.len();
        let ql = q.len();
        let max_shared = pl.min(ql);
        if unlikely(max_shared == 0) { return 0 }

        if same_page::<16>(p) && same_page::<16>(q) {
            let pv = vld1q_u8(p.as_ptr());
            let qv = vld1q_u8(q.as_ptr());
            let eq = vceqq_u8(pv, qv);

            //UGH! There must be a better way to do this...
            // let neg = vmvnq_u8(eq);
            // let lo: u64 = vgetq_lane_u64(core::mem::transmute(neg), 0);
            // let hi: u64 = vgetq_lane_u64(core::mem::transmute(neg), 1);
            // let count = if lo != 0 {
            //     lo.trailing_zeros()
            // } else {
            //     64 + hi.trailing_zeros()
            // } / 8;

            //UGH! This code is actually a bit faster than the commented out code above.
            // I'm sure I'm just not familiar enough with the neon ISA
            let mut bytes = [core::mem::MaybeUninit::<u8>::uninit(); 16];
            vst1q_u8(bytes.as_mut_ptr().cast(), eq);
            let scalar128 = u128::from_le_bytes(core::mem::transmute(bytes));
            let count = scalar128.trailing_ones() / 8;

            if count != 16 || max_shared < 17 {
                (count as usize).min(max_shared)
            } else {
                let new_len = max_shared-16;
                16 + count_shared_neon(core::slice::from_raw_parts(p.as_ptr().add(16), new_len), core::slice::from_raw_parts(q.as_ptr().add(16), new_len))
            }
        } else {
            return count_shared_cold(p, q);
        }
    }
}

/// Returns the number of characters shared between two slices
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline]
pub fn find_prefix_overlap(a: &[u8], b: &[u8]) -> usize {
    count_shared_neon(a, b)
}

/// Returns the number of characters shared between two slices
#[cfg(all(not(target_feature="avx2"), not(target_feature="neon")))]
#[inline]
pub fn find_prefix_overlap(a: &[u8], b: &[u8]) -> usize {
    count_shared_bare(a, b)
}

#[test]
fn find_prefix_overlap_test() {
    let tests = [
        ("12345", "67890", 0),
        ("", "12300", 0),
        ("12345", "", 0),
        ("12345", "12300", 3),
        ("123", "123000000", 3),
        ("123456789012345678901234567890xxxx", "123456789012345678901234567890yy", 30),
        ("123456789012345678901234567890123456789012345678901234567890xxxx", "123456789012345678901234567890123456789012345678901234567890yy", 60),
        ("1234567890123456xxxx", "1234567890123456yyyyyyy", 16),
        ("123456789012345xxxx", "123456789012345yyyyyyy", 15),
        ("12345678901234567xxxx", "12345678901234567yyyyyyy", 17),
        ("1234567890123456789012345678901xxxx", "1234567890123456789012345678901yy", 31),
        ("12345678901234567890123456789012xxxx", "12345678901234567890123456789012yy", 32),
        ("123456789012345678901234567890123xxxx", "123456789012345678901234567890123yy", 33),
        ("123456789012345678901234567890123456789012345678901234567890123xxxx", "123456789012345678901234567890123456789012345678901234567890123yy", 63),
        ("1234567890123456789012345678901234567890123456789012345678901234xxxx", "1234567890123456789012345678901234567890123456789012345678901234yy", 64),
        ("12345678901234567890123456789012345678901234567890123456789012345xxxx", "12345678901234567890123456789012345678901234567890123456789012345yy", 65),
    ];

    for test in tests {
        let overlap = find_prefix_overlap(test.0.as_bytes(), test.1.as_bytes());
        assert_eq!(overlap, test.2);
    }
}
