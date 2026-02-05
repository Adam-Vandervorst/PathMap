
use crate::ring::*;

pub mod ints;

pub mod debug;

/// Use `fast_slice_utils` directly.  We don't want to maintain this re-export from pathmap
//GOAT, remove this re-export when nothing downstream is going to break
#[deprecated]
pub use fast_slice_utils::find_prefix_overlap;

/// A 256-bit type containing a bit for every possible value in a byte
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct ByteMask(pub [u64; 4]);

impl ByteMask {
    pub const EMPTY: ByteMask = Self([0u64; 4]);
    pub const FULL: ByteMask = Self([!0u64; 4]);

    const SUBSET: [ByteMask; 256] = const {
        let mut bm = [[0u64; 4]; 256];
        let mut i = 0;
        while i < 256 {
            let mut j = 0;
            while j < 256 {
                if i & j == j { bm[i][j / 64] |= 1 << (j % 64) }
                j += 1;
            }
            i += 1;
        }
        unsafe { std::mem::transmute(bm) }
    };

    /// Nth row of the sierpinsky triangle
    pub fn subset(b: u8) -> Self {
        Self::SUBSET[b as usize]
    }

    /// Create a new empty ByteMask
    #[inline]
    pub const fn new() -> Self {
        Self::EMPTY
    }
    /// Unwraps the `ByteMask` type to yield the inner array
    #[inline]
    pub fn into_inner(self) -> [u64; 4] {
        self.0
    }
    /// Create an iterator over every byte, in ascending order
    #[inline]
    pub fn iter(&self) -> ByteMaskIter {
        ByteMaskIter::from(self.0)
    }

    #[cfg(target_feature = "avx512f")]
    #[inline]
    fn avx(&self) -> std::arch::x86_64::__m256i {
        unsafe { std::mem::transmute(self.clone()) }
    }

    #[cfg(target_feature = "avx512f")]
    #[inline]
    fn from_avx(m: std::arch::x86_64::__m256i) -> Self {
        unsafe { std::mem::transmute(m) }
    }

    /// mask of non-zero nibble lo masks
    #[inline]
    pub fn nibble_mask(&self) -> u16 {
        #[cfg(target_feature = "avx512f")]
        unsafe {
            use std::arch::x86_64::*;
            _mm256_cmp_epi16_mask::<4>(self.avx(), _mm256_set1_epi8(0))
        }
        #[cfg(not(target_feature = "avx512f"))]
        unsafe {
            let mut r = 0;
            for (i, m) in std::mem::transmute::<_, [u16; 16]>(self.0).iter().enumerate() {
                if *m != 0 { r |= 1 << i }
            }
            r
        }
    }

    /// one of 16 sub-masks
    #[inline]
    pub fn lo_mask(&self, i: u8) -> u16 {
        unsafe { std::mem::transmute::<_, [u16; 16]>(self.0)[i as usize] }
    }

    #[inline]
    pub(crate) fn store_nz_lo_masks(&self, nm: u16, mut p: *mut u16) {
        #[cfg(target_feature = "avx512f")]
        unsafe {
            use std::arch::x86_64::*;
            _mm256_mask_compressstoreu_epi16(p as _, nm, self.avx())
        }
        #[cfg(not(target_feature = "avx512f"))]
        unsafe {
            for (i, m) in std::mem::transmute::<_, [u16; 16]>(self.0).iter().enumerate() {
                if ((nm >> i) & 1) != 0 { *p = *m; p = p.add(1) }
            }
        }
    }

    #[inline]
    pub(crate) fn load_nz_lo_masks(nm: u16, mut p: *const u16) -> Self {
        #[cfg(target_feature = "avx512f")]
        unsafe {
            use std::arch::x86_64::*;
            Self::from_avx(_mm256_maskz_expandloadu_epi16(nm, p as _))
        }
        #[cfg(not(target_feature = "avx512f"))]
        unsafe {
            let mut a = [0u16; 16];
            for i in 0..16 {
                if ((nm >> i) & 1) != 0 { a[i] = *p; p = p.add(1) }
            }
            std::mem::transmute(a)
        }
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

    /// Returns the bit in the mask corresponding to the next highest bit above `byte`, or `None`
    /// if `byte` was at or above the highest set bit in the mask
    pub fn next_bit(&self, byte: u8) -> Option<u8> {
        if byte == 255 {
            return None
        }
        let byte = byte + 1;
        let word_idx = byte >> 6;
        let mod_idx = byte & 0x3F;
        let mut mask = !0u64 << mod_idx;
        if word_idx == 0 {
            let cnt = (self.0[0] & mask).trailing_zeros() as u8;
            if cnt < 64 {
                return Some(cnt)
            }
            mask = !0u64;
        }
        if word_idx < 2 {
            let cnt = (self.0[1] & mask).trailing_zeros() as u8;
            if cnt < 64 {
                return Some(64 + cnt)
            }
            if word_idx == 1 {
                mask = !0u64;
            }
        }
        if word_idx < 3 {
            let cnt = (self.0[2] & mask).trailing_zeros() as u8;
            if cnt < 64 {
                return Some(128 + cnt)
            }
            if word_idx == 2 {
                mask = !0u64;
            }
        }
        let cnt = (self.0[3] & mask).trailing_zeros() as u8;
        if cnt < 64 {
            return Some(192 + cnt)
        }
        None
    }

    /// Returns the bit in the mask corresponding to the previous bit below `byte`, or `None`
    /// if `byte` was at or below the lowest set bit in the mask
    pub fn prev_bit(&self, byte: u8) -> Option<u8> {
        if byte == 0 {
            return None
        }
        let byte = byte - 1;
        let word_idx = byte >> 6;
        let mod_idx = byte & 0x3F;
        let mut mask = !0u64 >> (63 - mod_idx);
        if word_idx == 3 {
            let cnt = (self.0[3] & mask).leading_zeros() as u8;
            if cnt < 64 {
                return Some(255 - cnt)
            }
            mask = !0u64;
        }
        if word_idx > 1 {
            let cnt = (self.0[2] & mask).leading_zeros() as u8;
            if cnt < 64 {
                return Some(191 - cnt)
            }
            if word_idx == 2 {
                mask = !0u64;
            }
        }
        if word_idx > 0 {
            let cnt = (self.0[1] & mask).leading_zeros() as u8;
            if cnt < 64 {
                return Some(127 - cnt)
            }
            if word_idx == 1 {
                mask = !0u64;
            }
        }
        let cnt = (self.0[0] & mask).leading_zeros() as u8;
        if cnt < 64 {
            return Some(63 - cnt)
        }
        None
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

#[allow(deprecated)]
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

crate::impl_name_only_debug!(
    impl core::fmt::Debug for ByteMaskIter
);

/// Iterate over a [u64; 4].  Deprecated in favor [`ByteMask`]
#[deprecated]
pub trait IntoByteMaskIter {
    fn byte_mask_iter(self) -> ByteMaskIter;
}

#[allow(deprecated)]
impl IntoByteMaskIter for [u64; 4] {
    fn byte_mask_iter(self) -> ByteMaskIter {
        ByteMaskIter::from(self)
    }
}

#[allow(deprecated)]
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
#[deprecated]
pub const fn empty_mask() -> [u64; 4] {
    [0; 4]
}

#[test]
fn bit_utils_test() {
    let mut mask = ByteMask::EMPTY;
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

#[test]
fn next_bit_test() {
    fn do_test(test_mask: ByteMask) {
        let set_bits: Vec<u8> = (0..=255).into_iter().filter(|i| test_mask.test_bit(*i)).collect();

        let mut i = 0;
        let mut cnt = test_mask.test_bit(0) as usize;
        while let Some(next_bit) = test_mask.next_bit(i) {
            assert!(test_mask.test_bit(next_bit));
            i = next_bit;
            cnt += 1;
        }
        assert_eq!(cnt, set_bits.len());

        let mut i = 255;
        let mut cnt = test_mask.test_bit(255) as usize;
        while let Some(prev_bit) = test_mask.prev_bit(i) {
            assert!(test_mask.test_bit(prev_bit));
            i = prev_bit;
            cnt += 1;
        }
        assert_eq!(cnt, set_bits.len());
    }
    do_test(ByteMask::from([
        0b1010010010010010010010000000000000000000000000000000000000010101u64,
        0b0000000000000000000000000000000000000000100000000000000000000000u64,
        0b0000000000000000000000000000000000000000000000000000000000000000u64,
        0b1001000000000000000000000000000000000000000000000000000000000001u64,
    ]));
    do_test(ByteMask::from([
        0b0000000000000000000000000000000000000000000000000000000000000000u64,
        0b0000000000000000000000000000000000000000100000000000000000000000u64,
        0b0000000000000000000000000000000000000000000000000000000000000000u64,
        0b1001000000000000000000000000000000000000000000000000000000000001u64,
    ]));
    do_test(ByteMask::from(ByteMask::FULL));
}

#[test]
fn next_bit_test2() {
    let mut test_mask = ByteMask::EMPTY;
    test_mask.set_bit(39);
    test_mask.set_bit(97);
    test_mask.set_bit(117);

    assert_eq!(Some(39), test_mask.next_bit(0));
    assert_eq!(Some(97), test_mask.next_bit(39));
    assert_eq!(Some(117), test_mask.next_bit(97));
    assert_eq!(None, test_mask.next_bit(117));
}

