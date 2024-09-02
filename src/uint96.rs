use core::{
    cmp::Ordering,
    fmt,
    hash::Hash,
    mem,
    num::{ParseIntError, TryFromIntError},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
    str::FromStr,
};

#[cfg(feature = "rand")]
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};

/// An unsigned 96-bit integer.
#[repr(C, align(4))]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct u96(u32, u32, u32);
const _: () = assert!(mem::size_of::<u96>() == 96 / 8);

impl u96 {
    const MASK: u128 = (1u128 << Self::BITS) - 1;

    /// The size of the integer in bits.
    pub const BITS: u32 = 96;

    /// The largest value that can be represented by this type.
    pub const MAX: Self = Self(u32::MAX, u32::MAX, u32::MAX);

    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self(0, 0, 0);

    /// Creates a `u96`.
    ///
    /// It returns `None` if `v` is greater than `(1<<96)-1`.
    pub const fn new(v: u128) -> Option<Self> {
        if v > Self::MASK {
            None
        } else {
            Some(Self::wrapping_new(v))
        }
    }

    /// Creates a `u96` from a `u64`.
    pub const fn from_u64(v: u64) -> Self {
        Self::from_words(v, 0)
    }

    const fn from_words(lo: u64, hi: u32) -> Self {
        Self(lo as u32, (lo >> 32) as u32, hi)
    }

    /// Converts the `u96` to a `u128`.
    pub const fn to_u128(self) -> u128 {
        (self.low64() as u128) | ((self.hi32() as u128) << 64)
    }

    /// Converts the `u96` to a `u64`, or returns `None` if it
    /// is too large to fit in a `u64`.
    pub const fn try_to_u64(self) -> Option<u64> {
        if self.hi32() != 0 {
            None
        } else {
            Some(self.low64())
        }
    }

    /// Reports whether `self == rhs`.
    const fn eq(self, rhs: Self) -> bool {
        self.0 == rhs.0 && self.1 == rhs.1 && self.2 == rhs.2
    }

    /// Reports whether `self >= rhs`.
    const fn gte(self, rhs: Self) -> bool {
        self.cmp(rhs).is_ge()
    }

    /// Reports whether `self < rhs`.
    const fn less(self, rhs: Self) -> bool {
        self.cmp(rhs).is_lt()
    }

    const fn cmp(self, rhs: Self) -> Ordering {
        if self.hi32() < rhs.hi32() || (self.hi32() == rhs.hi32() && self.low64() < rhs.low64()) {
            Ordering::Less
        } else if self.eq(rhs) {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    /// Reports whether the integer is zero.
    pub const fn is_zero(self) -> bool {
        self.0 == 0 && self.1 == 0 && self.2 == 0
    }

    /// Returns the low 64 bits.
    const fn low64(self) -> u64 {
        // SAFETY: `u64` is smaller than `self`.
        unsafe { mem::transmute_copy(&[self.0, self.1]) }
    }

    /// Returns the low 64 bits.
    const fn hi32(self) -> u32 {
        self.2
    }

    /// Shifts `self` left `rhs` times, filling with zeros on the
    /// right.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rdfp::u96;
    ///
    /// assert_eq!(u96::MAX.logical_shl(95),
    ///     "39614081257132168796771975168".parse::<u96>().unwrap());
    /// assert_eq!(u96::MAX.logical_shl(96), u96::from_u64(0));
    /// assert_eq!(u96::MAX.logical_shl(u32::MAX), u96::from_u64(0));
    /// ```
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn logical_shl(self, rhs: u32) -> Self {
        if rhs >= Self::BITS {
            Self::MIN
        } else {
            Self::wrapping_new(self.to_u128() << rhs)
        }
    }

    /// Shifts `self` right `rhs` times, filling with zeros on
    /// the left.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rdfp::u96;
    ///
    /// assert_eq!(u96::MAX.logical_shr(95), u96::from_u64(1));
    /// assert_eq!(u96::MAX.logical_shr(96), u96::from_u64(0));
    /// assert_eq!(u96::MAX.logical_shr(u32::MAX), u96::from_u64(0));
    /// ```
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn logical_shr(self, rhs: u32) -> Self {
        if rhs >= Self::BITS {
            Self::MIN
        } else {
            Self::wrapping_new(self.to_u128() >> rhs)
        }
    }

    /// Computes the quotient and remainder of `self / rhs` such
    /// that
    ///
    /// ```text
    /// q = self/rhs
    /// r = self - rhs*q
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn quorem(self, rhs: Self) -> (Self, Self) {
        let x = self;
        let y = rhs;

        if x.less(y) {
            // x/y for x < y = 0.
            // x%y for x < y = x.
            return (Self::MIN, x);
        }

        // `y` is 64 bits, so use fast division.
        if y.hi32() == 0 {
            let (q, r) = self.quorem64(y.low64());
            return (q, Self::from_u64(r));
        }

        if !cfg!(feature = "slow-128") {
            let q = self.to_u128() / rhs.to_u128();
            let r = self.to_u128() % rhs.to_u128();
            return (Self::wrapping_new(q), Self::wrapping_new(r));
        }

        // Perform 128-bit division as if the u96 is a u128 whose
        // upper 32 bits are all zero.
        let n = y.hi32().leading_zeros();
        let y1 = y.logical_shl(n); // y<<n
        let x1 = x.logical_shr(1); // x>>1
        let tq = {
            let (mut tq, _) = div64(x1.hi32() as u64, x1.low64(), y1.hi32() as u64);
            tq >>= 63 - n; // `n` is in [0,32]
            if tq != 0 {
                tq -= 1;
            }
            tq
        };
        let mut q = tq;
        let ytq = y.wrapping_mul64(tq); // ytq = y*tq
        let mut r = x.wrapping_sub(ytq); // r = x-ytq
        if r.gte(y) {
            q = q.wrapping_add(1); // q += 1
            r = r.wrapping_sub(y); // r -= y
        }
        let q = u96::from_u64(q);
        (q, r)
    }

    // TODO(eric): this is used in benchmarks, but I don't want
    // to expose it. Put it behind a feature or something?
    #[doc(hidden)]
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn quorem64(self, rhs: u64) -> (Self, u64) {
        if self.low64() < rhs {
            let (q, r) = div64(self.hi32() as u64, self.low64(), rhs);
            return (Self::from_u64(q), r);
        }
        let (hi, r) = div64(0, self.hi32() as u64, rhs);
        let (lo, r) = div64(r, self.low64(), rhs);
        (Self::from_words(lo, hi as u32), r)
    }
}

// Checked.
impl u96 {
    /// Computes `self + rhs`, returning `None` if the sum
    /// overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.overflowing_add(rhs) {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }

    /// Computes `self / rhs`, returning `None` if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_div(self, rhs: Self) -> Option<Self> {
        match self.overflowing_div(rhs) {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }

    /// Computes `self * rhs`, returning `None` if the product
    /// overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        match self.overflowing_mul(rhs) {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }

    /// Computes `-self`, returning `None` unless `self` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_neg(self) -> Option<Self> {
        match self.overflowing_neg() {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }

    /// Computes `self % rhs`, returning `None` if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
        match self.overflowing_rem(rhs) {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }

    /// Computes `self - rhs`, returning `None` if the difference
    /// overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.overflowing_sub(rhs) {
            (_, true) => None,
            (v, _) => Some(v),
        }
    }
}

// Const.
impl u96 {
    /// Computes `self + rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// the sum overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_add(self, rhs: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_add(rhs)
        } else {
            self.wrapping_add(rhs)
        }
    }

    /// Computes `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_div(self, rhs: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_div(rhs)
        } else {
            self.wrapping_div(rhs)
        }
    }

    /// Computes `self & rhs`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0, self.1 & rhs.1, self.2 & rhs.2)
    }

    /// Computes `self | rhs`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0, self.1 | rhs.1, self.2 | rhs.2)
    }

    /// Computes `self ^ rhs`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_bitxor(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0, self.1 ^ rhs.1, self.2 ^ rhs.2)
    }

    /// Computes `self * rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// the product overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_mul(self, rhs: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_mul(rhs)
        } else {
            self.wrapping_mul(rhs)
        }
    }

    /// Computes `-self`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// the integer is non-zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_neg(self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_neg()
        } else {
            self.wrapping_neg()
        }
    }

    /// Computes `!self`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_not(self) -> Self {
        Self(!self.0, !self.1, !self.2)
    }

    /// Computes `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_rem(self, rhs: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_rem(rhs)
        } else {
            self.wrapping_rem(rhs)
        }
    }

    /// Computes `self << rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// `rhs >= 96`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_shl(self, rhs: u32) -> Self {
        debug_assert!(rhs < Self::BITS);

        self.wrapping_shl(rhs)
    }

    /// Computes `self >> rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// `rhs >= 96`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_shr(self, rhs: u32) -> Self {
        debug_assert!(rhs < Self::BITS);

        self.wrapping_shr(rhs)
    }

    /// Computes `self - rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if debug assertions are enabled and
    /// the difference overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_sub(self, rhs: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_sub(rhs)
        } else {
            self.wrapping_sub(rhs)
        }
    }
}

// Overflowing.
impl u96 {
    /// Creates a `u96`, wrapping `v` if it is greater than
    /// `2^96-1`.
    #[must_use]
    pub const fn overflowing_new(v: u128) -> (Self, bool) {
        const MASK: u64 = u64::MAX ^ (u32::MAX as u64);
        let lo = v as u64;
        let hi = (v >> 64) as u64;
        let overflow = hi & MASK != 0;
        (Self::from_words(lo, hi as u32), overflow)
    }

    /// Computes `self + rhs` and also reports whether the sum
    /// overflowed.
    ///
    /// If an overflow occurs, the sum is wrapped.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, c) = self.low64().overflowing_add(rhs.low64());
        let (hi, c) = carrying_add32(self.hi32(), rhs.hi32(), c);
        (Self::from_words(lo, hi), c)
    }

    /// Computes `self / rhs` and also reports whether quotient
    /// overflowed.
    ///
    /// As division cannot overflow, the second value is always
    /// false.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        (self.quorem(rhs).0, false)
    }

    /// Computes `self * rhs` and also reports whether the sum
    /// overflowed.
    ///
    /// If an overflow occurs, the product is wrapped.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (lo, c) = carrying_mul64(self.low64(), rhs.low64(), 0);
        let (hi, _) = carrying_mul64(self.hi32() as u64, rhs.low64(), c);
        let (hi, c) = carrying_mul64(self.low64(), rhs.hi32() as u64, hi);
        let overflow = hi > (u32::MAX as u64) || c != 0;
        (Self::from_words(lo, hi as u32), overflow)
    }

    /// Computes `!self + 1` and also reports whether the result
    /// overflowed.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_neg(self) -> (Self, bool) {
        Self::MIN.overflowing_sub(self)
    }

    /// Computes `self % rhs` and also reports whether remainder
    /// overflowed.
    ///
    /// As division cannot overflow, the second value is always
    /// false.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        (self.quorem(rhs).1, false)
    }

    /// Computes `self - rhs` and also reports whether the
    /// difference overflowed.
    ///
    /// If an overflow occurs, the difference is wrapped.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, b) = self.low64().overflowing_sub(rhs.low64());
        let (hi, b) = borrowing_sub32(self.hi32(), rhs.hi32(), b);
        (Self::from_words(lo, hi), b)
    }
}

// Strict.
impl u96 {
    /// Computes `self + rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if the sum overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_add(self, rhs: Self) -> Self {
        match self.overflowing_add(rhs) {
            (_, true) => overflow_panic::add(),
            (v, _) => v,
        }
    }

    /// Computes `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.`
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_div(self, rhs: Self) -> Self {
        match self.overflowing_div(rhs) {
            (_, true) => overflow_panic::div(),
            (v, _) => v,
        }
    }

    /// Computes `self * rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if the sum overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_mul(self, rhs: Self) -> Self {
        match self.overflowing_mul(rhs) {
            (_, true) => overflow_panic::mul(),
            (v, _) => v,
        }
    }

    /// Computes `-self`.
    ///
    /// # Panics
    ///
    /// This function panics if the integer is non-zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_neg(self) -> Self {
        match self.overflowing_neg() {
            (_, true) => overflow_panic::neg(),
            (v, _) => v,
        }
    }

    /// Computes `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.`
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_rem(self, rhs: Self) -> Self {
        match self.overflowing_rem(rhs) {
            (_, true) => overflow_panic::rem(),
            (v, _) => v,
        }
    }

    /// Computes `self - rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if the difference overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn strict_sub(self, rhs: Self) -> Self {
        match self.overflowing_sub(rhs) {
            (_, true) => overflow_panic::sub(),
            (v, _) => v,
        }
    }
}

// Wrapping.
impl u96 {
    /// Creates a `u96`, wrapping `v` if it is greater than
    /// `2^96-1`.
    #[must_use]
    pub const fn wrapping_new(v: u128) -> Self {
        Self::from_words(v as u64, (v >> 64) as u32)
    }

    /// Computes `self + rhs`, wrapping if the sum overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        self.overflowing_add(rhs).0
    }

    /// Computes `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_div(self, rhs: Self) -> Self {
        self.overflowing_div(rhs).0
    }

    /// Computes `self * rhs`, wrapping if the product overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        if cfg!(feature = "slow-128") {
            self.overflowing_mul(rhs).0
        } else {
            let z = self.to_u128().wrapping_mul(rhs.to_u128());
            Self::wrapping_new(z)
        }
    }

    /// Computes `self * rhs`, wrapping if the product overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    const fn wrapping_mul64(self, rhs: u64) -> Self {
        if !cfg!(feature = "slow-128") {
            let z = self.to_u128().wrapping_mul(rhs as u128);
            Self::wrapping_new(z)
        } else {
            let (lo, mut hi) = mul64(self.low64(), rhs);
            hi = hi.wrapping_add((self.hi32() as u64).wrapping_mul(rhs));
            Self::from_words(lo, hi as u32)
        }
    }

    /// Computes `-self`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_neg(self) -> Self {
        Self::MIN.wrapping_sub(self)
    }

    /// Computes `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function panics if `rhs` is zero.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_rem(self, rhs: Self) -> Self {
        self.overflowing_rem(rhs).0
    }

    /// Computes `self << mask(rhs)`, where `mask` removes any
    /// high order bits from `rhs` that would cause the shift to
    /// overflow.
    ///
    /// # Note
    ///
    /// You probably want [`logical_shl`][Self::logical_shl].
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        self.logical_shl(rhs & (Self::BITS - 1))
    }

    /// Computes `self >> mask(rhs)`, where `mask` removes any
    /// high order bits from `rhs` that would cause the shift to
    /// overflow.
    ///
    /// # Note
    ///
    /// You probably want [`logical_shr`][Self::logical_shr].
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        self.logical_shr(rhs & (Self::BITS - 1))
    }

    /// Computes `self - rhs`, wrapping if the difference
    /// overflows.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        self.overflowing_sub(rhs).0
    }
}

impl BitAnd for u96 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.const_bitand(rhs)
    }
}

impl BitAndAssign for u96 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.const_bitand(rhs);
    }
}

impl BitOr for u96 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.const_bitor(rhs)
    }
}

impl BitOrAssign for u96 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.const_bitor(rhs);
    }
}

impl BitXor for u96 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.const_bitxor(rhs)
    }
}

impl BitXorAssign for u96 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.const_bitxor(rhs);
    }
}

impl Not for u96 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.const_not()
    }
}

impl Shl<u32> for u96 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.const_shl(rhs)
    }
}

impl ShlAssign<u32> for u96 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = self.const_shl(rhs);
    }
}

impl Shr<u32> for u96 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.const_shr(rhs)
    }
}

impl ShrAssign<u32> for u96 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = self.const_shr(rhs);
    }
}

impl PartialEq<u64> for u96 {
    fn eq(&self, other: &u64) -> bool {
        self.hi32() == 0 && self.low64() == *other
    }
}

impl PartialEq<u128> for u96 {
    fn eq(&self, other: &u128) -> bool {
        self.to_u128() == *other
    }
}

impl PartialOrd<u64> for u96 {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        if self.2 != 0 {
            Some(Ordering::Greater)
        } else {
            PartialOrd::partial_cmp(&self.low64(), other)
        }
    }
}

macro_rules! fmt_impl {
    ($($ty:ident),+ $(,)?) => {
        $(
            impl fmt::$ty for u96 {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.to_u128().fmt(f)
                }
            }
        )+
    };
}
fmt_impl! {
    Debug,
    Display,
    Binary,
    Octal,
    LowerHex,
    UpperHex,
}

macro_rules! from_impl {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl From<$ty> for u96 {
                fn from(v: $ty) -> Self {
                    Self::from_u64(u64::from(v))
                }
            }
        )+
    };
}
from_impl!(bool, u8, u16, u32, u64);

macro_rules! try_from_impl {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl TryFrom<$ty> for u96 {
                type Error = TryFromIntError;
                fn try_from(v: $ty) -> Result<Self, Self::Error> {
                    match u96::new(v.try_into()?) {
                        Some(v) => Ok(v),
                        None => Err(try_from_int_error()),
                    }
                }
            }
        )+
    };
}
try_from_impl!(i8, i16, i32, i64, i128, isize, u128, usize);

fn try_from_int_error() -> TryFromIntError {
    let result = u8::try_from(u32::MAX);
    // SAFETY: `u32::MAX` is not a valid representation of `u8`,
    // so this should always be `Err`.
    unsafe { result.unwrap_err_unchecked() }
}

impl FromStr for u96 {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match Self::new(s.parse::<u128>()?) {
            Some(v) => Ok(v),
            None => Err(parse_int_error()),
        }
    }
}

fn parse_int_error() -> ParseIntError {
    let result = "?".parse::<u8>();
    // SAFETY: `?` is not a valid representation of `u8`, so this
    // should always be `Err`.
    unsafe { result.unwrap_err_unchecked() }
}

/// ```text
/// q = (hi, lo) / y
/// r = (hi, lo) % y
/// ```
const fn div64(hi: u64, lo: u64, y: u64) -> (u64, u64) {
    let x = ((hi as u128) << 64) | (lo as u128);
    let q = (x / (y as u128)) as u64;
    let r = (x % (y as u128)) as u64;
    (q, r)
}

/// Returns `x*y` as `(lo, hi)`.
const fn mul64(x: u64, y: u64) -> (u64, u64) {
    // SAFETY: Overflow is contained in the wider type.
    //
    // ((1^64)-1)^2 < (1^128)-1
    let z = unsafe { (x as u128).unchecked_mul(y as u128) };
    (z as u64, (z >> 64) as u64)
}

/// Returns `x*y+z` as `(lo, hi)`.
const fn carrying_mul64(x: u64, y: u64, carry: u64) -> (u64, u64) {
    // SAFETY: Overflow is contained in the wider type.
    //
    // ((2^64)-1) + ((2^64)-1)^2 < (2^128)-1
    let z = unsafe {
        (x as u128)
            .unchecked_mul(y as u128)
            .unchecked_add(carry as u128)
    };
    (z as u64, (z >> 64) as u64)
}

/// Returns `x+y+c` as `(lo, hi)`.
const fn carrying_add32(x: u32, y: u32, carry: bool) -> (u32, bool) {
    let (sum, c0) = x.overflowing_add(y);
    let (sum, c1) = sum.overflowing_add(carry as u32);
    (sum, c0 != c1)
}

/// Returns `x+y+c` as `(lo, hi)`.
const fn borrowing_sub32(x: u32, y: u32, borrow: bool) -> (u32, bool) {
    let (d, c0) = x.overflowing_sub(y);
    let (d, c1) = d.overflowing_sub(borrow as u32);
    (d, c0 != c1)
}

/// <https://github.com/rust-lang/rust/blob/f6fa358a182b2f8e4d5a10faac4dae950493c9bc/library/core/src/num/overflow_panic.rs>
#[allow(dead_code)]
mod overflow_panic {
    #[cold]
    #[track_caller]
    pub const fn add() -> ! {
        panic!("attempt to add with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn sub() -> ! {
        panic!("attempt to subtract with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn mul() -> ! {
        panic!("attempt to multiply with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn div() -> ! {
        panic!("attempt to divide with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn rem() -> ! {
        panic!("attempt to calculate the remainder with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn neg() -> ! {
        panic!("attempt to negate with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn shr() -> ! {
        panic!("attempt to shift right with overflow")
    }

    #[cold]
    #[track_caller]
    pub const fn shl() -> ! {
        panic!("attempt to shift left with overflow")
    }
}

#[cfg(feature = "rand")]
impl Distribution<u96> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u96 {
        u96(rng.gen(), rng.gen(), rng.gen())
    }
}

#[cfg(test)]
mod tests {
    use rand::{random, thread_rng, Rng};
    use ruint::{ToUintError, Uint};

    use super::*;

    type Uint96 = Uint<96, 2>;
    impl TryFrom<u96> for Uint96 {
        type Error = ToUintError<Self>;
        fn try_from(x: u96) -> Result<Self, ToUintError<Self>> {
            Ok(Uint96::from_limbs([x.low64(), x.hi32() as u64]))
        }
    }
    impl PartialEq<Uint96> for u96 {
        fn eq(&self, other: &Uint96) -> bool {
            PartialEq::eq(&[self.low64(), self.hi32() as u64], other.as_limbs())
        }
    }
    impl PartialOrd<Uint96> for u96 {
        fn partial_cmp(&self, other: &Uint96) -> Option<Ordering> {
            PartialOrd::partial_cmp(&[self.low64(), self.hi32() as u64], other.as_limbs())
        }
    }

    macro_rules! u96 {
        ($v:literal) => {{
            u96::new($v).unwrap()
        }};
    }

    #[test]
    fn test_logical_shl() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u32 = thread_rng().gen_range(0..u96::BITS - 1);

            let got = x.logical_shl(y);
            let want = Uint96::from(x).wrapping_shl(y as usize);
            assert_eq!(got, want, "#{i}: {x} << {y}");
        }
    }

    #[test]
    fn test_logical_shr() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u32 = thread_rng().gen_range(0..u96::BITS - 1);

            let got = x.logical_shr(y);
            let want = Uint96::from(x).wrapping_shr(y as usize);
            assert_eq!(got, want, "#{i}: {x} >> {y}");
        }
    }

    #[test]
    fn test_overflowing_add() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.overflowing_add(y);
            let want = Uint96::from(x).overflowing_add(Uint96::from(y));
            assert_eq!(got.0, want.0, "#{i}: {x} + {y}");
            assert_eq!(got.1, want.1, "#{i}: {x} + {y}");
        }
    }

    #[test]
    fn test_overflowing_mul() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.overflowing_mul(y);
            let want = Uint96::from(x).overflowing_mul(Uint96::from(y));
            assert_eq!(got.0, want.0, "#{i}: {x} * {y}");
            assert_eq!(got.1, want.1, "#{i}: {x} * {y}");
        }
    }

    #[test]
    fn test_overflowing_sub() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.overflowing_sub(y);
            let want = Uint96::from(x).overflowing_sub(Uint96::from(y));
            assert_eq!(got.0, want.0, "#{i}: {x} - {y}");
            assert_eq!(got.1, want.1, "#{i}: {x} - {y}");
        }
    }

    #[test]
    fn test_wrapping_add_boundary() {
        let tests = [
            (u96!(0), u96!(0), u96!(0)),
            (u96!(1), u96!(0), u96!(1)),
            (u96!(1), u96!(1), u96!(2)),
            (u96::MAX, u96!(1), u96!(0)),
            (u96::MAX, u96!(2), u96!(1)),
        ];
        for (i, (x, y, want)) in tests.into_iter().enumerate() {
            let got = x.wrapping_add(y);
            assert_eq!(got, want, "#{i}");
        }
    }

    #[test]
    fn test_wrapping_add() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.wrapping_add(y);
            let want = Uint96::from(x).wrapping_add(Uint96::from(y));
            assert_eq!(got, want, "#{i}: {x} + {y}");
        }
    }

    #[test]
    fn test_wrapping_mul() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.wrapping_mul(y);
            let want = Uint96::from(x).wrapping_mul(Uint96::from(y));
            assert_eq!(got, want, "#{i}: {x} * {y}");
        }
    }

    #[test]
    fn test_quorem() {
        for i in 0..100_000 {
            let x: u96 = random();
            let y = loop {
                let y: u96 = random();
                if !y.is_zero() {
                    break y;
                }
            };

            let got = x.quorem(y);
            let want = (
                Uint96::from(x).wrapping_div(Uint96::from(y)),
                Uint96::from(x).wrapping_rem(Uint96::from(y)),
            );
            assert_eq!(got.0, want.0, "#{i}: {x} / {y}");
            assert_eq!(got.1, want.1, "#{i}: {x} % {y}");
        }
    }

    #[test]
    fn test_wrapping_shl() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u32 = thread_rng().gen_range(0..u96::BITS - 1);

            let got = x.wrapping_shl(y);
            let want = Uint96::from(x).wrapping_shl((y & (u96::BITS - 1)) as usize);
            assert_eq!(got, want, "#{i}: {x} << {y}");
        }
    }

    #[test]
    fn test_wrapping_shr() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u32 = thread_rng().gen_range(0..u96::BITS - 1);

            let got = x.wrapping_shr(y);
            let want = Uint96::from(x).wrapping_shr((y & (u96::BITS - 1)) as usize);
            assert_eq!(got, want, "#{i}: {x} >> {y}");
        }
    }

    #[test]
    fn test_wrapping_sub() {
        for i in 0..500_000 {
            let x: u96 = random();
            let y: u96 = random();

            let got = x.wrapping_sub(y);
            let want = Uint96::from(x).wrapping_sub(Uint96::from(y));
            assert_eq!(got, want, "#{i}: {x} - {y}");
        }
    }
}
