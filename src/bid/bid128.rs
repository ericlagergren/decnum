use core::{
    cmp::Ordering,
    fmt,
    mem::{size_of, MaybeUninit},
    num::FpCategory,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::{self, FromStr},
};

use super::arith113;
use crate::{
    conv::{self, Buffer, Fmt, ParseError},
    dpd::Dpd128,
    util::{self, assume, const_assert},
};

/// A 128-bit decimal floating point number.
///
/// (–1)^sign * coefficient * 10^exp
///
/// TODO: docs
#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Bid128(
    /// # Layout
    ///
    /// ## Bits
    ///
    /// 127: S
    /// 126-110: G
    /// 109-0: T
    ///
    /// ## Forms
    ///
    /// ### Form 1
    ///
    /// s 00eeeeee   (0)ttt tttttttttt tttttttttt
    /// s 01eeeeee   (0)ttt tttttttttt tttttttttt
    /// s 10eeeeee   (0)ttt tttttttttt tttttttttt
    ///
    /// ### Form 2
    ///
    /// s 1100eeeeee (100)t tttttttttt tttttttttt
    /// s 1101eeeeee (100)t tttttttttt tttttttttt
    /// s 1110eeeeee (100)t tttttttttt tttttttttt
    u128,
);
const_assert!(size_of::<Bid128>() == 128 / 8);

// Internal stuff.
impl Bid128 {
    const K: u32 = 128;
    const S: u32 = 1;
    const W: u32 = 12;
    const G: u32 = Self::W + 5;
    const T: u32 = 110;

    /// The bias added to the encoded exponent in order to
    /// convert it to the "actual" exponent.
    const BIAS: i16 = 6176;
    /// The maxmimum value of the encoded exponent.
    const LIMIT: u16 = 12287;
    /// Minimum unbiased exponent.
    const EMAX: i16 = 6144;
    /// Maximum unbiased exponent.
    const EMIN: i16 = -6143;

    const MAX_PREC: i16 = 34;

    /// The number of bits required to represent
    /// [`MAX_COEFF`][Self::MAX_COEFF].
    const MAX_COEFF_BITS: u32 = arith113::bitlen(Self::MAX_COEFF as u128);
    const MAX_COEFF_MASK: u128 = (1 << Self::MAX_COEFF_BITS) - 1;

    const SIGN_SHIFT: u32 = Self::K - Self::S;
    const SIGN_MASK: u128 = 1 << Self::SIGN_SHIFT;

    const COMB_BITS: u32 = Self::G;
    const COMB_SHIFT: u32 = Self::K - Self::S - Self::G;

    // Top N bits of the combination field.
    const COMB_TOP2: u128 = 0x3 << (Self::SIGN_SHIFT - 2);
    const COMB_TOP4: u128 = 0xf << (Self::SIGN_SHIFT - 4);
    const COMB_TOP5: u128 = 0x1f << (Self::SIGN_SHIFT - 5);
    const COMB_TOP6: u128 = 0x3f << (Self::SIGN_SHIFT - 6);

    const EXP_BITS: u32 = Self::W + 2;
    const EXP_MASK: u16 = (1 << Self::EXP_BITS) - 1;

    const FORM1_EXP_MASK: u128 = (Self::EXP_MASK as u128) << Self::FORM1_EXP_SHIFT;
    const FORM1_EXP_SHIFT: u32 = Self::SIGN_SHIFT - Self::EXP_BITS;

    const FORM2_EXP_MASK: u128 = Self::FORM1_EXP_MASK >> 2;
    const FORM2_EXP_SHIFT: u32 = Self::FORM1_EXP_SHIFT + 2;

    /// The number of bits in the form one coefficient.
    const FORM1_COEFF_BITS: u32 = 3 + Self::T;
    /// Gathers the bits in the form one coefficient.
    const FORM1_COEFF_MASK: u128 = (1 << Self::FORM1_COEFF_BITS) - 1;

    /// The number of bits in the form two coefficient.
    const FORM2_COEFF_BITS: u32 = 1 + Self::T;
    /// Gathers the bits in the form two coefficient.
    const FORM2_COEFF_MASK: u128 = (1 << Self::FORM2_COEFF_BITS) - 1;
    /// The implicit bits in the form two coefficient.
    const FORM2_IMPLICIT_COEFF_BITS: u128 = 0x8 << Self::T;

    const COEFF_BITS: u32 = Self::T;
    const COEFF_MASK: u128 = (1 << Self::COEFF_BITS) - 1;

    /// Do we need form two?
    const fn need_form2(coeff: u128) -> bool {
        // Form one is 3+T bits with an implicit leading 0b0.
        // Form two is 4+T bits with an implicit leading 0b100.

        if Self::MAX_COEFF_BITS <= Self::FORM1_COEFF_BITS {
            // The max coefficient fits in 3+T bits, so we do not
            // need form two.
            return false;
        }
        // If the MSB is set then we need form two.
        (coeff & Self::MAX_COEFF_MASK) >> (Self::MAX_COEFF_BITS - 1) != 0
    }

    const fn signbit(self) -> bool {
        (self.0 & Self::SIGN_MASK) != 0
    }

    /// Is this form one or form two?
    const fn is_form2(self) -> bool {
        self.0 & Self::COMB_TOP2 == Self::COMB_TOP2
    }

    /// Returns the biased exponment.
    ///
    /// If the number is finite, the result is in [0,
    /// [`LIMIT`][Self::LIMIT]].
    const fn biased_exp(self) -> u16 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let exp = if self.is_form2() {
            // exp = G[2:w+3]
            ((self.0 & Self::FORM2_EXP_MASK) >> Self::FORM2_EXP_SHIFT) as u16
        } else {
            // exp = G[0:w+1]
            ((self.0 & Self::FORM1_EXP_MASK) >> Self::FORM1_EXP_SHIFT) as u16
        };
        debug_assert!(exp & !Self::EXP_MASK == 0);
        debug_assert!(exp <= Self::LIMIT);

        exp
    }

    /// Returns the unbiased exponent.
    ///
    /// If the number is finite, the result is in
    /// [[`MIN_EXP`][Self::MIN_EXP], [`MAX_EXP`][Self::MAX_EXP]].
    const fn unbiased_exp(self) -> i16 {
        const_assert!(Bid128::LIMIT < i16::MAX as u16);
        const_assert!(i16::MAX - (Bid128::LIMIT as i16) > Bid128::BIAS);

        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        // `self.exp()` is in [0, LIMIT] and LIMIT < i16::MAX, so
        // the cast cannot wrap.
        //
        // The subtraction cannot wrap since
        //    LIMIT + BIAS < i16::MAX
        //    0 - BIAS > i16::MIN
        #[allow(clippy::cast_possible_wrap)]
        let exp = (self.biased_exp() as i16) - Self::BIAS;

        if self.is_finite() {
            // SAFETY: `self.unbiased_exp()` returns an integer
            // in [0, LIMIT]. Subtracting `BIAS` TODO
            unsafe {
                assume(exp >= Self::MIN_EXP);
                assume(exp <= Self::MAX_EXP);
            }
        }
        exp
    }

    /// Returns the adjusted exponent.
    ///
    /// This is `exp + digits - 1`.
    const fn adjusted_exp(self) -> i16 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        const_assert!(Bid128::DIGITS <= i16::MAX as u32);
        // `self.digits() as i16` does not wrap because it is in
        // [1, DIGITS], and `DIGITS <= i16::MAX`.
        #[allow(clippy::cast_possible_wrap)]
        let digits = self.digits() as i16;

        self.unbiased_exp() + digits - 1
    }

    /// Returns the full coefficient.
    const fn coeff(self) -> u128 {
        // The coefficient only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let coeff = if self.is_form2() {
            // 100 || G[w+4] || T
            Self::FORM2_IMPLICIT_COEFF_BITS | (self.0 & Self::FORM2_COEFF_MASK)
        } else {
            // G[w+2:w+4] || T
            self.0 & Self::FORM1_COEFF_MASK
        };

        // See 3.2(c)(2).
        if coeff > Self::MAX_COEFF as u128 {
            0
        } else {
            coeff
        }
    }

    /// Creates a finite number from its parts.
    pub(crate) const fn from_parts(sign: bool, exp: i16, coeff: u128) -> Self {
        debug_assert!(coeff <= Self::MAX_COEFF as u128);
        debug_assert!(exp >= Self::MIN_EXP);
        debug_assert!(exp <= Self::MAX_EXP);

        // TODO(eric): If `exp` is valid then this cannot
        // overflow. Maybe make sure of it?
        #[allow(clippy::cast_sign_loss)]
        let biased = (exp + Self::BIAS) as u16;

        let mut bits = 0;
        if Self::need_form2(coeff) {
            // s 1100eeeeee (100)t tttttttttt tttttttttt
            // s 1101eeeeee (100)t tttttttttt tttttttttt
            // s 1110eeeeee (100)t tttttttttt tttttttttt
            bits |= signbit(sign);
            bits |= Self::COMB_TOP2;
            bits |= (biased as u128) << Self::FORM2_EXP_SHIFT;
            bits |= coeff & ((1 << 111) - 1); // TODO: use consts
        } else {
            // s 00eeeeee   (0)ttt tttttttttt tttttttttt
            // s 01eeeeee   (0)ttt tttttttttt tttttttttt
            // s 10eeeeee   (0)ttt tttttttttt tttttttttt
            bits |= signbit(sign);
            bits |= (biased as u128) << Self::FORM1_EXP_SHIFT;
            bits |= coeff;
        }
        Self::from_bits(bits)
    }
}

// Public stuff.
impl Bid128 {
    /// The largest value that can be represented by this type.
    pub const MAX: Self = Self::new(Self::MAX_COEFF, Self::MAX_EXP);

    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self::new(Self::MIN_COEFF, Self::MAX_EXP);

    /// The smallest positive value that can be represented by
    /// this type.
    pub const MIN_POSITIVE: Self = Self::new(Self::MAX_COEFF, Self::MIN_EXP);

    /// The largest allowed coefficient.
    pub const MAX_COEFF: i128 = 10i128.pow(34) - 1;

    /// The smallestallowed coefficient.
    pub const MIN_COEFF: i128 = -Self::MAX_COEFF;

    /// The maximum allowed exponent.
    pub const MAX_EXP: i16 = Self::EMAX - Self::MAX_PREC + 1;

    /// The smallest allowed exponent.
    pub const MIN_EXP: i16 = Self::EMIN - Self::MAX_PREC + 1;

    /// The number of base 10 significant digits.
    pub const DIGITS: u32 = 34;

    /// Not a Number (NaN).
    ///
    /// # Note
    ///
    /// Do not use this constant to determine whether a number is
    /// NaN. Use [`is_nan`][Self::is_nan] instead.
    pub const NAN: Self = Self::nan(false);

    /// Infinity (∞).
    ///
    /// # Note
    ///
    /// Do not use this constant to determine whether a number is
    /// infinity. Use [`is_infinite`][Self::is_infinite] instead.
    pub const INFINITY: Self = Self::inf(false);

    /// Negative infinity (−∞).
    ///
    /// # Note
    ///
    /// Do not use this constant to determine whether a number is
    /// infinity. Use [`is_infinite`][Self::is_infinite] instead.
    pub const NEG_INFINITY: Self = Self::inf(true);

    /// Reports whether the number is neither infinite nor NaN.
    pub const fn is_finite(self) -> bool {
        !self.is_special()
    }

    /// Reports whether the number is infinite or NaN.
    const fn is_special(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN.
        self.0 & Self::COMB_TOP4 == Self::COMB_TOP4
    }

    /// Reports whether the number is a NaN.
    pub const fn is_nan(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN. The fifth bit signals NaN.
        self.0 & Self::COMB_TOP5 == Self::COMB_TOP5
    }

    /// Reports whether the number is a quiet NaN.
    pub const fn is_qnan(self) -> bool {
        // When the number is a NaN, the sixth combination bit
        // signals whether the NaN is signaling.
        self.0 & Self::COMB_TOP6 == Self::COMB_TOP5
    }

    /// Reports whether the number is a signaling NaN.
    pub const fn is_snan(self) -> bool {
        // When the number is a NaN, the sixth combination bit
        // signals whether the NaN is signaling.
        self.0 & Self::COMB_TOP6 == Self::COMB_TOP6
    }

    /// Reports whether the number is either positive or negative
    /// infinity.
    pub const fn is_infinite(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN. The fifth bit signals NaN.
        self.0 & Self::COMB_TOP5 == Self::COMB_TOP4
    }

    /// Reports whether the number is neither zero, infinite,
    /// subnormal, or NaN.
    pub const fn is_normal(self) -> bool {
        if self.is_special() || self.is_zero() {
            return false;
        }
        debug_assert!(self.is_finite());

        self.adjusted_exp() > Self::EMIN
    }

    /// Reports whether the number is subnormal.
    pub const fn is_subnormal(self) -> bool {
        if self.is_special() || self.is_zero() {
            return false;
        }
        debug_assert!(self.is_finite());

        self.adjusted_exp() <= Self::EMIN
    }

    /// Reports whether the number is positive, including `+0.0`.
    pub const fn is_sign_positive(self) -> bool {
        !self.is_sign_negative()
    }

    /// Reports whether the number is negative, including `-0.0`.
    pub const fn is_sign_negative(self) -> bool {
        self.signbit()
    }

    /// Reports whether the number is `-0.0` or `+0.0`.
    pub const fn is_zero(self) -> bool {
        // Covers the coefficient and form one.
        const MASK1: u128 = (0x7 << Bid128::COMB_SHIFT) | Bid128::COEFF_MASK;
        // Covers form two and specials.
        const MASK2: u128 = 0x18 << Bid128::COMB_SHIFT;
        (self.0 & MASK1) == 0 && (self.0 & MASK2) != MASK2
    }

    /// Returns the floating point category for the number.
    pub const fn classify(self) -> FpCategory {
        // TODO(eric): Optimize this.
        if self.is_nan() {
            FpCategory::Nan
        } else if self.is_infinite() {
            FpCategory::Infinite
        } else if self.is_zero() {
            FpCategory::Zero
        } else if self.is_normal() {
            FpCategory::Normal
        } else {
            FpCategory::Subnormal
        }
    }

    /// Returns the number of significant digits in the number.
    ///
    /// If the number is infinity or zero, it returns 1.
    ///
    /// The result will always be in [1,
    /// [`DIGITS`][Self::DIGITS]].
    ///
    /// TODO: NaN should return the number of digits in the
    /// payload.
    pub const fn digits(self) -> u32 {
        if self.is_infinite() {
            1
        } else {
            arith113::digits(self.coeff())
        }
    }

    /// Returns the unbiased exponent.
    ///
    /// If the number is infinite or NaN, it returns `None`.
    pub const fn exp(self) -> Option<i16> {
        if self.is_finite() {
            Some(self.unbiased_exp())
        } else {
            None
        }
    }

    /// Reports whether `self == other`.
    ///
    /// - If either number is NaN, it returns `false`.
    /// - +0.0 and -0.0 are considered equal.
    ///
    /// This is a const version of [`PartialEq`].
    pub fn const_eq(self, other: Self) -> bool {
        if cfg!(debug_assertions) {
            println!("const_eq({self}, {other})");
        }
        if self.is_nan() || other.is_nan() {
            // NaN != NaN
            return false;
        }
        // Neither are NaN.

        if self.to_bits() == other.to_bits() {
            // Obvious case: same bits.
            return true;
        }
        // Bits differ.

        if self.signbit() ^ other.signbit() {
            // +0 == -0
            // -0 == +0
            // +x != -y
            // -x != +y
            return self.is_zero() && other.is_zero();
        }
        // Signs are the same.
        debug_assert!(self.signbit() == other.signbit());

        if self.is_infinite() && other.is_infinite() {
            // +inf == -inf
            // -inf == +inf
            return true;
        }
        // Both are finite.
        debug_assert!(self.is_finite() && other.is_finite());

        if self.is_zero() || other.is_zero() {
            // +0 == -0
            // -0 == +0
            return self.is_zero() && other.is_zero();
        }
        // Both are non-zero.
        debug_assert!(!self.is_zero() && !other.is_zero());

        if cfg!(debug_assertions) {
            println!("lhs = {self}");
            println!("rhs = {other}");
        }

        // Bias doesn't matter for this comparison.
        let shift = self.biased_exp().abs_diff(other.biased_exp()) as u32;
        if shift >= Self::DIGITS {
            // The shift is larger than the maximum precision, so
            // the coefficients do not overlap.
            return false;
        }
        // `shift` is in [0, DIGITS].

        // Align the coefficients. For example:
        //
        // 123.40 // coeff = 12340, exp = -2
        // 123.4  // coeff = 1234, exp = -1
        //
        // 12340 // coeff = 12340, exp = 0
        // 1234  // coeff = 1234, exp = 1

        if cfg!(debug_assertions) {
            println!(
                "shift = {}",
                self.biased_exp() as i16 - other.biased_exp() as i16,
            );

            println!("lhs = {self}");
            println!("rhs = {other}");
        }

        let mut lhs = self.coeff();
        let mut rhs = other.coeff();
        if self.biased_exp() > other.biased_exp() {
            lhs = arith113::shl(lhs, shift);
        } else if self.biased_exp() < other.biased_exp() {
            rhs = arith113::shl(rhs, shift);
        }
        lhs == rhs
    }

    /// Returns the ordering between `self` and `other`.
    ///
    /// - If either number is NaN, it returns `None`.
    /// - +0.0 and -0.0 are considered equal.
    ///
    /// This is a const version of [`PartialOrd`].
    pub fn const_partial_cmp(self, other: Self) -> Option<Ordering> {
        if cfg!(debug_assertions) {
            println!("partial_cmp({self}, {other})");
        }
        if self.is_nan() || other.is_nan() {
            // NaN != NaN
            return None;
        }
        // Neither are NaN.

        if self.signbit() ^ other.signbit() {
            return if self.is_zero() && other.is_zero() {
                Some(Ordering::Equal) // 0 == 0
            } else if self.signbit() {
                Some(Ordering::Less) // -x < +x
            } else {
                Some(Ordering::Greater) // +x > -x
            };
        }
        // Signs are the same.

        if self.is_infinite() && other.is_infinite() {
            // +inf cmp +inf
            // -inf cmp -inf
            return Some(Ordering::Equal);
        }
        // Both are finite.
        debug_assert!(self.is_finite() && other.is_finite());

        if self.is_zero() || other.is_zero() {
            if cfg!(debug_assertions) {
                println!("lhs is zero = {}", self.is_zero());
                println!("rhs is zero = {}", other.is_zero());
            }
            return if !self.is_zero() {
                Some(Ordering::Greater) // x > 0
            } else if !other.is_zero() {
                Some(Ordering::Less) // 0 < x
            } else {
                Some(Ordering::Equal) // 0 == 0
            };
        }
        // Both are non-zero.
        debug_assert!(!self.is_zero() && !other.is_zero());

        // Bias doesn't matter for this comparison.
        let shift = self.biased_exp() as i16 - other.biased_exp() as i16;
        if shift.unsigned_abs() as u32 > Self::DIGITS {
            // The shift is larger than the maximum precision, so
            // the coefficients do not overlap. Therefore, the
            // larger exponent is the larger number.
            return if shift < 0 {
                Some(Ordering::Less)
            } else {
                Some(Ordering::Greater)
            };
        }
        // `shift` is in [0, DIGITS].

        if cfg!(debug_assertions) {
            println!("lhs exp = {}", self.biased_exp());
            println!("rhs exp = {}", other.biased_exp());
            println!("shift = {shift}");
        }

        let mut lhs = self.coeff();
        let mut rhs = other.coeff();
        if cfg!(debug_assertions) {
            println!("lhs = {lhs} ({self})");
            println!("rhs = {rhs} ({other})");
        }
        if shift > 0 {
            lhs = arith113::shl(lhs, shift.unsigned_abs() as u32);
        } else if shift < 0 {
            rhs = arith113::shl(rhs, shift.unsigned_abs() as u32);
        }
        if cfg!(debug_assertions) {
            println!("lhs = {lhs} ({self})");
            println!("rhs = {rhs} ({other})");
        }
        Some(arith113::const_cmp(lhs, rhs))
    }

    /// Returns the total ordering between `self` and `other`.
    ///
    /// The values are oredered as follows:
    ///
    /// - negative quiet NaN
    /// - negative signaling NaN
    /// - negative infinity
    /// - negative numbers
    /// - negative subnormal numbers
    /// - negative zero
    /// - positive zero
    /// - positive subnormal numbers
    /// - positive numbers
    /// - positive infinity
    /// - positive signaling NaN
    /// - positive quiet NaN
    ///
    /// The ordering established by this function does not always
    /// agree with the [`PartialOrd`] and [`PartialEq`]. For
    /// example, they consider negative and positive zero equal,
    /// while `const_total_cmp` doesn't.
    pub const fn const_total_cmp(self, other: Self) -> Ordering {
        let mut lhs = self.to_bits() as i128;
        let mut rhs = other.to_bits() as i128;

        lhs ^= (((lhs >> 127) as u128) >> 1) as i128;
        rhs ^= (((rhs >> 127) as u128) >> 1) as i128;

        if lhs < rhs {
            Ordering::Less
        } else if lhs > rhs {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

// To/from reprs.
impl Bid128 {
    /// Creates a `d128` from its coefficient and exponent.
    pub const fn new(coeff: i128, exp: i16) -> Self {
        // TODO(eric): the inf probably isn't correct.
        if coeff < Self::MIN_COEFF || exp < Self::MIN_EXP {
            Self::NEG_INFINITY
        } else if coeff > Self::MAX_COEFF || exp > Self::MAX_EXP {
            Self::INFINITY
        } else {
            // We explicitly check `coeff < 0`, so the sign loss
            // is okay.
            //
            // `coeff` is in [MIN_COEFF, MAX_COEFF], which is
            // smaller than [i128::MIN, i128::MAX], so the cast
            // cannot wrap. `u128::unsigned_abs` would be more
            // clear, but it needlessly adds extra instructions.
            #[allow(clippy::cast_sign_loss)]
            Self::from_parts(coeff < 0, exp, coeff as u128)
        }
    }

    /// Creates an infinity.
    const fn inf(sign: bool) -> Self {
        let bits = signbit(sign) | comb(0x1e000);
        Self::from_bits(bits)
    }

    /// Creates a quiet NaN.
    const fn nan(sign: bool) -> Self {
        let bits = signbit(sign) | comb(0x1f000);
        Self::from_bits(bits)
    }

    /// Creates a signaling NaN.
    const fn snan(sign: bool) -> Self {
        let bits = signbit(sign) | comb(0x1f800);
        Self::from_bits(bits)
    }

    /// Creates a `d128` from its raw bits.
    ///
    /// ```rust
    /// use decnum::Bid128;
    ///
    /// let got = Bid128::from_bits(0x2207c0000000000000000000000000a5);
    /// let want = "12.5".parse::<d128>().unwrap();
    /// assert_eq!(v, "12.5");
    /// ```
    pub const fn from_bits(bits: u128) -> Self {
        Self(bits)
    }

    /// Creates a `d128` from a little-endian byte array.
    pub const fn from_le_bytes(bytes: [u8; 16]) -> Self {
        Self::from_bits(u128::from_le_bytes(bytes))
    }

    /// Creates a `d128` from a big-endian byte array.
    pub const fn from_be_bytes(bytes: [u8; 16]) -> Self {
        Self::from_bits(u128::from_be_bytes(bytes))
    }

    /// Creates a `d128` from a native-endian byte array.
    pub const fn from_ne_bytes(bytes: [u8; 16]) -> Self {
        Self::from_bits(u128::from_ne_bytes(bytes))
    }

    /// Creates a `d128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        Self::from_u64(coeff as u64)
    }

    /// Creates a `d128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u64(coeff: u64) -> Self {
        Self::from_parts(false, 0, coeff as u128)
    }

    /// Raw transmutation to `u128`.
    pub const fn to_bits(self) -> u128 {
        self.0
    }

    /// Converts the `Bid128` to a `Dpd128`.
    pub const fn to_dpd128(self) -> Dpd128 {
        Dpd128::from_parts_bin(self.signbit(), self.unbiased_exp(), self.coeff())
    }
}

// Const arithmetic.
impl Bid128 {
    /// Returns `self + other`.
    ///
    /// This is the same as [`Add`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_add(self, _rhs: Self) -> Self {
        todo!()
    }

    /// Returns `self * other`.
    ///
    /// This is the same as [`Mul`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_mul(self, _rhs: Self) -> Self {
        todo!()
    }

    /// Returns `-self`.
    ///
    /// This is the same as [`Neg`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_neg(self) -> Self {
        Self(self.0 ^ Self::SIGN_MASK)
    }

    /// Returns `self - other`.
    ///
    /// This is the same as [`Sub`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_sub(self, rhs: Self) -> Self {
        // x - y = x + -y
        self.const_add(rhs.const_neg())
    }
}

// String conversions.
impl Bid128 {
    /// Converts the decimal to a string.
    #[allow(clippy::indexing_slicing)]
    pub fn format(self, dst: &mut Buffer) -> &str {
        let dst = &mut dst.buf;

        if self.is_special() {
            let start = usize::from(self.is_sign_positive());
            return if self.is_infinite() {
                &"-Infinity"[start..]
            } else if self.is_qnan() {
                &"-NaN"[start..]
            } else {
                &"-sNaN"[start..]
            };
        }
        debug_assert!(self.is_finite());

        let exp = i32::from(self.unbiased_exp());

        let mut tmp = itoa::Buffer::new();
        let coeff = tmp.format(self.coeff()).as_bytes();
        // SAFETY: `coeff_to_str` writes [1, DIGITS] to `tmp`
        // returns a subslice of `tmp`, so the length of `coeff`
        // must be in [1, DIGITS].
        unsafe {
            assume(!coeff.is_empty());
            assume(coeff.len() <= Self::DIGITS as usize);
        }

        // `e` is the adjusted exponent.
        // `pre` is the number of digits before the '.'.
        let (e, pre) = {
            let mut e = 0;
            #[allow(clippy::cast_possible_wrap)]
            let mut pre = (coeff.len() as i32) + exp;
            if exp > 0 || pre < -5 {
                // Exponential form
                e = pre - 1;
                pre = 1;
            }
            // SAFETY:
            //
            // Because `coeff.len()` is in [1, DIGITS] and `exp`
            // is in [MIN_EXP, MAX_EXP], `pre` is initially in
            // [1+MIN_EXP, DIGITS+MAX_EXP]. After adjustment into
            // exponential form, `pre` is in [min(1, -5),
            // DIGITS+MAX_EXP].
            unsafe {
                assume(pre >= -5);
                assume(pre <= (Self::DIGITS + Self::MAX_EXP as u32) as i32);
            }
            (e, pre)
        };

        if pre > 0 {
            // SAFETY: `pre` was in [min(1, -5), DIGITS+MAX_EXP].
            // This block is predicated on `pre > 0`, so `pre` is
            // now in [1, DIGITS+MAX_EXP].
            unsafe {
                assume(pre <= (Self::DIGITS + Self::MAX_EXP as u32) as i32);
            }

            let pre = pre.unsigned_abs() as usize;

            let mut i = 1;
            dst[0].write(b'-');

            if pre < coeff.len() {
                let (pre, post) = coeff.split_at(pre);
                copy_from_slice(&mut dst[i..i + pre.len()], pre);
                dst[i + pre.len()].write(b'.');
                copy_from_slice(
                    &mut dst[i + pre.len() + 1..i + pre.len() + 1 + post.len()],
                    post,
                );
                i += 1;
            } else {
                copy_from_slice(&mut dst[i..i + coeff.len()], coeff);
            };
            i += coeff.len();

            //println!("e={e}");
            if e != 0 {
                dst[i].write(b'E');
                i += 1;
                if e < 0 {
                    dst[i].write(b'-');
                } else {
                    dst[i].write(b'+');
                };
                i += 1;

                //println!("i={i}");

                // `e` is either 0 or `pre-1`. Since `pre` is in
                // [1, DIGITS+MAX_EXP] and DIGITS+MAX_EXP <=
                // u16::MAX, the cast cannot wrap.
                const_assert!((Bid128::DIGITS + Bid128::MAX_EXP as u32) < u16::MAX as u32);
                let s = util::itoa4(e.unsigned_abs() as u16);
                copy_from_slice(&mut dst[i..i + 4], &s.to_bytes());
                i += s.digits();
            }

            let start = usize::from(self.is_sign_positive());
            //println!("start={start} i={i} len={}", dst.len());
            // SAFETY: `buf` only ever contains UTF-8.
            return unsafe { str::from_utf8_unchecked(slice_assume_init_ref(&dst[start..i])) };
        }

        // SAFETY: TODO
        unsafe {
            assume(pre >= -5);
            assume(pre <= 0);
        }

        // -5 => 7
        // -4 => 6
        // -3 => 5
        // -2 => 4
        // -1 => 3
        //  0 => 2
        let pre = 2 + pre.unsigned_abs() as usize;
        // SAFETY: `pre` was in [-5, 0]. After negation and
        // adding 2, `pre` is now in [2, 7].
        unsafe {
            assume(pre >= 2);
            assume(pre <= 7);
        }
        const_assert!(1 + 7 + Bid128::DIGITS as usize <= Buffer::len());

        copy(dst, b"-0.00000");
        let mut i = 1 + pre;
        // SAFETY: `pre` was in [-5, 0]. After negation and
        // adding 2, `pre` is now in [2, 7]. `coeff` is in [1,
        // DIGITS], so `i+pre+coeff.len()` is in [1+2+DIGITS,
        // 1+7+DIGITS].
        // let tmp = unsafe { dst.get_unchecked_mut(i..i + coeff.len()) };
        // tmp.copy_from_slice(coeff);
        let (_, rest) = dst.split_at_mut(i);
        copy_from_slice(&mut rest[..coeff.len()], coeff);
        i += coeff.len();

        let start = usize::from(self.is_sign_positive());
        // SAFETY: `buf` only ever contains UTF-8.
        return unsafe { str::from_utf8_unchecked(slice_assume_init_ref(&dst[start..i])) };
    }

    /// Parses a decimal from a string.
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        let mut s = s.as_bytes();
        if s.is_empty() {
            return Err(ParseError::empty());
        }

        let mut sign = false;
        if let Some((c @ (b'-' | b'+'), rest)) = s.split_first() {
            sign = *c == b'-';
            s = rest;
        }

        match s.first() {
            Some(b'0'..=b'9') => {}
            Some(b'i' | b'I' | b'n' | b'N' | b's' | b'S') => return Self::parse_special(sign, s),
            Some(_) => return Err(ParseError::invalid("expected digit or special")),
            None => return Err(ParseError::invalid("unexpected end of input")),
        }

        let (coeff, sd, s) = match Self::parse_coeff(s) {
            Ok((c, e, r)) => (c, e, r),
            Err(err) => return Err(err),
        };
        if cfg!(debug_assertions) {
            println!("coeff = {coeff}");
            println!("  dot = {sd:?}");
            println!("    s = \"{}\"", str::from_utf8(s).unwrap());
        }
        let exp = match Self::parse_exp(s) {
            // If the decimal-part included a decimal point the
            // exponent is then reduced by the count of digits
            // following the decimal point (which may be zero)
            // and the decimal point is removed.
            //
            // https://speleotrove.com/decimal/daconvs.html#reftonum
            Ok(exp) => exp - sd as i16,
            Err(err) => return Err(err),
        };
        if cfg!(debug_assertions) {
            println!("  exp = {exp}");
        }

        Ok(Self::from_parts(sign, exp, coeff))
    }

    /// Parses the coefficient.
    ///
    /// It returns the coefficient, number of digits after the
    /// decimal point, and unused remainder of the input.
    fn parse_coeff(s: &[u8]) -> Result<(u128, usize, &[u8]), ParseError> {
        debug_assert!(!s.is_empty());

        if cfg!(debug_assertions) {
            println!("parse_coeff = {}", str::from_utf8(s).unwrap());
        }

        let (pre, rest, coeff) = conv::parse_digits_u128(s, 0);
        let (post, rest, coeff): (&[u8], &[u8], u128) =
            if let Some((&b'.', rest)) = rest.split_first() {
                conv::parse_digits_u128(rest, coeff)
            } else {
                (&[], rest, coeff)
            };

        // `rest` should not start with a digit.
        debug_assert!(!matches!(rest.first(), Some(&(b'0'..=b'9'))));

        if cfg!(debug_assertions) {
            println!(" pre = {pre:?} {}", str::from_utf8(pre).unwrap());
            println!("post = {post:?} {}", str::from_utf8(post).unwrap());
            println!("rest = {rest:?} {}", str::from_utf8(rest).unwrap());
        }

        // Number of significant digits. Make sure to collect
        // this before we start trimming zeros.
        let sd = post.len();

        let mut digits = pre.len() + post.len();
        if digits > Self::DIGITS as usize {
            // Uncommon case: too many digits to know whether
            // `coeff` overflowed. Maybe we have leading zeros?
            let mut tmp = match s.split_at_checked(digits) {
                Some((s, _)) => s,
                // NB: This case is impossible since
                //   s = pre || post || rest
                //   s = pre || '.' || post || rest
                // but the compiler doesn't understand this.
                None => &[],
            };
            while let Some(((b'0'..=b'9') | b'.', rest)) = tmp.split_first() {
                digits -= 1;
                tmp = rest;
            }
        }

        // Common case fast path: we had a reasonable number of
        // digits.
        if digits <= Self::DIGITS as usize {
            return Ok((coeff, sd, rest));
        }

        // Slow path: we have more than 32 digits, so `lo` has
        // overflown.
        let coeff = Self::parse_large_coeff(pre, post);
        Ok((coeff, sd, rest))
    }

    /// Parses a coefficient with too many digits.
    ///
    /// - `pre` is the coefficient before the dot.
    /// - `post` is the coefficient after the dot.
    ///
    /// The coefficient does not have any leading zeros.
    #[cold]
    const fn parse_large_coeff<'a>(mut pre: &'a [u8], mut post: &'a [u8]) -> u128 {
        debug_assert!(pre.len() + post.len() > Self::DIGITS as usize);
        util::debug_assert_all_digits(pre);
        util::debug_assert_all_digits(post);

        // Partition (pre, post) into (pre, post, extra)
        // where `pre || post` is at most 34 digits.

        let mut coeff = 0;
        let mut nd = 0; // number of digits.
        let mut lsd = 0; // least significant digits
        while let Some((&c, rest)) = pre.split_first() {
            if nd >= Self::DIGITS {
                break;
            }
            let d = (c - b'0') as u128;
            lsd = d;
            coeff = coeff * 10 + d;
            pre = rest;
            nd += 1;
        }
        while let Some((&c, rest)) = post.split_first() {
            if nd >= Self::DIGITS {
                break;
            }
            let d = (c - b'0') as u128;
            lsd = d;
            coeff = coeff * 10 + d;
            post = rest;
            nd += 1;
        }

        // `coeff` is now exactly 34 digits. Use the next digit
        // for rounding.
        let d = match (pre, post) {
            ([d, ..], _) | ([], [d, ..]) => *d - b'0',
            _ => {
                todo!()
            }
        };
        if d > 5 || (d == 5 && (lsd % 2 != 0)) {
            // Round up if d>5 or the new LSD is odd.
            coeff += 1;
        }

        coeff
    }

    fn parse_exp(mut s: &[u8]) -> Result<i16, ParseError> {
        if cfg!(debug_assertions) {
            println!("parse_exp: {}", str::from_utf8(s).unwrap());
        }
        if s.is_empty() {
            return Ok(0);
        }

        if let Some((b'e' | b'E', rest)) = s.split_first() {
            s = rest;
        } else {
            return Err(ParseError::invalid("expected `e` or `E`"));
        }

        let mut sign = false;
        if let Some((c @ (b'-' | b'+'), rest)) = s.split_first() {
            sign = *c == b'-';
            s = rest;
        }

        let mut exp: i16 = 0;
        while let Some((&c, rest)) = s.split_first() {
            let d = c.wrapping_sub(b'0');
            if d >= 10 {
                return Err(ParseError::invalid("expected digit"));
            }
            exp = match exp.checked_mul(10) {
                Some(exp) => exp,
                None => return Err(ParseError::invalid("exp overflow")),
            };
            exp = match exp.checked_add(d as i16) {
                Some(exp) => exp,
                None => return Err(ParseError::invalid("exp overflow")),
            };
            s = rest;
        }
        if sign {
            exp = -exp;
        }
        if cfg!(debug_assertions) {
            println!("exp = {exp} sign = {sign}");
        }
        Ok(exp)
    }

    const fn parse_special(sign: bool, s: &[u8]) -> Result<Self, ParseError> {
        if conv::equal_fold(s, b"inf") || conv::equal_fold(s, b"infinity") {
            Ok(Self::inf(sign))
        } else if conv::equal_fold(s, b"nan") || conv::equal_fold(s, b"qnan") {
            Ok(Self::nan(sign))
        } else if conv::equal_fold(s, b"snan") {
            Ok(Self::snan(sign))
        } else {
            Err(ParseError::invalid("unknown special"))
        }
    }
}

impl Add for Bid128 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.const_add(rhs)
    }
}

impl AddAssign for Bid128 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for Bid128 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.const_mul(rhs)
    }
}

impl MulAssign for Bid128 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for Bid128 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.const_neg()
    }
}

impl Sub for Bid128 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.const_sub(rhs)
    }
}

impl SubAssign for Bid128 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl PartialEq for Bid128 {
    fn eq(&self, other: &Self) -> bool {
        self.const_eq(*other)
    }
}

impl PartialOrd for Bid128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.const_partial_cmp(*other)
    }
}

impl FromStr for Bid128 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Bid128::parse(s)
    }
}

impl fmt::Display for Bid128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::Default);
        write!(f, "{str}")
    }
}

impl fmt::Binary for Bid128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.to_bits(), f)
    }
}

impl fmt::LowerExp for Bid128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::LowerExp);
        write!(f, "{str}")
    }
}

impl fmt::UpperExp for Bid128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::UpperExp);
        write!(f, "{str}")
    }
}

impl fmt::Debug for Bid128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ">> ")?;

        for word in [
            (self.0 >> 96) as u32,
            (self.0 >> 64) as u32,
            (self.0 >> 32) as u32,
            (self.0 as u32),
        ] {
            let b = word.to_be_bytes();
            for (i, c) in b.iter().enumerate() {
                write!(f, "{c:02x}")?;
                if i == 3 {
                    write!(f, " ")?;
                }
            }
        }
        let b = self.0.to_be_bytes();
        let sign = b[15] >> 7;
        let cb = (b[15] >> 2) & 0x1f;
        let ec = (u16::from(b[15] & 0x3) << 10) | u16::from(b[14] << 2) | u16::from(b[13] >> 6);
        write!(f, " [S:{sign} Cb:{cb:02x} Ec:{ec:02x}]")
    }
}

const fn signbit(sign: bool) -> u128 {
    (sign as u128) << Bid128::SIGN_SHIFT
}

const fn comb(bits: u32) -> u128 {
    debug_assert!(bits & !((1 << Bid128::COMB_BITS) - 1) == 0);

    (bits as u128) << Bid128::COMB_SHIFT
}

/// See [`MaybeUninit::copy_from_slice`].
fn copy_from_slice(dst: &mut [MaybeUninit<u8>], src: &[u8]) {
    // SAFETY: &[T] and &[MaybeUninit<T>] have the same layout
    let uninit_src: &[MaybeUninit<u8>] =
        unsafe { &*(src as *const [u8] as *const [MaybeUninit<u8>]) };
    dst.copy_from_slice(uninit_src);
}

/// See [`MaybeUninit::slice_assume_init_ref`].
const unsafe fn slice_assume_init_ref(slice: &[MaybeUninit<u8>]) -> &[u8] {
    // SAFETY: casting `slice` to a `*const [T]` is safe since
    // the caller guarantees that `slice` is initialized, and
    // `MaybeUninit` is guaranteed to have the same layout as
    // `T`. The pointer obtained is valid since it refers to
    // memory owned by `slice` which is a reference and thus
    // guaranteed to be valid for reads.
    unsafe { &*(slice as *const [MaybeUninit<u8>] as *const [u8]) }
}

#[inline(always)]
fn copy(dst: &mut [MaybeUninit<u8>], src: &[u8]) -> usize {
    let n = src.len();
    // The caller must verify the length of `dst`
    #[allow(clippy::indexing_slicing)]
    copy_from_slice(&mut dst[..n], src);
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "slow-tests")]
    use crate::decnumber::Quad;

    impl Bid128 {
        const SNAN: Self = Self::snan(false);
        const NEG_NAN: Self = Self::nan(true);
        const NEG_SNAN: Self = Self::snan(true);
    }

    #[test]
    fn test_exp() {
        for exp in 0..=Bid128::MAX_EXP {
            let d = Bid128::new(0, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(1) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), 0, "#{exp}");

            let d = Bid128::new(Bid128::MAX_COEFF, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(2) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), Bid128::MAX_COEFF as u128, "#{exp}");
        }
    }

    static STR_TESTS: &[(Bid128, &'static str)] = &[
        (Bid128::NAN, "NaN"),
        (Bid128::NEG_NAN, "-NaN"),
        (Bid128::SNAN, "sNaN"),
        (Bid128::NEG_SNAN, "-sNaN"),
        (Bid128::INFINITY, "Infinity"),
        (Bid128::NEG_INFINITY, "-Infinity"),
        (Bid128::new(0, 0), "0"),
        (Bid128::new(0, -1), "0.0"),
        (Bid128::new(0, Bid128::MAX_EXP), "0E+6111"),
        (Bid128::new(0, Bid128::MIN_EXP), "0E-6176"),
        (Bid128::new(21, -1), "2.1"),
        (Bid128::new(210, -2), "2.10"),
        (
            Bid128::new(9111222333444555666777888999000111, Bid128::MAX_EXP),
            "9.111222333444555666777888999000111E+6144",
        ),
        (
            Bid128::new(9111222333444555666777888999000111, Bid128::MIN_EXP),
            "9.111222333444555666777888999000111E-6143",
        ),
        (
            Bid128::new(9111222333444555666777888999000111, 0),
            "9111222333444555666777888999000111",
        ),
        (
            Bid128::new(9111222333444555666777888999000111, -2),
            "91112223334445556667778889990001.11",
        ),
        (
            Bid128::new(9111222333444555666777888999000111, 2),
            "9.111222333444555666777888999000111E+35",
        ),
        (
            Bid128::new(9999999999999999999999999999999999, -39),
            "0.000009999999999999999999999999999999999",
        ),
        (Bid128::new(42, 1), "4.2E+2"),
        (Bid128::new(42, 0), "42"),
        (Bid128::new(42, -1), "4.2"),
        (Bid128::new(42, -2), "0.42"),
        (Bid128::new(42, -3), "0.042"),
        (Bid128::new(42, -4), "0.0042"),
        (Bid128::new(42, -5), "0.00042"),
        (Bid128::new(42, -6), "0.000042"),
        (Bid128::new(42, -7), "0.0000042"),
        (Bid128::new(42, -8), "4.2E-7"),
    ];

    #[test]
    fn test_format() {
        for (i, (input, want)) in STR_TESTS.iter().enumerate() {
            let got = input.to_string();
            assert_eq!(got, *want, "#{i}");
        }
    }

    #[test]
    fn test_parse() {
        for (i, &(want, output)) in STR_TESTS.iter().enumerate() {
            let got: Bid128 = output.parse().unwrap();
            if want.is_nan() {
                assert!(got.is_nan(), "#{i}: parse(\"{output}\") -> {want}");
            } else {
                assert_eq!(got, want, "#{i}: parse(\"{output}\") -> {want}");
            }
            println!("");
        }
    }

    // NB: This takes ~3.5 minutes on an Apple M1.
    #[test]
    #[cfg(feature = "slow-tests")]
    fn test_from_u32() {
        for x in 0..=u32::MAX {
            let got = Bid128::from_u32(x);
            let want = Quad::from_u32(x);
            assert_eq!(got, want, "#{x}");
        }
    }

    #[test]
    fn test_digits() {
        for i in 1..Bid128::DIGITS {
            let v = 10i128.pow(i);
            let got = Bid128::new(v - 1, 0).digits();
            let want = v.ilog10();
            assert_eq!(got, want, "#{}", v - 1);
        }
    }

    #[test]
    fn test_partial_cmp() {
        let tests = [
            // ("NaN", "3", None),
            // ("3", "NaN", None),
            ("2.1", "3", Some(Ordering::Less)),
            ("2.1", "2.1", Some(Ordering::Equal)),
            ("2.1", "2.10", Some(Ordering::Equal)),
            ("3", "2.1", Some(Ordering::Greater)),
            ("2.1", "-3", Some(Ordering::Greater)),
            ("-3", "2.1", Some(Ordering::Less)),
        ];
        for (i, (lhs, rhs, want)) in tests.into_iter().enumerate() {
            println!("lhs={lhs} rhs={rhs}");
            let x: Bid128 = lhs.parse().unwrap();
            let y: Bid128 = rhs.parse().unwrap();
            println!("x={x} y={y}");
            let got = PartialOrd::partial_cmp(&x, &y);
            assert_eq!(got, want, "#{i}: partial_cmp({lhs}, {rhs})");
            assert_eq!(
                x.const_partial_cmp(y),
                want,
                "#{i}: const_partial_cmp({lhs}, {rhs})"
            );
            println!("");
        }
    }

    #[test]
    fn test_shift() {
        let lhs = Bid128::new(1230, -1);
        let rhs = Bid128::new(12300, -2);
        println!("lhs = {lhs} {}", lhs.unbiased_exp());
        println!("rhs = {rhs} {}", rhs.unbiased_exp());
    }
}
