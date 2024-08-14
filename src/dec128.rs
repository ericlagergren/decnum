use core::{
    cmp::Ordering,
    fmt,
    mem::{self, size_of, MaybeUninit},
    num::FpCategory,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::{self, FromStr},
};

use super::{
    bcd::Str3,
    conv::{self, Buffer, Fmt, ParseError},
    dpd,
    util::{self, assume, const_assert},
};

/// A 128-bit decimal floating point number.
///
/// TODO: docs
#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct d128(
    /// # Layout
    ///
    /// ## Bits
    ///
    /// 0: sign
    /// 1-5: combination
    /// 6-17: exponent continuation
    /// 17-127: coefficient continuation
    u128,
);
const_assert!(size_of::<d128>() == 128 / 8);

// Internal stuff.
impl d128 {
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

    #[allow(dead_code)] // TODO
    const SIGN_BIT: u32 = 1;
    const SIGN_SHIFT: u32 = 128 - 1;
    const SIGN_MASK: u128 = 1 << Self::SIGN_SHIFT;

    const COMB_BITS: u32 = 5;
    const COMB_SHIFT: u32 = 128 - 1 - 5;
    const COMB_MASK: u128 = 0x1f << Self::COMB_SHIFT;

    const ECON_BITS: u32 = 12;
    const ECON_SHIFT: u32 = 128 - 1 - 5 - 12;
    const ECON_MASK: u128 = 0xfff << Self::ECON_SHIFT;

    const COEFF_BITS: u32 = 110;
    const COEFF_MASK: u128 = (1 << 110) - 1;

    const fn signbit(self) -> bool {
        (self.0 & Self::SIGN_MASK) != 0
    }

    /// Returns the combination field.
    const fn comb(self) -> Comb {
        let comb = (self.0 & Self::COMB_MASK) >> Self::COMB_SHIFT;
        Comb(comb as u8)
    }

    /// Returns the coefficient MSD.
    const fn msd(self) -> u8 {
        self.comb().msd()
    }

    /// Reports whether the MSD is non-zero.
    const fn have_msd(self) -> bool {
        self.comb().have_msd()
    }

    /// Returns the exponent continuation field.
    ///
    /// The top four bits are always zero, so the result is
    /// always in [0, 4095].
    const fn econ(self) -> u16 {
        let econ = ((self.0 & Self::ECON_MASK) >> Self::ECON_SHIFT) as u16;
        // SAFETY: Given our mask and shift, the top four bits
        // are always zero.
        unsafe {
            assume(econ & 0xf000 == 0);
        }
        econ
    }

    /// Returns the biased exponment.
    ///
    /// If the number is finite, the result is in [0,
    /// [`LIMIT`][Self::LIMIT]].
    const fn exp(self) -> u16 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let econ = self.econ();
        let msb = self.comb().msb() as u16;
        let exp = (msb << 12) | econ;

        if self.is_finite() {
            const_assert!(d128::LIMIT < (1 << 14) - 1);

            // SAFETY: `exp` is a 14 bit integer: `econ` is
            // the lower 12 bits and `msb` is the upper 2 bits.
            // Since `msb` is in [0, 2], the maximum value is
            //   0b10_111111111111
            //    msb      econ
            // which is the same as LIMIT.
            unsafe {
                assume(msb <= 2);
                assume(exp <= Self::LIMIT);
            }
        }
        exp
    }

    /// Returns the unbiased exponent.
    ///
    /// If the number is finite, the result is in
    /// [[`MIN_EXP`][Self::MIN_EXP], [`MAX_EXP`][Self::MAX_EXP]].
    const fn unbiased_exp(self) -> i16 {
        const_assert!(d128::LIMIT < i16::MAX as u16);
        const_assert!(i16::MAX - (d128::LIMIT as i16) > d128::BIAS);

        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        // `self.exp()` is in [0, LIMIT] and LIMIT < i16::MAX, so
        // the cast cannot wrap.
        //
        // The subtraction cannot wrap since
        //    LIMIT + BIAS < i16::MAX
        //    0 - BIAS > i16::MIN
        #[allow(clippy::cast_possible_wrap)]
        let exp = (self.exp() as i16) - Self::BIAS;

        if self.is_finite() {
            // SAFETY: `self.exp()` returns an integer in
            // [0, LIMIT]. Subtracting `BIAS` TODO
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
        const_assert!(d128::DIGITS <= i16::MAX as u32);

        debug_assert!(self.is_finite());

        // `self.digits() as i16` does not wrap because it is in
        // [1, DIGITS], and `DIGITS <= i16::MAX`.
        #[allow(clippy::cast_possible_wrap)]
        let digits = self.digits() as i16;

        self.unbiased_exp() + digits - 1
    }

    /// Returns the coefficient, less the MSD, as a DPD.
    const fn coeff(self) -> u128 {
        debug_assert!(self.is_finite());

        self.0 & Self::COEFF_MASK
    }

    /// Returns the coefficient, including the MSD, as a DPD.
    #[allow(dead_code)] // TODO
    const fn full_coeff(self) -> u128 {
        self.coeff() | ((self.msd() as u128) << 110)
    }

    const fn from_parts(sign: bool, exp: i16, coeff: u128) -> Self {
        debug_assert!(exp >= Self::MIN_EXP);
        debug_assert!(exp <= Self::MAX_EXP);
        debug_assert!(coeff <= Self::MAX_COEFF as u128);

        let dpd = dpd::pack_bin_u113(coeff);
        // TODO(eric): If `exp` is valid then this cannot
        // overflow. Maybe make sure of it?
        #[allow(clippy::cast_sign_loss)]
        let biased = (exp + Self::BIAS) as u128;

        let comb = {
            // `dpd` is 120 bits. The top 6 bits are always zero.
            // The next 4 bits contain the MSD.
            let msd = ((dpd >> 110) & 0x9) as u8;
            debug_assert!(msd <= 9);

            let msb = ((biased & 0x3000) >> 12) as u8;
            debug_assert!(msb <= 2);

            // [0,7] -> 0cde
            // [8,9] -> 100e
            if msd <= 7 {
                (msb << 3) | msd
            } else {
                0x18 | (msb << 1) | msd
            }
        };
        let econ = (biased & 0xfff) as u16;
        let coeff = dpd & Self::COEFF_MASK;

        Self::from_fields(sign, comb, econ, coeff)
    }

    const fn from_fields(sign: bool, comb: u8, econ: u16, coeff: u128) -> Self {
        debug_assert!(comb & !((1 << Self::COMB_BITS) - 1) == 0);
        debug_assert!(econ & !((1 << Self::ECON_BITS) - 1) == 0);
        debug_assert!(coeff & !Self::COEFF_MASK == 0);

        let mut bits = 0;
        bits |= (sign as u128) << Self::SIGN_SHIFT;
        bits |= (comb as u128) << Self::COMB_SHIFT;
        bits |= (econ as u128) << Self::ECON_SHIFT;
        bits |= coeff;
        Self(bits)
    }
}

// Public stuff.
impl d128 {
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
    pub const NAN: Self = Self::nan(false);

    /// Infinity (∞).
    pub const INFINITY: Self = Self::inf(false);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self::inf(true);

    /// Reports whether the number is neither infinite nor NaN.
    pub const fn is_finite(self) -> bool {
        self.comb().is_finite()
    }

    /// Reports whether the number is either positive or negative
    /// infinity.
    pub const fn is_infinite(self) -> bool {
        self.comb().is_infinite()
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

    /// Reports whether the number is `-0.0` or `+0.0`.
    pub const fn is_zero(self) -> bool {
        // Covers the coefficient and MSD <= 7.
        const MASK1: u128 = (0x7 << d128::COMB_SHIFT) | d128::COEFF_MASK;
        // Covers MSD > 7 and specials.
        const MASK2: u128 = 0x18 << d128::COMB_SHIFT;
        (self.0 & MASK1) == 0 && (self.0 & MASK2) != MASK2
    }

    /// Reports whether the number is a NaN.
    pub const fn is_nan(self) -> bool {
        self.comb().is_nan()
    }

    /// Reports whether the number is a quiet NaN.
    pub const fn is_qnan(self) -> bool {
        // When the number is a NaN, the first exponent
        // continuation bit signals whether the NaN is signaling.
        self.is_nan() && self.econ() >> (Self::ECON_BITS - 1) == 0
    }

    /// Reports whether the number is a signaling NaN.
    pub const fn is_snan(self) -> bool {
        // When the number is a NaN, the first exponent
        // continuation bit signals whether the NaN is signaling.
        self.is_nan() && self.econ() >> (Self::ECON_BITS - 1) == 1
    }

    /// Reports whether the number is positive, including `+0.0`.
    pub const fn is_sign_positive(self) -> bool {
        !self.is_sign_negative()
    }

    /// Reports whether the number is negative, including `-0.0`.
    pub const fn is_sign_negative(self) -> bool {
        self.signbit()
    }

    /// Reports whether the number is infinite or NaN.
    const fn is_special(self) -> bool {
        self.comb().is_special()
    }

    /// Returns the floating point category for the number.
    pub const fn classify(self) -> FpCategory {
        let comb = (self.0 & Self::COMB_MASK) >> Self::COMB_SHIFT;
        match comb & 0x1f {
            0x1f => return FpCategory::Nan,
            0x1e => return FpCategory::Infinite,
            _ => {}
        }
        debug_assert!(self.is_finite());

        if self.is_zero() {
            return FpCategory::Zero;
        }

        if self.adjusted_exp() > Self::EMIN {
            FpCategory::Normal
        } else {
            FpCategory::Subnormal
        }

        // if self.is_nan() {
        //     FpCategory::Nan
        // } else if self.is_infinite() {
        //     FpCategory::Infinite
        // } else if self.is_zero() {
        //     FpCategory::Zero
        // } else if self.is_normal() {
        //     FpCategory::Normal
        // } else {
        //     FpCategory::Subnormal
        // }
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
            return 1;
        }
        if self.have_msd() {
            return Self::DIGITS;
        }
        let coeff = self.coeff();
        // The number of whole declets.
        let declets = (128 - coeff.leading_zeros()) / 10;
        // Shift off the whole declets to figure out how many
        // significant digits are in the partial declet.
        let dpd = ((coeff >> (declets * 10)) & 0x3ff) as u16;
        dpd::sig_digits(dpd) + (declets * 3)
    }

    /// Reports whether `self == other`.
    ///
    /// - If either number is NaN, it returns `false`.
    /// - +0.0 and -0.0 are considered equal.
    ///
    /// This is a const version of [`PartialEq`].
    pub const fn const_eq(self, other: Self) -> bool {
        if self.comb().0 != other.comb().0 || self.is_nan() || other.is_nan() {
            return false;
        }
        if self.signbit() ^ other.signbit() {
            return false;
        }
        if self.exp() == other.exp() {
            // let lhs = self.coeff();
            // let rhs = other.coeff();
            todo!()
        }
        true
    }

    /// Returns the ordering between `self` and `other`.
    ///
    /// - If either number is NaN, it returns `None`.
    /// - +0.0 and -0.0 are considered equal.
    ///
    /// This is a const version of [`PartialOrd`].
    #[no_mangle]
    pub const fn const_partial_cmp(self, other: Self) -> Option<Ordering> {
        if self.is_nan() || other.is_nan() {
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
            return if self.is_zero() {
                Some(Ordering::Less) // 0 < x
            } else {
                Some(Ordering::Greater) // x > 0
            };
        }
        // Both are non-zero.
        debug_assert!(!self.is_zero() && !other.is_zero());

        // Bias doesn't matter for this comparison.
        let shift = self.exp() as i16 - other.exp() as i16;
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

        let mut lhs = self.full_coeff();
        let mut rhs = other.full_coeff();
        if shift == 0 {
            return Some(dpd::cmp120(lhs, rhs));
        }

        None
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
    #[no_mangle]
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
impl d128 {
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
            // cannot wrap.
            #[allow(clippy::cast_sign_loss)]
            Self::from_parts(coeff < 0, exp, coeff as u128)
        }
    }

    /// Creates a quiet NaN.
    const fn nan(sign: bool) -> Self {
        Self::from_fields(sign, 0x1f, 0, 0)
    }

    /// Creates a signaling NaN.
    const fn snan(sign: bool) -> Self {
        Self::from_fields(sign, 0x1f, 0x800, 0)
    }

    /// Creates an infinity.
    const fn inf(sign: bool) -> Self {
        Self::from_fields(sign, 0x1e, 0, 0)
    }

    /// Creates a `d128` from its raw bits.
    ///
    /// ```rust
    /// use decnum::d128;
    ///
    /// let got = d128::from_bits(0x2207c0000000000000000000000000a5);
    /// let want = "12.5".parse::<d128>().unwrap();
    /// assert_eq!(v, "12.5");
    /// ```
    pub const fn from_bits(bits: u128) -> Self {
        Self(bits)
    }

    /// Creates a `d128` from a little-endian byte array.
    ///
    /// ```rust
    /// use decnum::d128;
    /// ```
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
        let dpd = dpd::pack_bin_u32(coeff) as u128;
        const ZERO: u128 = 0x22080000 << 96;
        Self(ZERO | dpd)
    }

    /// Raw transmutation to `u128`.
    ///
    /// ```rust
    /// use decnum::d128;
    /// ```
    pub const fn to_bits(self) -> u128 {
        self.0
    }
}

// Const arithmetic.
impl d128 {
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
impl d128 {
    const MAX_STR_LEN: usize = Self::DIGITS as usize + "-.E1234".len();

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

        let mut tmp = [MaybeUninit::uninit(); 1 + Self::DIGITS as usize];
        let coeff = self.coeff_to_str(&mut tmp).as_bytes();
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
                const_assert!((d128::DIGITS + d128::MAX_EXP as u32) < u16::MAX as u32);
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
        const_assert!(1 + 7 + d128::DIGITS as usize <= Buffer::len());

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

    /// Writes the coefficient to `dst`.
    ///
    /// It writes at least 1 and most [`DIGITS`][Self::DIGITS] to
    /// `dst`. The extra byte is slop to let us write four bytes
    /// at a time.
    #[allow(clippy::indexing_slicing)]
    fn coeff_to_str(self, dst: &mut [MaybeUninit<u8>; 1 + Self::DIGITS as usize]) -> &str {
        // See the comment near the end of the method.
        dst[0].write(b'0');

        let mut i = 0;
        if self.msd() != 0 {
            dst[i].write(self.msd() + b'0');
            i += 1;
        }
        let dpd = self.coeff();

        // This would be more obvious as `0..=COEFF_BITS-10`, but
        // that confuses the compiler and prevents it from
        // eliding the bounds checks.
        for shift in (0..Self::COEFF_BITS - 9).rev().step_by(10) {
            let declet = ((dpd >> shift) & 0x3ff) as u16;
            let s = Str3::from_dpd(declet);
            let (src, n) = if i > 0 {
                (s.to_bytes(), 3)
            } else if s.digits() > 0 {
                (s.to_trimmed_bytes(), s.digits())
            } else {
                // This is an insignificant zero.
                continue;
            };
            copy_from_slice(&mut dst[i..i + 4], &src);
            i += n;
        }

        // We didn't write anything, but we already wrote '0' to
        // dst[0].
        //
        // Unfortunately, we can't do the write here since it
        // prevents the compiler from optimizing this method.
        if i == 0 {
            i += 1;
        }

        // SAFETY: We only write UTF-8 to `dst`.
        unsafe { str::from_utf8_unchecked(slice_assume_init_ref(&dst[..i])) }
    }

    /// Parses a decimal from a string.
    pub const fn parse(s: &str) -> Result<Self, ParseError> {
        let s = s.as_bytes();
        if s.is_empty() {
            return Err(ParseError::empty());
        }
        if s.len() > Self::MAX_STR_LEN {
            return Err(ParseError::invalid("too long"));
        }
        // `s.len()` is in [1, MAX_LEN].

        let mut i = 0;
        let sign = s[0] == b'-';
        match s[0] {
            b'-' | b'+' => i += 1,
            b'0'..=b'9' => {}
            b'i' | b'I' | b'n' | b'N' => return Self::parse_special(sign, s),
            _ => return Err(ParseError::invalid("expected digit or special")),
        }
        // `i` is in [0, 1]

        let (mut coeff, mut i) = Self::parse_coeff(s, i, 0);
        if i >= s.len() {
            return Ok(Self::from_parts(sign, 0, coeff));
        }
        if s[0] == b'.' {
            i += 1;
            (coeff, i) = Self::parse_coeff(s, i, coeff);
        }

        let mut exp = 0;
        if i < s.len() {
            match s[i] {
                b'e' | b'E' => {
                    exp = match Self::parse_exp(s, i) {
                        Ok(exp) => exp,
                        Err(err) => return Err(err),
                    };
                }
                _d => {
                    //println!("d={d}");
                    return Err(ParseError::invalid("invalid digit"));
                }
            }
        }

        Ok(Self::from_parts(sign, exp, coeff))
    }

    const fn parse_coeff(s: &[u8], mut i: usize, mut coeff: u128) -> (u128, usize) {
        while i + 4 < s.len() {
            // SAFETY: `i+4` < s.len(), so we cannot read past
            // the end of `s`.
            // TODO(eric): Do this safely.
            let chunk = unsafe { mem::transmute_copy(&s[i]) };
            let Some(s) = Str3::try_from_bytes(chunk) else {
                // We don't have three digits.
                break;
            };
            let dpd = s.to_dpd() as u128;
            coeff <<= 10;
            coeff |= dpd;
            i += 3;
        }

        if i < s.len() {
            // There might be at most three more digits.
            let mut bcd = 0;
            while i < s.len() {
                let d = s[i].wrapping_sub(b'0');
                if d >= 10 {
                    break;
                }
                bcd <<= 4;
                bcd |= d as u16;
                i += 1;
            }
            coeff |= dpd::pack(bcd) as u128;
        }

        (coeff, i)
    }

    const fn parse_exp(s: &[u8], mut i: usize) -> Result<i16, ParseError> {
        let neg = s[0] == b'-';
        if matches!(s[0], b'-' | b'+') {
            i += 1;
        }
        let mut exp: i16 = 0;
        while i < s.len() {
            let c = s[i];
            if !matches!(c, b'0'..=b'9') {
                return Err(ParseError::invalid("expected digit"));
            }
            exp = match exp.checked_mul(10) {
                Some(exp) => exp,
                None => return Err(ParseError::invalid("exp overflow")),
            };
            exp = match exp.checked_add((c - b'0') as i16) {
                Some(exp) => exp,
                None => return Err(ParseError::invalid("exp overflow")),
            };
            i += 1;
        }
        if neg {
            exp = -exp;
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

impl Add for d128 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.const_add(rhs)
    }
}

impl AddAssign for d128 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for d128 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.const_mul(rhs)
    }
}

impl MulAssign for d128 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for d128 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.const_neg()
    }
}

impl Sub for d128 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.const_sub(rhs)
    }
}

impl SubAssign for d128 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl PartialEq for d128 {
    fn eq(&self, other: &Self) -> bool {
        self.const_eq(*other)
    }
}

impl PartialOrd for d128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.const_partial_cmp(*other)
    }
}

impl FromStr for d128 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        d128::parse(s)
    }
}

impl fmt::Display for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::Default);
        write!(f, "{str}")
    }
}

impl fmt::Binary for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl fmt::LowerExp for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::LowerExp);
        write!(f, "{str}")
    }
}

impl fmt::UpperExp for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::UpperExp);
        write!(f, "{str}")
    }
}

impl fmt::Debug for d128 {
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
        write!(f, " [S:{sign} Cb:{cb:02x} Ec:{ec:02x}]",)
    }
}

/// The combination field.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Comb(
    /// ```text
    /// | Field     | Type     | Exp | Coeff   |
    /// | --------- | -------- | --- | ------- |
    /// | a b c d e | Finite   | a b | 0 c d e |
    /// | 1 1 c d e | Finite   | c d | 1 0 0 e |
    /// | 1 1 1 1 0 | Infinity | - - | - - - - |
    /// | 1 1 1 1 1 | NaN      | - - | - - - - |
    /// ```
    u8,
);

impl Comb {
    const AB: u8 = 0b11000; // ab...
    const CD: u8 = 0b00110; // ..cd.
    const E_: u8 = 0b00001; // ....e

    const fn is_finite(self) -> bool {
        !self.is_special()
    }

    const fn is_infinite(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN. The fifth bit signals NaN.
        self.0 & 0x1f == 0x1e
    }

    const fn is_nan(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN. The fifth bit signals NaN.
        self.0 & 0x1f == 0x1f
    }

    const fn is_special(self) -> bool {
        // When the first (top) four bits of the combination
        // field are set, the number is either an infinity or
        // a NaN.
        self.0 & 0x1e == 0x1e
    }

    /// Returns the encoded MSD.
    ///
    /// If the number is finite, the result is in [0, 9].
    const fn msd(self) -> u8 {
        // The MSD only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let msd = match self.0 & Self::AB {
            Self::AB => 0x8 | (self.0 & Self::E_), // 100e
            _ => self.0 & (Self::CD | Self::E_),   // 0cde
        };
        if self.is_finite() {
            // SAFETY: `msd` is either `100e` (9 or 8) or `0cde`
            // (0 through 7).
            unsafe { assume(msd <= 9) }
        }
        msd
    }

    /// Reports whether the encoded MSD is non-zero.
    const fn have_msd(self) -> bool {
        // The MSD only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        if (self.0 & Self::AB) == Self::AB {
            // If bits `ab` are set then the result is `100e`,
            // which is always non-zero.
            true
        } else {
            (self.0 & (Self::CD | Self::E_)) != 0
        }
    }

    /// Returns the encoded two MSB for the exponent.
    ///
    /// If the number is finite, the result is always in [0, 2].
    const fn msb(self) -> u8 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        // self = abcde
        let msb = match self.0 & Self::AB {
            // If bits `ab` are both set, then the MSBs are
            // encoded in bits `cd`. Otherwise, the MSBs are
            // encoded in `ab`.
            Self::AB => (self.0 & Self::CD) >> 1,
            b => b >> 3,
        };
        if self.is_finite() {
            // SAFETY: We mask and shift exactly the bits we
            // want. The only possibilities are in [0, 2].
            unsafe { assume(msb <= 2) }
        }
        msb
    }
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
    use std::ffi::CStr;

    use decnumber_sys::*;

    use super::*;

    impl d128 {
        const SNAN: Self = Self::snan(true);
        const NEG_NAN: Self = Self::nan(true);
        const NEG_SNAN: Self = Self::snan(true);
    }

    impl PartialEq<decQuad> for d128 {
        fn eq(&self, other: &decQuad) -> bool {
            self.0.to_le_bytes() == other.bytes
        }
    }

    #[test]
    fn test_exp() {
        let got = d128::new(d128::MAX_COEFF, d128::MAX_EXP);

        let want = {
            let mut d = decQuad { bytes: [0u8; 16] };
            let mut bcd = [0u8; 34];
            let mut bin = d128::MAX_COEFF;
            let mut i = 0;
            while i < bcd.len() {
                bcd[i] = (bin % 10) as u8;
                bin /= 10;
                i += 1;
            }
            unsafe { decQuadFromBCD(&mut d, d128::MAX_EXP as i32, bcd.as_ptr().cast(), 0) };
            unsafe { decQuadShow(&d, "\0".as_ptr().cast()) };
            d
        };

        assert_eq!(got.unbiased_exp(), unsafe {
            decQuadGetExponent(&want) as i16
        });
    }

    static STR_TESTS: &[(d128, &'static str)] = &[
        (d128::NAN, "NaN"),
        (d128::INFINITY, "Infinity"),
        (d128::NEG_INFINITY, "-Infinity"),
        (d128::NAN, "NaN"),
        (d128::SNAN, "sNaN"),
        (d128::NEG_NAN, "-NaN"),
        (d128::NEG_SNAN, "-sNaN"),
        (d128::new(0, 0), "0"),
        (d128::new(0, d128::MAX_EXP), "0E+6111"),
        (d128::new(0, d128::MIN_EXP), "0E-6176"),
        (
            d128::new(9111222333444555666777888999000111, d128::MAX_EXP),
            "9.111222333444555666777888999000111E+6144",
        ),
        (
            d128::new(9111222333444555666777888999000111, d128::MIN_EXP),
            "9.111222333444555666777888999000111E-6143",
        ),
        (
            d128::new(9111222333444555666777888999000111, 0),
            "9111222333444555666777888999000111",
        ),
        (
            d128::new(9111222333444555666777888999000111, -2),
            "91112223334445556667778889990001.11",
        ),
        (
            d128::new(9111222333444555666777888999000111, 2),
            "9.111222333444555666777888999000111E+35",
        ),
        (
            d128::new(9999999999999999999999999999999999, -39),
            "0.000009999999999999999999999999999999999",
        ),
        (d128::new(42, 1), "4.2E+2"),
        (d128::new(42, 0), "42"),
        (d128::new(42, -1), "4.2"),
        (d128::new(42, -2), "0.42"),
        (d128::new(42, -3), "0.042"),
        (d128::new(42, -4), "0.0042"),
        (d128::new(42, -5), "0.00042"),
        (d128::new(42, -6), "0.000042"),
        (d128::new(42, -7), "0.0000042"),
        (d128::new(42, -8), "4.2E-7"),
    ];

    #[test]
    fn test_format() {
        for (i, (input, want)) in STR_TESTS.iter().enumerate() {
            let got = input.to_string();
            assert_eq!(got, *want, "#{i}");
        }

        #[allow(dead_code)] // TODO
        fn to_str(mut bin: i128, exp: i16) -> String {
            let neg = bin < 0;
            let mut d = decQuad { bytes: [0u8; 16] };
            let mut bcd = [0u8; 34];
            for v in bcd.iter_mut().rev() {
                *v = (bin % 10) as u8;
                bin /= 10;
            }
            unsafe { decQuadFromBCD(&mut d, exp as i32, bcd.as_ptr().cast(), neg as i32) };
            unsafe { decQuadShow(&d, "\0".as_ptr().cast()) };

            let mut buf = [0i8; 128];
            let ptr = unsafe { decQuadToString(&d, buf.as_mut_ptr()) };
            let cstr = unsafe { CStr::from_ptr(ptr) };
            cstr.to_str().unwrap().to_owned()
        }
    }

    #[test]
    fn test_parse() {
        for (i, (want, output)) in STR_TESTS.iter().enumerate() {
            let got: d128 = output.parse().unwrap();
            assert_eq!(got, *want, "#{i}");
        }
    }

    #[test]
    fn test_from_u32() {
        let got = d128::from_u32(u32::MAX);

        let want = {
            let mut d = decQuad { bytes: [0u8; 16] };
            unsafe { decQuadFromUInt32(&mut d, u32::MAX) };
            unsafe { decQuadShow(&d, "\0".as_ptr().cast()) };
            d
        };

        assert_eq!(got, want);
    }

    #[test]
    fn test_digits() {
        for i in 1..d128::DIGITS {
            let v = 10i128.pow(i);
            let got = d128::new(v - 1, 0).digits();
            let want = v.ilog10();
            assert_eq!(got, want, "#{}", v - 1);
            println!();
        }
    }

    #[test]
    fn test_partial_cmp() {
        let tests = [
            ("NaN", "3", None),
            ("3", "NaN", None),
            ("2.1", "3", Some(Ordering::Less)),
            ("2.1", "2.1", Some(Ordering::Equal)),
            ("2.1", "2.10", Some(Ordering::Equal)),
            ("3", "2.1", Some(Ordering::Greater)),
            ("2.1", "-3", Some(Ordering::Greater)),
            ("-3", "2.1", Some(Ordering::Less)),
        ];
        for (i, (lhs, rhs, want)) in tests.into_iter().enumerate() {
            let x: d128 = lhs.parse().unwrap();
            let y: d128 = rhs.parse().unwrap();
            let got = x.const_partial_cmp(y);
            assert_eq!(got, want, "#{i}: total_cmp({lhs}, {rhs})");
        }
    }
}
