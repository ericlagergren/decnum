use core::{fmt, num::FpCategory, str};

use super::{
    dpd,
    util::{self, assume},
};

/// A 128-bit decimal.
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
const _: () = assert!(size_of::<d128>() == 128 / 8);

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

    /// Returns the combination field.
    const fn comb(self) -> Comb {
        let v = (self.0 & Self::COMB_MASK) >> Self::COMB_SHIFT;
        Comb(v as u8)
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
            const _: () = assert!(d128::LIMIT < (1 << 14) - 1);

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
        const _: () = assert!(d128::LIMIT < i16::MAX as u16);
        const _: () = assert!(i16::MAX - (d128::LIMIT as i16) > d128::BIAS);

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
        const _: () = assert!(d128::DIGITS <= i16::MAX as u32);

        debug_assert!(self.is_finite());

        // `self.digits() as i16` does not wrap because it is in
        // [1, DIGITS], and `DIGITS <= i16::MAX`.
        #[allow(clippy::cast_possible_wrap)]
        let digits = self.digits() as i16;

        self.unbiased_exp() + digits - 1
    }

    /// Returns the coefficient, less the MSD.
    const fn coeff(self) -> u128 {
        debug_assert!(self.is_finite());

        self.0 & Self::COEFF_MASK
    }

    /// Returns the coefficient, including the MSD.
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
    pub const NAN: Self = Self::from_fields(false, 0x1f, 0, 0);

    /// Infinity (∞).
    pub const INFINITY: Self = Self::from_fields(false, 0x1e, 0, 0);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self::from_fields(true, 0x1e, 0, 0);

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
        (self.0 & Self::SIGN_MASK) == 0
    }

    /// Reports whether the number is negative, including `-0.0`.
    pub const fn is_sign_negative(self) -> bool {
        !self.is_sign_positive()
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

    /// Creates a `d128` from its raw bits.
    pub const fn from_bits(bits: u128) -> Self {
        Self(bits)
    }

    /// Creates a `d128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        let dpd = dpd::pack_bin_u32(coeff) as u128;
        const ZERO: u128 = 0x22080000 << 96;
        Self(ZERO | dpd)
    }
}

// Const.
impl d128 {
    /// Returns `self + other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_add(self, _rhs: Self) -> Self {
        todo!()
    }
}

// String conversions.
impl d128 {
    /// The maximum length in bytes of a `d128` encoded as
    /// a string.
    pub const MAX_STR_LEN: usize = "-9.999999999999999999999999999999999E+6144".len();

    /// Converts the `d128` to a string.
    #[allow(clippy::indexing_slicing)]
    pub fn to_str(self, dst: &mut [u8; Self::MAX_STR_LEN]) -> &str {
        if self.is_special() {
            let start = usize::from(self.is_sign_positive());
            let end = if self.is_infinite() {
                copy(dst, b"-Infinity")
            } else if self.is_qnan() {
                copy(dst, b"-NaN")
            } else {
                copy(dst, b"-sNaN")
            };
            // SAFETY: `buf` only ever contains UTF-8.
            return unsafe { str::from_utf8_unchecked(&dst[start..end]) };
        }
        debug_assert!(self.is_finite());

        let exp = i32::from(self.unbiased_exp());
        //println!("exp={exp}");

        let mut tmp = [0u8; 1 + Self::DIGITS as usize];
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
        let (mut e, pre) = {
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
            dst[0] = b'-';

            //println!("pre={pre} coeff={}", coeff.len());
            if pre < coeff.len() {
                let (pre, post) = coeff.split_at(pre);
                dst[i..i + pre.len()].copy_from_slice(pre);
                dst[i + pre.len()] = b'.';
                dst[i + pre.len() + 1..i + pre.len() + 1 + post.len()].copy_from_slice(post);
                i += 1;
            } else {
                dst[i..i + coeff.len()].copy_from_slice(coeff);
            };
            i += coeff.len();

            //println!("e={e}");
            if e != 0 {
                dst[i] = b'E';
                i += 1;
                if e < 0 {
                    dst[i] = b'-';
                    e = -e;
                } else {
                    dst[i] = b'+';
                };
                i += 1;
                debug_assert!(e > 0);

                //println!("i={i}");

                const _: () = assert!((d128::DIGITS + d128::MAX_EXP as u32) < u16::MAX as u32,);

                // We negate `e` if `e < 0`, so we cannot lose
                // the sign here.
                //
                // `e` is either 0 or `pre-1`. Since `pre` is in
                // [1, DIGITS+MAX_EXP] and DIGITS+MAX_EXP <=
                // u16::MAX, the cast cannot wrap.
                #[allow(clippy::cast_sign_loss)]
                let s = util::itoa4(e as u16);
                dst[i..i + 4].copy_from_slice(&s.to_bytes());
                i += s.digits();
            }

            let start = usize::from(self.is_sign_positive());
            //println!("start={start} i={i} len={}", dst.len());
            // SAFETY: `buf` only ever contains UTF-8.
            return unsafe { str::from_utf8_unchecked(&dst[start..i]) };
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
        // SAFETY: TODO
        unsafe {
            assume(pre <= 7);
            assume(pre >= 2);
        }
        let mut i = 1;
        dst[0] = b'-';
        dst[i..i + 7].copy_from_slice(b"0.00000");
        // SAFETY: `pre` was in [-5, 0]. After negation and
        // adding 2, `pre` is now in [2, 7]. `coeff` is in [1,
        // DIGITS], so `i+pre+coeff.len()` is in [1+2+DIGITS,
        // 1+7+DIGITS].
        unsafe {
            const _: () = assert!(1 + 7 + d128::DIGITS as usize <= d128::MAX_STR_LEN);
            dst.get_unchecked_mut(i + pre..i + pre + coeff.len())
        }
        .copy_from_slice(coeff);
        i += pre;
        i += coeff.len();

        let start = usize::from(self.is_sign_positive());
        // SAFETY: `buf` only ever contains UTF-8.
        return unsafe { str::from_utf8_unchecked(&dst[start..i]) };
    }

    /// Writes the coefficient to `dst`.
    ///
    /// It writes at least 1 and most [`DIGITS`][Self::DIGITS] to
    /// `dst`. The extra byte is slop to let us write four bytes
    /// at a time.
    #[allow(clippy::indexing_slicing)]
    fn coeff_to_str(self, dst: &mut [u8; 1 + Self::DIGITS as usize]) -> &str {
        // See the comment near the end of the method.
        dst[0] = b'0';

        let mut i = 0;
        if self.msd() != 0 {
            dst[i] = self.msd() + b'0';
            i += 1;
        }
        let dpd = self.coeff();

        // This would be more obvious as `0..=COEFF_BITS-10`, but
        // that confuses the compiler and prevents it from
        // eliding the bounds checks.
        for shift in (0..Self::COEFF_BITS - 9).rev().step_by(10) {
            let declet = ((dpd >> shift) & 0x3ff) as u16;
            let s = dpd::unpack_to_str(declet);
            let (src, n) = if i > 0 {
                (s.to_bytes(), 3)
            } else if s.digits() > 0 {
                (s.to_trimmed_bytes(), s.digits())
            } else {
                // This is an insignificant zero.
                continue;
            };
            dst[i..i + 4].copy_from_slice(&src);
            i += n;
        }

        // We didn't write anything. We already wrote '0' to
        // dst[0].
        //
        // Unfortunately, we can't do the write here since it
        // prevents the compiler from optimizing this method.
        if i == 0 {
            i += 1;
        }

        // SAFETY: We only write UTF-8 to `dst`.
        unsafe { str::from_utf8_unchecked(&dst[..i]) }
    }
}

impl fmt::Display for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u8; Self::MAX_STR_LEN];
        let str = self.to_str(&mut buf);
        write!(f, "{str}")
    }
}

impl fmt::Binary for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
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

#[inline(always)]
fn copy(dst: &mut [u8], src: &[u8]) -> usize {
    let n = src.len();
    // The caller must verify the length of `dst`
    #[allow(clippy::indexing_slicing)]
    dst[..n].copy_from_slice(src);
    n
}

#[cfg(test)]
mod tests {
    use std::ffi::CStr;

    use decnumber_sys::*;

    use super::*;

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

    #[test]
    fn test_to_str() {
        let tests = [
            (d128::NAN, "NaN"),
            (d128::INFINITY, "Infinity"),
            (d128::NEG_INFINITY, "-Infinity"),
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
        for (i, (input, want)) in tests.into_iter().enumerate() {
            println!("want={want}");
            //println!("want={}", to_str(9999999999999999999999999999999999, -39));
            let got = input.to_string();
            assert_eq!(got, want, "#{i}");
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
}
