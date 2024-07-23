#![allow(dead_code, unused_imports)]

use core::{fmt, hint, mem, str};

use super::{
    bcd::{self, Bcd10},
    dpd,
    tables::{BIN_TO_DPD, DPD_TO_BIN, TEST_MSD},
};

const BIAS: u32 = 6176;
const E_LIMIT: i16 = 12287;
const E_CONT_LEN: u32 = 12;

const SIGNBIT: u32 = 1 << 31;

/// Indicates an infinity or NaN.
const SPECIAL: u32 = 0b0_11110_00 << 24;
const INF: u32 = 0b0_11110_00 << 24;
const NAN: u32 = 0b0_11111_00 << 24;
const QNAN: u32 = 0b0_11111_00 << 24;
const SNAN: u32 = 0b0_11111_10 << 24;

/// Covers all of the NaN bits.
const NAN_MASK: u32 = 0b0111111 << 25;

/// A 128-bit decimal.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
pub struct d128(
    /// # Layout
    ///
    /// ## Bits
    ///
    /// 0: sign
    /// 1-5: combination
    /// 6-17: exponent continuation
    /// 17-127: coefficient continuation
    ///
    /// ## Words
    ///
    /// 0: xxx
    /// 1: xxx
    /// 2: xxx
    /// 3: xxx
    ///
    ///
    /// # Combination field
    ///
    /// ```text
    /// | Field     | Type     | Exp | Coeff   |
    /// | --------- | -------- | --- | ------- |
    /// | a b c d e | Finite   | a b | 0 c d e |
    /// | 1 1 c d e | Finite   | c d | 1 0 0 e |
    /// | 1 1 1 1 0 | Infinity | - - | - - - - |
    /// | 1 1 1 1 1 | NaN      | - - | - - - - |
    /// ```
    u128,
);
const _: () = assert!(mem::size_of::<d128>() == 128 / 8);

impl d128 {
    // /// The largest value that can be represented by this type.
    // pub const MAX: Self = Self::new(Self::MAX_COEFF, Self::MAX_EXP);

    // /// The smallest value that can be represented by this type.
    // pub const MIN: Self = Self::new(Self::MIN_COEFF, Self::MAX_EXP);

    // /// The smallest positive value that can be represented by
    // /// this type.
    // pub const MIN_POSITIVE: Self = Self::new(Self::MAX_COEFF, Self::MIN_EXP);

    /// The largest allowed coefficient.
    pub const MAX_COEFF: i128 = 10i128.pow(34) - 1;

    /// The smallestallowed coefficient.
    pub const MIN_COEFF: i128 = -Self::MAX_COEFF;

    /// The maximum allowed exponent.
    pub const MAX_EXP: i16 = 6144 - Self::MAX_PREC + 1;

    /// The smallest allowed exponent.
    pub const MIN_EXP: i16 = -6143 - Self::MAX_PREC + 1;

    /// The exponent's bias.
    const BIAS: i16 = 6176;
    const LIMIT: i16 = 12287;

    /// The number of significant digits in base 10.
    pub const DIGITS: u32 = 34;
    const MAX_PREC: i16 = 34;

    /// Not a Number (NaN).
    pub const NAN: Self = Self::special(NAN);

    /// Infinity (∞).
    pub const INFINITY: Self = Self::special(INF);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self::special(INF | SIGNBIT);

    const SIGN_MASK: u128 = 1 << Self::SIGN_SHIFT;
    const SIGN_SHIFT: u32 = 128 - 1;

    const COMB_MASK: u128 = 0x1f << Self::COMB_SHIFT;
    const COMB_SHIFT: u32 = 128 - 1 - 5;

    const ECON_MASK: u128 = 0xfff << Self::ECON_SHIFT;
    const ECON_SHIFT: u32 = 128 - 1 - 5 - 12;

    const COEFF_MASK: u128 = (1 << 110) - 1;

    /// Reports whether the number is neither infinite nor NaN.
    pub const fn is_finite(self) -> bool {
        !self.is_special()
    }

    /// Reports whether the number is either positive or negative
    /// infinity.
    pub const fn is_infinite(self) -> bool {
        (self.top_word() & INF) == INF
    }

    /// Reports whether the number is neither zero, infinite,
    /// subnormal, or NaN.
    pub const fn is_normal(self) -> bool {
        if !self.is_special() || !self.is_zero() {
            return false;
        }
        // (exp + self.digits() - 1) >= E_MIN
        todo!()
    }

    /// Reports whether the number is subnormal.
    pub const fn is_subnormal(self) -> bool {
        !self.is_special() && !self.is_normal() && !self.is_zero()
    }

    /// Reports whether the number is `-0.0` or `+0.0`.
    pub const fn is_zero(self) -> bool {
        // Check the least significant words.
        if self.word32(3) != 0 || self.word32(2) != 0 || self.word32(1) != 0 {
            return false;
        }
        // Match the MSD and part of the coefficient.
        const MSD_DPD: u32 = 0b0_00111_000000000000_11111111111111;
        if self.word32(0) & MSD_DPD != 0 {
            return false;
        }
        // Exclude specials and MSD > 7.
        const SPECIALS_MSD: u32 = 0b0_11000_000000000000_00000000000000;
        self.word32(0) & SPECIALS_MSD != SPECIALS_MSD
    }

    /// Reports whether the number is a NaN.
    pub const fn is_nan(self) -> bool {
        (self.top_word() & NAN_MASK) == QNAN
    }

    /// Reports whether the number is a quiet NaN.
    pub const fn is_qnan(self) -> bool {
        (self.top_word() & NAN_MASK) == QNAN
    }

    /// Reports whether the number is a signaling NaN.
    pub const fn is_snan(self) -> bool {
        (self.top_word() & NAN_MASK) == SNAN
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
        (self.top_word() & SPECIAL) == SPECIAL
    }

    /// Returns the combination field.
    const fn comb(self) -> u16 {
        ((self.0 & Self::COMB_MASK) >> Self::COMB_SHIFT) as u16
    }

    /// Returns the exponent continuation field.
    const fn econ(self) -> u16 {
        ((self.0 & Self::ECON_MASK) >> Self::ECON_SHIFT) as u16
    }

    /// Returns the biased exponment.
    const fn exp(self) -> i16 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let econ = self.econ();

        let comb = self.comb();
        const AB: u16 = 0b11000; // ab...
        const CD: u16 = 0b00110; // ..cd.
        let msb = match comb & AB {
            AB => (comb & CD) << 12,
            b => b << 10,
        };
        (msb | econ) as i16
    }

    /// Returns the unbiased exponent.
    const fn unbiased_exp(self) -> i16 {
        self.exp() - Self::BIAS
    }

    /// Returns the most significant word.
    const fn top_word(self) -> u32 {
        self.word32(0)
    }

    /// Returns the word at `idx`.
    const fn word32(self, idx: u32) -> u32 {
        debug_assert!(idx < 4);

        (self.0 >> ((3 - idx) * 32)) as u32
    }

    /// Creates a `d128` from its coefficient and exponent.
    pub const fn new(coeff: i128, exp: i16) -> Self {
        // TODO(eric): the inf probably isn't correct.
        if coeff < Self::MIN_COEFF || exp < Self::MIN_EXP {
            Self::NEG_INFINITY
        } else if coeff > Self::MAX_COEFF || exp > Self::MAX_EXP {
            Self::INFINITY
        } else {
            Self::from_parts(coeff < 0, exp, coeff as u128)
        }
    }

    /// Creates a `d128` from its raw bits.
    ///
    /// # Safety
    ///
    /// It is undefined behavior if `bits` is not a valid IEEE
    /// 754-2008 decimal. This may affect the safety of other
    /// operations.
    pub const unsafe fn from_bits(bits: u128) -> Self {
        // TODO(eric): debug assert validity
        Self(bits)
    }

    /// Creates a `d128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        let dpd = dpd::from_u32(coeff) as u128;
        const ZERO: u128 = 0x22080000 << 96;
        Self(ZERO | dpd)
    }

    const fn from_words32(w0: u32, w1: u32, w2: u32, w3: u32) -> Self {
        Self(((w0 as u128) << 96) | ((w1 as u128) << 64) | ((w2 as u128) << 32) | w3 as u128)
    }

    const fn from_words64(w0: u64, w1: u64) -> Self {
        Self(((w0 as u128) << 64) | (w1 as u128))
    }

    const fn from_parts(sign: bool, exp: i16, coeff: u128) -> Self {
        debug_assert!(exp >= Self::MIN_EXP);
        debug_assert!(exp <= Self::MAX_EXP);
        debug_assert!(coeff <= Self::MAX_COEFF as u128);

        let dpd = dpd::from_u113(coeff);
        let biased = (exp + Self::BIAS) as u128;

        let sign = (sign as u128) << Self::SIGN_SHIFT;
        let comb = {
            // `dpd` is 120 bits. The top 6 bits are always zero.
            // The next 4 bits contain the MSD.
            let msd = (dpd >> 110) & 0x9;
            debug_assert!(msd <= 9);

            let mut msb = (biased & 0x3000) >> 12;
            debug_assert!(msb <= 2);

            // 0 c d e -> [0,7]
            // 1 0 0 e -> [8,9]
            if msd <= 7 {
                msb <<= 3
            } else {
                msb <<= 1
            }
            (msb | msd) << Self::COMB_SHIFT
        };
        debug_assert!(comb & !Self::COMB_MASK == 0);

        let econ = (biased << Self::ECON_SHIFT) & Self::ECON_MASK;
        debug_assert!(econ & !Self::ECON_MASK == 0);

        let coeff = dpd & Self::COEFF_MASK;
        debug_assert!(coeff & !Self::COEFF_MASK == 0);

        // println!("sign = {sign:0128b}");
        // println!("comb = {comb:0128b}");
        // println!("econ = {econ:0128b}");
        // println!("coef = {coeff:0128b}");
        // println!("     = {:0128b}", sign | comb | econ | coeff);

        Self(sign | comb | econ | coeff)
    }

    /// Creates a special decimal.
    const fn special(w: u32) -> Self {
        Self((w as u128) << 96)
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
    ///
    /// # Panics
    ///
    /// This function panics if `buf` is not long enough. To
    /// ensure it does not panic, `buf` should be at least
    /// [`MAX_STR_LEN`][Self::MAX_STR_LEN] bytes long.
    pub fn to_str<'a>(self, buf: &'a mut [u8]) -> &'a str {
        let mut i = 0;
        if self.is_sign_negative() {
            buf[i] = b'-';
            i += 1;
        }

        if self.is_special() {
            if self.is_infinite() {
                i += copy(&mut buf[i..], b"Infinity");
            } else if self.is_qnan() {
                i += copy(&mut buf[i..], b"NaN");
            } else if self.is_snan() {
                i += copy(&mut buf[i..], b"sNaN");
            }
            // SAFETY: `buf` only ever contains UTF-8.
            return unsafe { str::from_utf8_unchecked(&buf[..i]) };
        }

        let exp = self.unbiased_exp();

        let len = 0;
        let (e, pre) = if exp > 0 || (len + exp) < -5 {
            (len + exp - 1, 1)
        } else {
            (0, len + exp)
        };

        // SAFETY: `buf` only ever contains UTF-8.
        return unsafe { str::from_utf8_unchecked(&buf[..i]) };
    }
}

impl fmt::Display for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u8; Self::MAX_STR_LEN];
        let str = self.to_str(&mut buf);
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
        let ec = (((b[15] & 0x3) as u16) << 10) | (b[14] << 2) as u16 | (b[13] >> 6) as u16;
        write!(f, " [S:{sign} Cb:{cb:02x} Ec:{ec:02x}]",)
    }
}

pub(super) const COMB_EXP: [u32; 64] = [
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    0,
    0,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    INF,
    NAN,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    0,
    0,
    1 << E_CONT_LEN,
    1 << E_CONT_LEN,
    2 << E_CONT_LEN,
    2 << E_CONT_LEN,
    INF,
    NAN,
];

const COMB_MSD: [u32; 64] = [
    0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 9, 8, 9, 0, 0,
    0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 9, 8, 9, 0, 0,
];

fn copy(dst: &mut [u8], src: &[u8]) -> usize {
    let n = src.len();
    dst[..n].copy_from_slice(src);
    n
}

#[cfg(test)]
mod tests {
    use core::ptr;

    use dec::Decimal128;
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
        let _want = {
            let mut d = decQuad { bytes: [0u8; 16] };
            let mut ctx = decContext {
                digits: 0,
                emax: 0,
                emin: 0,
                round: 0,
                traps: 0,
                status: 0,
                clamp: 0,
            };
            unsafe { decContextDefault(&mut ctx, 128) };
            unsafe { decQuadFromString(&mut d, "-sNaN\0".as_ptr().cast(), &mut ctx) };
            unsafe { decQuadShow(&d, "\0".as_ptr().cast()) };
            d
        };
    }

    #[test]
    fn test_from_u32() {
        let got = d128::from_u32(u32::MAX);
        println!("{got:?}");

        let want = {
            let mut d = decQuad { bytes: [0u8; 16] };
            unsafe { decQuadFromUInt32(&mut d, u32::MAX) };
            unsafe { decQuadShow(&d, "\0".as_ptr().cast()) };
            d
        };

        assert_eq!(got, want);
    }
}
