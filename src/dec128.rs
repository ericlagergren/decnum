#![allow(dead_code, unused_imports)]

use core::{fmt, mem};

use super::{
    bcd::{self, Bcd10},
    dpd,
    tables::{BIN2CHAR, BIN2DPD, DPD2BIN, TEST_MSD},
};

const E_MIN: i16 = -6143;
const E_MAX: i16 = 6144;
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
    /// The largest value that can be represented by this type.
    pub const MAX: Self = Self::new(79228162514264337593543950335);
    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self::new(-79228162514264337593543950335);

    /// Not a Number (NaN).
    pub const NAN: Self = Self::special(NAN);

    /// Infinity (∞).
    pub const INFINITY: Self = Self::special(INF);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self::special(INF | SIGNBIT);

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
        (self.top_word() & SIGNBIT) == 0
    }

    /// Reports whether the number is negative, including `-0.0`.
    pub const fn is_sign_negative(self) -> bool {
        (self.top_word() & SIGNBIT) != 0
    }

    /// Reports whether the number is infinite or NaN.
    const fn is_special(self) -> bool {
        (self.top_word() & SPECIAL) == SPECIAL
    }

    /// Returns the exponent continuation.
    const fn econ(&self) -> u32 {
        const SHIFT: u32 = 32 - 6 - E_CONT_LEN;
        (self.top_word() & 0x03ffffff) >> SHIFT
    }

    /// Returns the most significant word.
    const fn top_word(self) -> u32 {
        self.word32(0)
    }

    /// Returns the word at `idx`.
    const fn word32(self, idx: u32) -> u32 {
        debug_assert!(idx < 4);

        (self.0 >> (4 - idx) * 32) as u32
    }

    /// TODO
    pub const fn new(_v: i128) -> Self {
        todo!()
    }

    /// Creates a `d128` from `v`.
    pub const fn from_u32(v: u32) -> Self {
        let bcd = Bcd10::from_bin(v);
        let dpd = bcd.pack();

        const ZERO: u32 = 0x22080000;
        Self::from_words(ZERO, 0, (v / 1_000_000_000) >> 2, dpd)
    }

    const fn from_words(w0: u32, w1: u32, w2: u32, w3: u32) -> Self {
        Self(((w0 as u128) << 96) | ((w1 as u128) << 64) | ((w2 as u128) << 32) | w3 as u128)
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
    pub const fn const_add(self, rhs: Self) -> Self {
        let lhs_msd = self.top_word();
        let mut summ = TEST_MSD[(lhs_msd >> 26) as usize];
        let _bexpr = COMB_EXP[(lhs_msd >> 26) as usize] + self.econ();

        let rhs_msd = rhs.top_word();
        summ += TEST_MSD[(rhs_msd >> 26) as usize];
        let _bexpl = COMB_EXP[(rhs_msd >> 26) as usize] + rhs.econ();

        let diff_sign = (lhs_msd ^ rhs_msd) & SIGNBIT != 0;

        // Is MSD + MSD good?
        if summ <= 8 {
            // Is there a special?
            if summ < 0 {
                if summ < -64 {
                    todo!() // one or two NaNs
                }
                if summ == -64 && diff_sign {
                    todo!() // invalid
                }
                if self.is_infinite() {
                    todo!() // self inf
                }
                debug_assert!(rhs.is_infinite());
                todo!() // rhs inf
            }
        }

        Self(0)
    }
}

impl fmt::Display for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lo = self.0 as u32;
        let ml = (self.0 >> 32) as u32;
        let mh = (self.0 >> 64) as u32;
        let hi = (self.0 >> 96) as u32;

        // Combination field.
        let comb = (hi >> 26) & 0x1f;
        let mut msd = COMB_MSD[comb as usize];
        let mut exp = COMB_EXP[comb as usize];

        if (hi as i32) < 0 {
            write!(f, "-")?;
        }

        if exp == 3 {
            if msd == 0 {
                return write!(f, "inf");
            }
            if (hi & 0x02000000) != 0 {
                write!(f, "s")?;
            }
            write!(f, "NaN")?;
            if lo == 0 && ml == 0 && mh == 0 && (hi & 0x0003ffff) == 0 {
                return Ok(());
            }
            exp = 0;
            msd = 0;
        } else {
            exp = (exp << 12) + ((hi >> 14) & 0xfff) - BIAS;
        }
        let _ = exp;

        if msd != 0 {
            write!(f, "{}", b'c' + msd as u8)?;
        }

        // macro_rules! dpd2char {
        //     ($f:ident, $dpd:expr) => {
        //         let u = BIN2CHAR[(DPD2BIN[dpd as usize] * 4) as usize];
        //     };
        // }

        Ok(())
    }
}

impl fmt::Debug for d128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ">> ")?;
        for (i, c) in self.0.to_be_bytes().iter().enumerate() {
            write!(f, "{c:02x}")?;
            if ((i + 1) % 4) == 0 {
                write!(f, " ")?;
            }
        }
        let b = self.0.to_be_bytes();
        write!(
            f,
            " [S:{} Cb:{:02x} Ec:{:02x}]",
            b[15] >> 7,
            (b[15] >> 2) & 0x1f,
            (((b[15] & 0x3) as u16) << 10) | (b[14] << 2) as u16 | (b[13] >> 6) as u16,
        )
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

#[cfg(test)]
mod tests {
    use core::ptr;

    use dec::Decimal128;
    use decnumber_sys::{decQuad, decQuadFromUInt32, decQuadShow};

    use super::*;

    #[test]
    fn test_from_u32() {
        let d = d128::from_u32(u32::MAX);
        println!("{d:?}");

        let mut q = decQuad { bytes: [0u8; 16] };
        unsafe { decQuadFromUInt32(&mut q, u32::MAX) };
        unsafe { decQuadShow(&q, "\0".as_ptr().cast()) }
    }
}
