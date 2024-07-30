#![allow(dead_code, unused_imports)]

use core::{fmt, hint, mem, str};

use super::{
    bcd::{self, Bcd10},
    dpd,
    tables::{BIN_TO_DPD, DPD_TO_BIN, TEST_MSD},
    util::{self, assume},
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

/// The combination field.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Comb(u8);

impl Comb {
    const fn is_finite(self) -> bool {
        !self.is_special()
    }

    const fn is_infinite(self) -> bool {
        // When the first four bits of the combination field are
        // set, the number is either an infinity or a NaN. If he
        // fifth bit is also set, then the number is a NaN.
        const MASK: u8 = 0b111111;
        self.0 & MASK == 0b111110
    }

    const fn is_nan(self) -> bool {
        // When the first four bits of the combination field are
        // set, the number is either an infinity or a NaN. If he
        // fifth bit is also set, then the number is a NaN.
        const MASK: u8 = 0b111111;
        self.0 & MASK == MASK
    }

    const fn is_special(self) -> bool {
        // When the first four bits of the combination field are
        // set, the number is either an infinity or a NaN.
        const MASK: u8 = 0b111110;
        self.0 & MASK == MASK
    }

    /// Returns the encoded MSD.
    const fn msd(self) -> u8 {
        // The MSD only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        const AB: u8 = 0b11000; // ab...
        const CD: u8 = 0b00110; // ..cd.
        const E_: u8 = 0b00001; // ....e
        match self.0 & AB {
            AB => 0x8 | (self.0 & E_), // 100e
            _ => self.0 & (CD | E_),   // 0cde
        }
    }

    /// Reports whether the encoded MSD is non-zero.
    const fn have_msd(self) -> bool {
        // The MSD only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        const AB: u8 = 0b11000; // ab...
        const CD: u8 = 0b00110; // ..cd.
        const E_: u8 = 0b00001; // ....e

        (self.0 & AB) == AB || (self.0 & (CD | E_)) != 0
    }

    /// Returns the encoded two MSB for the exponent.
    ///
    /// The result is always one of `0x0`, `0x1`, or `0x2`.
    const fn msb(self) -> u8 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        const AB: u8 = 0b11000; // ab....
        const CD: u8 = 0b00110; // ..cd..
        match self.0 >> 3 {
            // If bits `ab` are both set, then the MSBs are
            // encoded in `cd`. Otherwise, the MSBs are encoded
            // in `ab`.
            0x3 => (self.0 & CD) >> 1,
            b => b,
        }
    }
}

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
const _: () = assert!(size_of::<d128>() == 128 / 8);

// Internal stuff.
impl d128 {
    const BIAS: i16 = 6176;
    const LIMIT: i16 = 12287;
    const MAX_PREC: i16 = 34;

    /// The number of three digit declets in the full
    /// coefficient.
    const DECLETS: usize = 12;

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

    // TODO
    const fn validate(self) {
        // let comb = self.comb();
        // let msb = comb >> 3;
        // debug_assert!((msb & 1) ^ (msb >> 1) == 0);
    }

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
    const fn econ(self) -> u16 {
        ((self.0 & Self::ECON_MASK) >> Self::ECON_SHIFT) as u16
    }

    /// Returns the biased exponment.
    ///
    /// The result is in [0, [`LIMIT`][Self::LIMIT]].
    const fn exp(self) -> i16 {
        // The exponent only has meaning for finite numbers.
        debug_assert!(self.is_finite());

        let econ = self.econ();
        let msb = self.comb().msb() as u16;
        // `exp` is a 14-bit integer. Its two MSB are either 10,
        // 01, or 00, so its maximum value is 0x2fff = 12287.
        #[allow(clippy::cast_possible_wrap)]
        let exp = (msb | econ) as i16;
        exp
    }

    /// Returns the unbiased exponent.
    ///
    /// The result is in [[`MIN_EXP`][Self::MIN_EXP],
    /// [`MAX_EXP`][Self::MAX_EXP]].
    const fn unbiased_exp(self) -> i16 {
        //const _: () = assert!(d128::LIMIT + d128::BIAS);

        let exp = self.exp() - Self::BIAS;
        // SAFETY: `self.exp()` returns an integer in [0,LIMIT].
        unsafe {
            assume(exp >= Self::MIN_EXP);
            assume(exp <= Self::MAX_EXP);
        }
        exp
    }

    /// Returns the coefficient, less the MSD.
    const fn coeff(self) -> u128 {
        self.0 & Self::COEFF_MASK
    }

    /// Returns the coefficient, including the MSD.
    const fn full_coeff(self) -> u128 {
        self.coeff() | ((self.msd() as u128) << 110)
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

        let dpd = dpd::pack_bin_u113(coeff);
        // TODO(eric): If `exp` is valid then this cannot
        // overflow. Maybe make sure of it?
        #[allow(clippy::cast_sign_loss)]
        let biased = (exp + Self::BIAS) as u128;

        let sign = (sign as u128) << Self::SIGN_SHIFT;
        let comb = {
            // `dpd` is 120 bits. The top 6 bits are always zero.
            // The next 4 bits contain the MSD.
            let msd = (dpd >> 110) & 0x9;
            debug_assert!(msd <= 9);

            let msb = (biased & 0x3000) >> 12;
            debug_assert!(msb <= 2);

            // [0,7] -> 0cde
            // [8,9] -> 100e
            let comb = if msd <= 7 {
                (msb << 3) | msd
            } else {
                0x18 | (msb << 1) | msd
            };
            comb << Self::COMB_SHIFT
        };
        debug_assert!(comb & !Self::COMB_MASK == 0);

        let econ = ((biased & 0xfff) << Self::ECON_SHIFT) & Self::ECON_MASK;
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
    pub const MAX_EXP: i16 = 6144 - Self::MAX_PREC + 1;

    /// The smallest allowed exponent.
    pub const MIN_EXP: i16 = -6143 - Self::MAX_PREC + 1;

    /// The number of significant digits in base 10.
    pub const DIGITS: u32 = 34;

    /// Not a Number (NaN).
    pub const NAN: Self = Self::special(NAN);

    /// Infinity (∞).
    pub const INFINITY: Self = Self::special(INF);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self::special(INF | SIGNBIT);

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
        let exp = self.unbiased_exp() + self.digits() - 1;
        exp > -6143 // emin
    }

    /// Reports whether the number is subnormal.
    pub const fn is_subnormal(self) -> bool {
        !self.is_special() && !self.is_normal() && !self.is_zero()
    }

    /// Reports whether the number is `-0.0` or `+0.0`.
    pub const fn is_zero(self) -> bool {
        self.is_finite() && self.full_coeff() == 0
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

    /// Returns the number of digits in the coefficient.
    pub const fn coeff_len(self) -> usize {
        let coeff = self.coeff();
        // The number of whole declets. Less 18 for the sign,
        // comb, and exp fields.
        let n = (110 - (coeff.leading_zeros() - 18)) / 10;
        let dpd = ((coeff >> (n * 10)) & 0x3ff) as u16;
        let mut digits = 0;
        digits += dpd::sig_digits(dpd);
        digits += n * 3;
        digits += self.have_msd() as u32;
        digits as usize
    }

    /// Converts the `d128` to a string.
    #[allow(clippy::indexing_slicing)]
    pub fn to_str(self, dst: &mut [u8; Self::MAX_STR_LEN]) -> &str {
        if self.is_special() {
            let start = usize::from(self.is_sign_negative());
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

        let mut i = 0;
        let start = i;

        dst[0] = b'-';
        i += 1;

        let mut tmp = [0u8; 34];
        let mut coeff = self.coeff_to_str(&mut tmp);
        // SAFETY: `coeff_to_str` returns a subslice of `tmp`, so
        // the length of `coeff` must be in [0,34].
        unsafe { assume(coeff.len() <= 34) }

        if coeff.is_empty() {
            // All zero.
            coeff = &[b'0'];
            i += 1;
        } else {
            i += coeff.len();
        }
        // SAFETY: The length of `coeff` was previously in
        // [0,34]. If its length was zero, we just replaced it
        // with a slice of len == 1. Therefore, the length of
        // `coeff` is in [1,34].
        unsafe { assume(!coeff.is_empty() && coeff.len() <= 34) }

        // The adjusted exponent.
        let mut e = 0;
        // Number of digits before the '.'.
        //
        // Here, `coeff.len()` is in [1,34]. `exp` TODO
        #[allow(clippy::cast_possible_wrap)]
        let mut pre = (coeff.len() as i32) + exp;
        if exp > 0 || pre < -5 {
            // Exponential form
            e = pre - 1;
            pre = 1;
        }
        //println!("pre={pre}");

        let msd = self.msd();
        if msd != 0 {
            dst[i] = msd + b'0';
            i += 1;
        }

        // println!("i = {}", i - 1);
        // println!("? = {}", self.coeff_len());

        //println!("i={i}");

        // SAFETY: `buf` is large enough to hold all of the
        // decimal's declets.
        unsafe { assume(i < dst.len()) }

        //println!("exp={exp} {}", self.exp());

        if pre > 0 {
            // We just checked that `pre > 0`.
            #[allow(clippy::cast_sign_loss)]
            let dot = start + pre as usize;
            //println!("pre={pre} start={start} dot={dot} i={i}");
            if dot < i {
                //println!("pre={pre} i={i}");
                dst.copy_within(dot..i, dot + 1);
                dst[dot] = b'.';
                i += 1;
            }
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
                let w = util::itoa4(e as u16);
                dst[i..i + 4].copy_from_slice(&w.to_bytes());
                i += w.len();
            }

            let start = usize::from(self.is_sign_positive());
            // SAFETY: `buf` only ever contains UTF-8.
            return unsafe { str::from_utf8_unchecked(&dst[start..i]) };
        }

        // pre = -pre + 2;
        // let t = start + round_down4(i - start);

        // SAFETY: `buf` only ever contains UTF-8.
        return unsafe { str::from_utf8_unchecked(&dst[..i]) };
    }

    #[allow(clippy::indexing_slicing)]
    fn coeff_to_str(self, dst: &mut [u8]) -> &[u8] {
        //let dst = &mut dst[..34 + 1];

        let dpd = self.coeff();

        let mut i = 0;
        let mut shift = 100;
        loop {
            let declet = ((dpd >> shift) & 0x3ff) as u16;
            let s = dpd::unpack_to_str(declet);
            if i > 0 {
                dst[i..i + 4].copy_from_slice(&s.to_bytes());
                //println!("{i}..{} -> {} of {} shift={shift}", i + 4, i + 3, dst.len());
                i += 3;
            } else if s.len() > 0 {
                let n = s.len();
                dst[i..i + n].copy_from_slice(&s.to_bytes()[..n]);
                i += n;
            }
            if shift == 0 {
                break;
            }
            shift -= 10;
        }

        &dst[..i]
    }

    /*
    fn coeff_to_str(self, dst: &mut [u8], dot: Option<usize>) -> usize {
        let dst = &mut dst[..34 + 1];

        // The coefficient is at most 114 bits.
        let dpd = self.full_coeff() & (1 << 114) - 1;
        if dpd == 0 {
            dst[0] = b'0';
            return 1;
        }

        // Skip past the leading zeros. This prevents the
        // compiler from unrolling the loop, but simplifies the
        // BCD to string conversion code.
        let nlz = ((dpd.leading_zeros() - 14) + 9) / 10;
        let nd = Self::DIGITS - nlz; // # non-zero digits

        let mut shift = (nd / 3) * 10; // max 110

        // The first declet is special since it shouldn't have
        // leading zeros.
        let declet = ((dpd >> shift) & 0x3ff) as u16;
        let s = dpd::unpack_to_str(declet).trimmed();
        dst[..3].copy_from_slice(&s.to_bytes());
        let (_, rest) = dst.split_at_mut(s.len());

        let mut i = 0;
        while shift > 0 {
            shift -= 10;
            let declet = ((dpd >> shift) & 0x3ff) as u16;
            let s = dpd::unpack_to_str(declet);
            rest[i..i + 3].copy_from_slice(&s.to_bytes());
            i += 3;
        }
        nd as usize
    }
    */
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

#[inline(always)]
fn copy(dst: &mut [u8], src: &[u8]) -> usize {
    let n = src.len();
    // The caller must verify the length of `dst`
    #[allow(clippy::indexing_slicing)]
    dst[..n].copy_from_slice(src);
    n
}

const fn round_down4(v: usize) -> usize {
    v & !3
}

#[cfg(test)]
mod tests {
    use std::{ffi::CStr, ptr};

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
        // let got = d128::INFINITY;
        // println!("got={got}");

        let _got = d128::new(0, d128::MAX_EXP);
        // println!(" got={got}");

        // let x = d128::MAX_COEFF;
        // let x = 1234567890_1234567890_1234567890_1234i128;
        let x = 9_111_222_333_444_555_666_777_888_999_000_111;
        assert!(x <= d128::MAX_COEFF);

        let got = d128::new(x, d128::MAX_EXP);
        println!("exp={}", got.exp());
        println!(" got={got}");

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
        //println!("want={}", to_str(0, d128::MAX_EXP));
        //println!("want={}", to_str(d128::MAX_COEFF, d128::MAX_EXP));
        println!("want={}", to_str(x, d128::MAX_EXP));

        assert!(false);
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

    #[test]
    fn test_coeff_len() {
        let mut i = 1;
        while i < d128::DIGITS {
            let v = 10i128.pow(i);
            let got = d128::new(v - 1, 0).coeff_len();
            let want = v.ilog10() as usize;
            assert_eq!(got, want, "#{}", v - 1);
            i += 1;
        }
    }
}
