use core::{
    cmp::Ordering,
    fmt,
    mem::size_of,
    num::FpCategory,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::{self, FromStr},
};

use super::dpd;
use crate::{
    bid::Bid128,
    conv::{Buffer, Fmt, ParseError},
    util::{assume, const_assert},
};

/// A 128-bit decimal floating point number.
///
/// (–1)^sign * coefficient * 10^exp
///
/// TODO: docs
#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Dpd128(
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
const_assert!(size_of::<Dpd128>() == 128 / 8);

// Internal stuff.
impl Dpd128 {
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
            const_assert!(Dpd128::LIMIT < (1 << 14) - 1);

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
        const_assert!(Dpd128::LIMIT < i16::MAX as u16);
        const_assert!(i16::MAX - (Dpd128::LIMIT as i16) > Dpd128::BIAS);

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
        const_assert!(Dpd128::DIGITS <= i16::MAX as u32);

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
    const fn full_coeff(self) -> u128 {
        self.coeff() | ((self.msd() as u128) << 110)
    }

    pub(crate) const fn from_parts_bin(sign: bool, exp: i16, bin: u128) -> Self {
        debug_assert!(exp >= Self::MIN_EXP);
        debug_assert!(exp <= Self::MAX_EXP);
        debug_assert!(bin <= Self::MAX_COEFF as u128);

        let dpd = dpd::pack_bin_u113(bin);
        Self::from_parts_dpd(sign, exp, dpd)
    }

    const fn from_parts_dpd(sign: bool, exp: i16, dpd: u128) -> Self {
        debug_assert!(exp >= Self::MIN_EXP);
        debug_assert!(exp <= Self::MAX_EXP);

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
impl Dpd128 {
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
        const MASK1: u128 = (0x7 << Dpd128::COMB_SHIFT) | Dpd128::COEFF_MASK;
        // Covers MSD > 7 and specials.
        const MASK2: u128 = 0x18 << Dpd128::COMB_SHIFT;
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
        self.to_bid128().classify()
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
    pub fn const_eq(self, other: Self) -> bool {
        self.to_bid128().const_eq(other.to_bid128())
    }

    /// Returns the ordering between `self` and `other`.
    ///
    /// - If either number is NaN, it returns `None`.
    /// - +0.0 and -0.0 are considered equal.
    ///
    /// This is a const version of [`PartialOrd`].
    pub fn const_partial_cmp(self, other: Self) -> Option<Ordering> {
        self.to_bid128().const_partial_cmp(other.to_bid128())
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
        self.to_bid128().const_total_cmp(other.to_bid128())
    }
}

// To/from reprs.
impl Dpd128 {
    /// Creates a `d128` from its coefficient and exponent.
    pub const fn new(coeff: i128, exp: i16) -> Self {
        Bid128::new(coeff, exp).to_dpd128()
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
    /// let got = Dpd128::from_bits(0x2207c0000000000000000000000000a5);
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

    /// Creates a `Dpd128` from a big-endian byte array.
    pub const fn from_be_bytes(bytes: [u8; 16]) -> Self {
        Self::from_bits(u128::from_be_bytes(bytes))
    }

    /// Creates a `Dpd128` from a native-endian byte array.
    pub const fn from_ne_bytes(bytes: [u8; 16]) -> Self {
        Self::from_bits(u128::from_ne_bytes(bytes))
    }

    /// Creates a `Dpd128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        Self::from_u64(coeff as u64)
    }

    /// Creates a `Dpd128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u64(coeff: u64) -> Self {
        Self::from_parts_bin(false, 0, coeff as u128)
    }

    /// Raw transmutation to `u128`.
    pub const fn to_bits(self) -> u128 {
        self.0
    }

    /// Converts the `Dpd128` to a little-endian byte array.
    pub const fn to_le_bytes(self) -> [u8; 16] {
        self.0.to_le_bytes()
    }

    /// Converts the `Dpd128` to a big-endian byte array.
    pub const fn to_big_bytes(self) -> [u8; 16] {
        self.0.to_be_bytes()
    }

    /// Converts the `Dpd128` to a native-endian byte array.
    pub const fn to_ne_bytes(self) -> [u8; 16] {
        self.0.to_ne_bytes()
    }

    /// Converts the `Dpd128` to a `Bid128`.
    pub const fn to_bid128(self) -> Bid128 {
        let coeff = dpd::unpack_bin_u113(self.full_coeff());
        Bid128::from_parts(self.signbit(), self.unbiased_exp(), coeff)
    }
}

// Const arithmetic.
impl Dpd128 {
    /// Returns `self + other`.
    ///
    /// This is the same as [`Add`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_add(self, rhs: Self) -> Self {
        self.to_bid128().const_add(rhs.to_bid128()).to_dpd128()
    }

    /// Returns `self * other`.
    ///
    /// This is the same as [`Mul`], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_mul(self, rhs: Self) -> Self {
        self.to_bid128().const_mul(rhs.to_bid128()).to_dpd128()
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
impl Dpd128 {
    // const MAX_STR_LEN: usize = Self::DIGITS as usize + "-.E1234".len();

    /// Converts the decimal to a string.
    #[allow(clippy::indexing_slicing)]
    pub fn format(self, dst: &mut Buffer) -> &str {
        self.to_bid128().format(dst)
    }

    /// Parses a decimal from a string.
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        Bid128::parse(s).map(Bid128::to_dpd128)
    }
}

impl Add for Dpd128 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.const_add(rhs)
    }
}

impl AddAssign for Dpd128 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for Dpd128 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.const_mul(rhs)
    }
}

impl MulAssign for Dpd128 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for Dpd128 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.const_neg()
    }
}

impl Sub for Dpd128 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.const_sub(rhs)
    }
}

impl SubAssign for Dpd128 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl PartialEq for Dpd128 {
    fn eq(&self, other: &Self) -> bool {
        self.const_eq(*other)
    }
}

impl PartialOrd for Dpd128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.const_partial_cmp(*other)
    }
}

impl FromStr for Dpd128 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Dpd128::parse(s)
    }
}

impl fmt::Display for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::Default);
        write!(f, "{str}")
    }
}

impl fmt::Binary for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl fmt::LowerExp for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::LowerExp);
        write!(f, "{str}")
    }
}

impl fmt::UpperExp for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = Buffer::new();
        let str = buf.format(*self, Fmt::UpperExp);
        write!(f, "{str}")
    }
}

impl fmt::Debug for Dpd128 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decnumber::Quad;

    impl Dpd128 {
        const SNAN: Self = Self::snan(true);
        const NEG_NAN: Self = Self::nan(true);
        const NEG_SNAN: Self = Self::snan(true);
    }

    #[test]
    fn test_exp() {
        for exp in 0..=Dpd128::MAX_EXP {
            let d = Dpd128::new(0, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(1) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), 0, "#{exp}");

            let d = Dpd128::new(Bid128::MAX_COEFF, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(2) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), Bid128::MAX_COEFF as u128, "#{exp}");
        }
    }

    static STR_TESTS: &[(Dpd128, &'static str)] = &[
        (Dpd128::NAN, "NaN"),
        (Dpd128::INFINITY, "Infinity"),
        (Dpd128::NEG_INFINITY, "-Infinity"),
        (Dpd128::NAN, "NaN"),
        (Dpd128::SNAN, "sNaN"),
        (Dpd128::NEG_NAN, "-NaN"),
        (Dpd128::NEG_SNAN, "-sNaN"),
        (Dpd128::new(0, 0), "0"),
        (Dpd128::new(0, -1), "0.0"),
        (Dpd128::new(0, Dpd128::MAX_EXP), "0E+6111"),
        (Dpd128::new(0, Dpd128::MIN_EXP), "0E-6176"),
        (Dpd128::new(21, -1), "2.1"),
        (Dpd128::new(210, -2), "2.10"),
        (
            Dpd128::new(9111222333444555666777888999000111, Dpd128::MAX_EXP),
            "9.111222333444555666777888999000111E+6144",
        ),
        (
            Dpd128::new(9111222333444555666777888999000111, Dpd128::MIN_EXP),
            "9.111222333444555666777888999000111E-6143",
        ),
        (
            Dpd128::new(9111222333444555666777888999000111, 0),
            "9111222333444555666777888999000111",
        ),
        (
            Dpd128::new(9111222333444555666777888999000111, -2),
            "91112223334445556667778889990001.11",
        ),
        (
            Dpd128::new(9111222333444555666777888999000111, 2),
            "9.111222333444555666777888999000111E+35",
        ),
        (
            Dpd128::new(9999999999999999999999999999999999, -39),
            "0.000009999999999999999999999999999999999",
        ),
        (Dpd128::new(42, 1), "4.2E+2"),
        (Dpd128::new(42, 0), "42"),
        (Dpd128::new(42, -1), "4.2"),
        (Dpd128::new(42, -2), "0.42"),
        (Dpd128::new(42, -3), "0.042"),
        (Dpd128::new(42, -4), "0.0042"),
        (Dpd128::new(42, -5), "0.00042"),
        (Dpd128::new(42, -6), "0.000042"),
        (Dpd128::new(42, -7), "0.0000042"),
        (Dpd128::new(42, -8), "4.2E-7"),
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
            let got: Dpd128 = output.parse().unwrap();
            if got.is_nan() {
                continue;
            }
            assert_eq!(got, want, "#{i}: parse(\"{output}\") -> {want}");
            println!("");
        }
    }

    #[test]
    fn test_from_u32() {
        for x in 0..=u32::MAX {
            let got = Dpd128::from_u32(x);
            let want = Quad::from_u32(x);
            assert_eq!(got, want, "#{x}");
        }
    }

    #[test]
    fn test_digits() {
        for i in 1..Dpd128::DIGITS {
            let v = 10i128.pow(i);
            let got = Dpd128::new(v - 1, 0).digits();
            let want = v.ilog10();
            assert_eq!(got, want, "#{}", v - 1);
            println!();
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
            let x: Dpd128 = lhs.parse().unwrap();
            let y: Dpd128 = rhs.parse().unwrap();
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
        let lhs = Dpd128::new(1230, -1);
        let rhs = Dpd128::new(12300, -2);
        println!("lhs = {lhs} {}", lhs.unbiased_exp());
        println!("rhs = {rhs} {}", rhs.unbiased_exp());
    }
}
