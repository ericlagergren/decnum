use core::{cmp::Ordering, fmt, mem::size_of};

use super::encoding as dpd;
use crate::{
    bid::Bid128,
    util::{assume, const_assert},
};

/// TODO: docs
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Dpd128(u128);
const_assert!(size_of::<Dpd128>() == 128 / 8);

// Internal stuff.
impl Dpd128 {
    const BIAS: i16 = Bid128::BIAS;
    const LIMIT: u16 = Bid128::LIMIT;
    const EMAX: i16 = Bid128::EMAX;
    const EMIN: i16 = Bid128::EMIN;

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

    const COEFF_MASK: u128 = (1 << 110) - 1;

    const PAYLOAD_MASK: u128 = Self::COEFF_MASK;

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

    /// Returns the coefficient, less the MSD, as a DPD.
    const fn coeff(self) -> u128 {
        debug_assert!(self.is_finite());

        self.0 & Self::COEFF_MASK
    }

    /// Returns the coefficient, including the MSD, as a DPD.
    const fn full_coeff(self) -> u128 {
        self.coeff() | ((self.msd() as u128) << 110)
    }

    /// Returns the full coefficient as a binary number.
    const fn full_coeff_bin(self) -> u128 {
        dpd::unpack_bin_u113(self.full_coeff())
    }

    /// Returns the payload.
    const fn payload(self) -> u128 {
        debug_assert!(self.is_nan());

        self.0 & Self::PAYLOAD_MASK
    }

    /// Returns the payload as a binary number.
    pub(crate) const fn payload_bin(self) -> u128 {
        dpd::unpack_bin_u113(self.payload())
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
    /// The largest allowed coefficient.
    const MAX_COEFF: i128 = 10i128.pow(34) - 1;

    /// The maximum allowed exponent.
    const MAX_EXP: i16 = Self::EMAX - Self::MAX_PREC + 1;

    /// The smallest allowed exponent.
    const MIN_EXP: i16 = Self::EMIN - Self::MAX_PREC + 1;

    /// Reports whether the number is neither infinite nor NaN.
    const fn is_finite(self) -> bool {
        self.comb().is_finite()
    }

    /// Reports whether the number is either positive or negative
    /// infinity.
    const fn is_infinite(self) -> bool {
        self.comb().is_infinite()
    }

    /// Reports whether the number is a NaN.
    const fn is_nan(self) -> bool {
        self.comb().is_nan()
    }

    /// Reports whether the number is a signaling NaN.
    const fn is_snan(self) -> bool {
        // When the number is a NaN, the first exponent
        // continuation bit signals whether the NaN is signaling.
        self.is_nan() && self.econ() >> (Self::ECON_BITS - 1) == 1
    }
}

// To/from reprs.
impl Dpd128 {
    /// Creates a quiet NaN.
    pub(crate) const fn nan(sign: bool, payload: u128) -> Self {
        Self::from_fields(sign, 0x1f, 0, payload)
    }

    /// Creates a signaling NaN.
    pub(crate) const fn snan(sign: bool, payload: u128) -> Self {
        Self::from_fields(sign, 0x1f, 0x800, payload)
    }

    /// Creates an infinity.
    pub(crate) const fn inf(sign: bool) -> Self {
        Self::from_fields(sign, 0x1e, 0, 0)
    }

    /// Creates a `d128` from its raw bits.
    ///
    /// ```rust
    /// use rdfp::d128;
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
    /// use rdfp::d128;
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
        if self.is_nan() {
            if self.is_snan() {
                Bid128::snan(self.signbit(), self.payload_bin())
            } else {
                Bid128::nan(self.signbit(), self.payload_bin())
            }
        } else if self.is_infinite() {
            Bid128::inf(self.signbit())
        } else {
            Bid128::from_parts(self.signbit(), self.unbiased_exp(), self.full_coeff_bin())
        }
    }

    /// Converts the `Bid128` to a `Dpd128`.
    pub const fn from_bid128(bid: Bid128) -> Self {
        bid.to_dpd128()
    }
}

impl PartialEq for Dpd128 {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self.to_bid128(), &other.to_bid128())
    }
}

impl PartialOrd for Dpd128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.to_bid128(), &other.to_bid128())
    }
}

impl fmt::Display for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_bid128().fmt(f)
    }
}

impl fmt::Binary for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl fmt::LowerExp for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_bid128().fmt(f)
    }
}

impl fmt::UpperExp for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_bid128().fmt(f)
    }
}

impl fmt::Debug for Dpd128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sign = u8::from(self.signbit());
        if self.is_nan() {
            write!(f, "[{sign},")?;
            if self.is_snan() {
                write!(f, "s")?;
            } else {
                write!(f, "q")?;
            }
            write!(f, "NaN")?;
            if self.payload() != 0 {
                write!(f, ",{}", self.payload_bin())?;
            }
            write!(f, "]")
        } else if self.is_infinite() {
            write!(f, "[{sign},inf]")
        } else {
            write!(
                f,
                "[{sign},{},{}]",
                self.full_coeff_bin(),
                self.unbiased_exp(),
                // TODO(eric): form
            )
        }
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
