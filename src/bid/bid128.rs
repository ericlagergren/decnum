use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith128, base::impl_dec};
use crate::{
    conv::{self, ParseError},
    dpd::{self, Dpd128},
    util::{self, const_assert},
};

/// A 128-bit decimal floating point number.
///
/// (–1)^sign * coefficient * 10^exp
///
/// TODO: docs
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

impl_dec! {
    name = Bid128,
    ucoeff = u128,
    icoeff = i128,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u32,
    arith = arith128,
}

// To/from reprs.
impl Bid128 {
    /// Creates a `Bid128` from its coefficient and exponent.
    pub fn new2(coeff: i128, exp: i16) -> Self {
        let sign = coeff < 0;
        let coeff = coeff.unsigned_abs();
        if !Self::need_round(coeff, exp) {
            Self::from_parts(sign, exp, coeff)
        } else {
            Self::rounded2(sign, exp, coeff)
        }
    }

    fn rounded2(sign: bool, mut exp: i16, mut coeff: u128) -> Self {
        println!("rounded2: sign={sign} exp={exp} coeff={coeff}");

        // This method also works if we don't need to
        // round, but for performance reasons we always
        // check first.
        debug_assert!(Self::need_round(coeff, exp));

        let mut digits = arith128::digits(coeff) as i16;
        println!("digits={digits}");

        let mut drop = core::cmp::max(digits - Self::DIGITS as i16, Self::ETINY - exp);
        println!("drop={drop}");
        if drop > 0 {
            exp += drop;

            let mut d = 0;
            while drop > 0 {
                d = coeff % 10;
                coeff /= 10;
                digits -= 1;
                drop -= 1;
            }

            // Round half even: up if d > 5 or the new LSD is
            // odd.
            if d > 5 || (d == 5 && (coeff % 10) != 0) {
                // NB: This is where we'd mark inexact.
                coeff += 1;
                if coeff > Self::MAX_COEFF as u128 {
                    // We went from 999... to 100..., so chop off
                    // a trailing digit.
                    coeff /= 10;
                    digits -= 1;
                    exp += 1;
                }
            }
        }

        println!("digits={digits}");
        let adj = exp + (digits - 1);
        println!("exp = {exp}");
        println!("adj = {adj}");
        if exp < Self::EMIN && adj < Self::EMIN {
            // NB: This is where we'd mark underflow.
            if adj < Self::ETINY {
                // Subnormal < ETINY, so exp = ETINY and the coeff is
                // rounded.
                //
                // TODO(eric): Round to 0, don't hard code 0.
                return Self::from_parts(sign, Self::ETINY, 0);
            }
            debug_assert!(adj >= Self::ETINY);
        }
        debug_assert!(exp >= Self::EMIN);
        debug_assert!(adj >= Self::EMIN);

        if exp > Self::ADJ_EMAX {
            if coeff == 0 {
                println!("clamped to zero");
                exp = Self::ADJ_EMAX; // clamped
            } else if adj > Self::EMAX {
                println!("inf");
                // NB: This is where we'd mark overflow.
                return Self::inf(sign);
            } else {
                let shift = exp - (Self::EMAX - (Self::MAX_PREC - 1) as i16);
                println!("shift = {shift}");
                if shift > 0 {
                    coeff *= 10u128.pow(shift as u32);
                    exp -= shift;
                }
            }
        }
        debug_assert!(exp <= Self::EMAX);

        println!("exp={exp}");

        // adj is in [ETINY, EMAX].

        Self::from_parts(sign, exp, coeff)
    }

    /// Creates an infinity.
    pub(crate) const fn inf(sign: bool) -> Self {
        let bits = signbit(sign) | comb(0x1e000);
        Self::from_bits(bits)
    }

    /// Creates a quiet NaN.
    pub(crate) const fn nan(sign: bool, payload: u128) -> Self {
        debug_assert!(payload <= Self::PAYLOAD_MAX);

        let bits = signbit(sign) | comb(0x1f000) | payload;
        Self::from_bits(bits)
    }

    /// Creates a signaling NaN.
    pub(crate) const fn snan(sign: bool, payload: u128) -> Self {
        debug_assert!(payload <= Self::PAYLOAD_MAX);

        let bits = signbit(sign) | comb(0x1f800) | payload;
        Self::from_bits(bits)
    }

    /// Creates a zero.
    const fn zero() -> Self {
        Self::from_u64(0)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_i32(coeff: i32) -> Self {
        Self::from_i128(coeff as i128)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        Self::from_u128(coeff as u128)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_i64(coeff: i64) -> Self {
        Self::from_i128(coeff as i128)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u64(coeff: u64) -> Self {
        Self::from_u128(coeff as u128)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result may be rounded if `coeff` is less than
    /// [`MIN_COEFF`][Self::MIN_COEFF] or greater than
    /// [`MAX_COEFF`][Self::MAX_COEFF].
    pub const fn from_i128(coeff: i128) -> Self {
        Self::new(coeff, 0)
    }

    /// Creates a `Bid128` from `coeff` and an exponent of zero.
    ///
    /// The result may be rounded if `coeff` is less than
    /// [`MIN_COEFF`][Self::MIN_COEFF] or greater than
    /// [`MAX_COEFF`][Self::MAX_COEFF].
    pub const fn from_u128(coeff: u128) -> Self {
        if !Self::need_round(coeff, 0) {
            Self::from_parts(false, 0, coeff)
        } else {
            Self::rounded(false, 0, coeff)
        }
    }

    /// Converts the `Bid128` to a `Dpd128`.
    pub const fn to_dpd128(self) -> Dpd128 {
        if self.is_nan() {
            let payload = dpd::pack_bin_u113(self.payload());
            if self.is_snan() {
                Dpd128::snan(self.signbit(), payload)
            } else {
                Dpd128::nan(self.signbit(), payload)
            }
        } else if self.is_infinite() {
            Dpd128::inf(self.signbit())
        } else {
            Dpd128::from_parts_bin(self.signbit(), self.unbiased_exp(), self.coeff())
        }
    }

    /// Converts the `Dpd128` to a `Bid128`.
    pub const fn from_dpd128(dpd: Dpd128) -> Self {
        dpd.to_bid128()
    }
}

// Const arithmetic.
impl Bid128 {
    /// Returns `self + other`.
    ///
    /// This is the same as [`Add`][core::ops::Add], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_add(self, _rhs: Self) -> Self {
        todo!()
    }

    /// Returns `self / other`.
    ///
    /// This is the same as [`Div`][core::ops::Div], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_div(self, _rhs: Self) -> Self {
        todo!()
    }

    /// Returns `self * other`.
    ///
    /// This is the same as [`Mul`][core::ops::Mul], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_mul(self, _rhs: Self) -> Self {
        todo!()
    }

    /// Returns `self % other`.
    ///
    /// This is the same as [`Rem`][core::ops::Rem], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_rem(self, _rhs: Self) -> Self {
        todo!()
    }
}

// Misc.
impl Bid128 {
    /// TODO
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn set_exponent(self, _n: i16) -> Self {
        todo!()
    }
}

macro_rules! from_unsigned_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid128 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_u128(coeff as u128)
            }
        }
    )*)
}
from_unsigned_impl!(u8 u16 u32 u64 u128);

macro_rules! from_signed_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid128 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_i128(coeff as i128)
            }
        }
    )*)
}
from_signed_impl!(i8 i16 i32 i64 i128);

const fn signbit(sign: bool) -> u128 {
    (sign as u128) << Bid128::SIGN_SHIFT
}

const fn comb(bits: u32) -> u128 {
    debug_assert!(bits & !((1 << Bid128::COMB_BITS) - 1) == 0);

    (bits as u128) << Bid128::COMB_SHIFT
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dectest::dectests;

    dectests!(d128);

    impl Bid128 {
        const SNAN: Self = Self::snan(false, 0);
        const NEG_NAN: Self = Self::nan(true, 0);
        const NEG_SNAN: Self = Self::snan(true, 0);
    }

    #[test]
    fn test_idk() {
        let x = Dpd128::from_bits(0x7e7e7e7e7e7e7e7e7e7e7e7e7e7e7e7e);
        println!("dpd {x:?} {:x}", x.to_bits());

        let y = x.to_bid128();
        println!("bid {y:?} {:x}", y.to_bits());

        let z = y.to_dpd128();
        println!("dpd {z:?} {:x}", z.to_bits());

        println!("{}", x.payload_bin());
        println!("{}", y.payload());
        println!("{}", z.payload_bin());

        let got = z;
        let want = Dpd128::from_bits(0x7e003e7e7c7e7e7e7e7c7e7e7e7e7c7e);
        println!("want = {want:?} {:x}", want.to_bits());
        assert_eq!(got, want);

        assert!(false);
    }

    #[test]
    fn test_exp() {
        for mut want in Bid128::MIN_EXP..=Bid128::MAX_EXP {
            if want > Bid128::ADJ_EMAX {
                want = Bid128::ADJ_EMAX;
            }

            let d = Bid128::new2(0, want);
            let got = d.unbiased_exp();
            assert_eq!(got, want, "(1) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), 0, "#{want}");

            let d = Bid128::new2(Bid128::MAX_COEFF, want);
            let got = d.unbiased_exp();
            assert_eq!(got, want, "(2) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), Bid128::MAX_COEFF as u128, "#{want}");
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

    #[test]
    fn test_nan_is_canonical() {
        const BITS: u32 = Bid128::G - 6;
        const MAX: u32 = (1 << BITS) - 1;
        for x in [
            Bid128::nan(false, Bid128::PAYLOAD_MAX),
            Bid128::snan(false, Bid128::PAYLOAD_MAX),
        ] {
            let bits = x.to_bits();
            for exp in 0..=MAX {
                let g = (exp as u128) << (Bid128::SIGN_SHIFT - 6 - BITS);
                let got = Bid128::from_bits(bits | g);
                assert_eq!(exp == 0, got.is_canonical(), "#{exp}");
            }
        }
    }

    #[test]
    fn test_inf_is_canonical() {
        const BITS: u32 = Bid128::G - 5;
        const MAX: u32 = (1 << BITS) - 1;
        for coeff in [0, 1234, Bid128::COEFF_MASK] {
            for exp in 0..=MAX {
                let bits = Bid128::inf(false).to_bits();
                let g = (exp as u128) << (Bid128::SIGN_SHIFT - 5 - BITS);
                let got = Bid128::from_bits(bits | g | coeff);
                assert_eq!(exp == 0 && coeff == 0, got.is_canonical(), "#{exp}");
            }
        }
    }
}
