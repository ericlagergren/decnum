use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith64, base::impl_dec};
use crate::{
    conv::{self, ParseError},
    dpd::Dpd128,
    util::{self, assume, const_assert},
};

/// A 128-bit decimal floating point number.
///
/// (–1)^sign * coefficient * 10^exp
///
/// TODO: docs
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Bid64(
    /// ## Form 1
    ///
    /// s 00eeeeee   (0)ttt tttttttttt tttttttttt
    /// s 01eeeeee   (0)ttt tttttttttt tttttttttt
    /// s 10eeeeee   (0)ttt tttttttttt tttttttttt
    ///
    /// ## Form 2
    ///
    /// s 1100eeeeee (100)t tttttttttt tttttttttt
    /// s 1101eeeeee (100)t tttttttttt tttttttttt
    /// s 1110eeeeee (100)t tttttttttt tttttttttt
    u64,
);
const_assert!(size_of::<Bid64>() == 64 / 8);

impl_dec! {
    name = Bid64,
    ucoeff = u64,
    icoeff = i64,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u16,
    arith = arith64,
}

// To/from reprs.
impl Bid64 {
    /// Creates an infinity.
    const fn inf(sign: bool) -> Self {
        let bits = signbit(sign) | comb(0x1e00);
        Self::from_bits(bits)
    }

    /// Creates a quiet NaN.
    const fn nan(sign: bool, payload: u64) -> Self {
        debug_assert!(payload <= Self::PAYLOAD_MAX);

        let bits = signbit(sign) | comb(0x1f00);
        Self::from_bits(bits)
    }

    /// Creates a signaling NaN.
    const fn snan(sign: bool, payload: u64) -> Self {
        debug_assert!(payload <= Self::PAYLOAD_MAX);

        let bits = signbit(sign) | comb(0x1f80);
        Self::from_bits(bits)
    }

    /// Creates a zero.
    const fn zero() -> Self {
        Self::from_u64(0)
    }

    /// Creates a `Bid64` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_i32(coeff: i32) -> Self {
        Self::from_i64(coeff as i64)
    }

    /// Creates a `Bid64` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        Self::from_u64(coeff as u64)
    }

    /// Creates a `Bid64` from `coeff` and an exponent of zero.
    ///
    /// The result may be rounded if `coeff` is less than
    /// [`MIN_COEFF`][Self::MIN_COEFF] or greater than
    /// [`MAX_COEFF`][Self::MAX_COEFF].
    pub const fn from_i64(coeff: i64) -> Self {
        Self::new(coeff, 0)
    }

    /// Creates a `Bid64` from `coeff` and an exponent of zero.
    ///
    /// The result may be rounded if `coeff` is less than
    /// [`MIN_COEFF`][Self::MIN_COEFF] or greater than
    /// [`MAX_COEFF`][Self::MAX_COEFF].
    pub const fn from_u64(coeff: u64) -> Self {
        if !Self::need_round(coeff, 0) {
            Self::from_parts(false, 0, coeff)
        } else {
            Self::rounded(false, 0, coeff)
        }
    }

    /// Converts the `Bid64` to a `Dpd128`.
    // TODO(eric): Change this to `to_dpd64`.
    pub const fn to_dpd128(self) -> Dpd128 {
        Dpd128::from_parts_bin(self.signbit(), self.unbiased_exp(), self.coeff() as u128)
    }

    /// TODO
    const fn rounded2(sign: bool, exp: i16, coeff: u64) -> Self {
        Self::rounded(sign, exp, coeff)
    }
}

// Const arithmetic.
impl Bid64 {
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

macro_rules! from_unsigned_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid64 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_u64(u64::from(coeff))
            }
        }
    )*)
}
from_unsigned_impl!(u8 u16 u32 u64);

macro_rules! from_signed_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid64 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_i64(i64::from(coeff))
            }
        }
    )*)
}
from_signed_impl!(i8 i16 i32 i64);

const fn signbit(sign: bool) -> u64 {
    (sign as u64) << Bid64::SIGN_SHIFT
}

const fn comb(bits: u16) -> u64 {
    debug_assert!(bits & !((1 << Bid64::COMB_BITS) - 1) == 0);

    (bits as u64) << Bid64::COMB_SHIFT
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decnumber::Quad;

    impl Bid64 {
        const SNAN: Self = Self::snan(false, 0);
        const NEG_NAN: Self = Self::nan(true, 0);
        const NEG_SNAN: Self = Self::snan(true, 0);
    }

    #[test]
    fn test_exp() {
        for exp in 0..=Bid64::MAX_EXP {
            let d = Bid64::new(0, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(1) d={:024b}", d.to_bits() >> (64 - 24));
            assert_eq!(d.coeff(), 0, "#{exp}");

            let d = Bid64::new(Bid64::MAX_COEFF, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(2) d={:024b}", d.to_bits() >> (64 - 24));
            assert_eq!(d.coeff(), Bid64::MAX_COEFF as u64, "#{exp}");
        }
    }

    static STR_TESTS: &[(Bid64, &'static str)] = &[
        // (Bid64::NAN, "NaN"),
        // (Bid64::NEG_NAN, "-NaN"),
        // (Bid64::SNAN, "sNaN"),
        // (Bid64::NEG_SNAN, "-sNaN"),
        // (Bid64::INFINITY, "Infinity"),
        // (Bid64::NEG_INFINITY, "-Infinity"),
        // (Bid64::new(0, 0), "0"),
        // (Bid64::new(0, -1), "0.0"),
        // (Bid64::new(0, Bid64::MAX_EXP), "0E+6111"),
        // (Bid64::new(0, Bid64::MIN_EXP), "0E-6176"),
        // (Bid64::new(21, -1), "2.1"),
        // (Bid64::new(210, -2), "2.10"),
        // (Bid64::new(42, 1), "4.2E+2"),
        // (Bid64::new(42, 0), "42"),
        // (Bid64::new(42, -1), "4.2"),
        // (Bid64::new(42, -2), "0.42"),
        // (Bid64::new(42, -3), "0.042"),
        // (Bid64::new(42, -4), "0.0042"),
        // (Bid64::new(42, -5), "0.00042"),
        // (Bid64::new(42, -6), "0.000042"),
        // (Bid64::new(42, -7), "0.0000042"),
        // (Bid64::new(42, -8), "4.2E-7"),
        // (
        //     Bid64::new(Bid64::MAX_COEFF, -39),
        //     "0.000009999999999999999999999999999999999",
        // ),
        // (Bid64::new(9999, Bid64::MIN_EXP), "1E-12287"),
        // (Bid64::new(0, Bid64::MAX_EXP), "1E+6145"),
        // (
        //     Bid64::new(10i64.pow(Bid64::DIGITS + 1) - 1, Bid64::MAX_EXP),
        //     "99999999999999999999999999999999999E+6144",
        // ),
        // (
        //     Bid64::new(10i64.pow(Bid64::DIGITS + 1) - 1, 0),
        //     "99999999999999999999999999999999999",
        // ),
        // (
        //     Bid64::new(10i64.pow(Bid64::DIGITS + 1) - 1, 36),
        //     "1.000000000000000000000000000000000E+37",
        // ),
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
            let q = Quad::parse(output);
            println!("q = {q}");
            let got: Bid64 = output.parse().unwrap();
            println!("got = {got}");
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
            let got = Bid64::from_u32(x);
            let want = Quad::from_u32(x);
            assert_eq!(got, want, "#{x}");
        }
    }

    #[test]
    fn test_digits() {
        for i in 1..Bid64::DIGITS {
            let v = 10i64.pow(i);
            let got = Bid64::new(v - 1, 0).digits();
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
            let x: Bid64 = lhs.parse().unwrap();
            let y: Bid64 = rhs.parse().unwrap();
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
        let lhs = Bid64::new(1230, -1);
        let rhs = Bid64::new(12300, -2);
        println!("lhs = {lhs} {}", lhs.unbiased_exp());
        println!("rhs = {rhs} {}", rhs.unbiased_exp());
    }
}
