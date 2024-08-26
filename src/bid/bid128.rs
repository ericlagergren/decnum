use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith128, base::impl_dec};
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
        // Fast path: `coeff` and `exp` are obviously valid.
        if !Self::need_round(coeff, exp) {
            return Self::from_parts(sign, exp, coeff);
        }

        // Slow path: we have to round.
        let mut digits = arith128::digits(coeff) as i16;
        println!("digits={digits}");

        let drop = core::cmp::max(digits - Self::DIGITS as i16, Self::ETINY - exp);
        println!("drop={drop}");
        if drop > 0 {
            exp += drop;

            let mut d = 0; // rounding
            while drop > 0 {
                d = coeff % 10;
                coeff /= 10;
                digits -= 1;
            }

            // Round half even: up if d > 5 or the new LSD is
            // odd.
            if d > 5 || (d == 5 && (coeff % 10) != 0) {
                // NB: This is where we'd mark inexact.
                coeff += 1;
                if coeff > Self::MAX_COEFF as u128 {
                    coeff /= 10;
                    digits -= 1;
                    exp += 1;
                }
            }
        }

        println!("digits={digits}");
        let adj = exp + (digits - 1);
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

        println!("exp = {exp}");
        println!("adj = {adj}");
        if exp > Self::ADJ_EMAX {
            if coeff == 0 {
                println!("zero");
                exp = Self::ADJ_EMAX; // clamped
            } else if adj > Self::EMAX {
                println!("inf");
                // NB: This is where we'd mark overflow.
                return Self::inf(sign);
            } else {
                let shift = exp + (Self::EMAX - (Self::MAX_PREC - 1) as i16);
                println!("shift = {shift}");
            }
        }
        debug_assert!(exp <= Self::EMAX);

        println!("exp={exp}");

        // adj is in [ETINY, EMAX].

        Self::from_parts(sign, exp, coeff)
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
        Dpd128::from_parts_bin(self.signbit(), self.unbiased_exp(), self.coeff())
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

    /// Returns `-self`.
    ///
    /// This is the same as [`Neg`][core::ops::Neg], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_neg(self) -> Self {
        Self(self.0 ^ Self::SIGN_MASK)
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

    /// Returns `self - other`.
    ///
    /// This is the same as [`Sub`][core::ops::Sub], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_sub(self, rhs: Self) -> Self {
        // x - y = x + -y
        self.const_add(rhs.const_neg())
    }
}

// Misc.
impl Bid128 {
    /// TODO
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn scaleb(self, n: u32) -> Self {
        if self.is_nan() {
            return self;
        }
        if n > Self::MAX_SCALEB_N {
            return Self::NAN;
        }
        if self.is_infinite() {
            return self;
        }
        let mut exp = self.biased_exp() + n as u16;
        if exp <= Self::LIMIT {
            return self.with_biased_exp(exp);
        }
        while exp >= Self::LIMIT {
            exp -= 1;
        }
        todo!()
    }

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
    use crate::decnumber::Quad;

    impl Bid128 {
        const SNAN: Self = Self::snan(false);
        const NEG_NAN: Self = Self::nan(true);
        const NEG_SNAN: Self = Self::snan(true);
    }

    #[test]
    fn test_idk() {
        let i = 0;
        let output = "9.111222333444555666777888999000111E+6144";
        let want = Bid128::new2(9111222333444555666777888999000111, 6111);
        let q = Quad::parse(output);
        assert_eq!(output, q.to_string(), "#{i}");
        println!("q = {q}");
        let got: Bid128 = output.parse().unwrap();
        if want.is_nan() {
            assert!(got.is_nan(), "#{i}: parse(\"{output}\") -> {want}");
        } else {
            assert_eq!(got, want, "#{i}: parse(\"{output}\") -> {want}");
        }
        println!("");
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

    static STR_TESTS: &[(&'static str, Bid128)] = &[
        ("NaN", Bid128::NAN),
        ("-NaN", Bid128::NEG_NAN),
        ("sNaN", Bid128::SNAN),
        ("-sNaN", Bid128::NEG_SNAN),
        ("Infinity", Bid128::INFINITY),
        ("-Infinity", Bid128::NEG_INFINITY),
        ("0", Bid128::new(0, 0)),
        ("0.0", Bid128::new(0, -1)),
        ("0E+6111", Bid128::new(0, Bid128::MAX_EXP)),
        ("0E-6143", Bid128::new(0, Bid128::MIN_EXP)),
        ("0E-6176", Bid128::new(0, Bid128::ETINY)),
        ("2.1", Bid128::new(21, -1)),
        ("2.10", Bid128::new(210, -2)),
        ("4.2E+2", Bid128::new(42, 1)),
        ("42", Bid128::new(42, 0)),
        ("4.2", Bid128::new(42, -1)),
        ("0.42", Bid128::new(42, -2)),
        ("0.042", Bid128::new(42, -3)),
        ("0.0042", Bid128::new(42, -4)),
        ("0.00042", Bid128::new(42, -5)),
        ("0.000042", Bid128::new(42, -6)),
        ("0.0000042", Bid128::new(42, -7)),
        ("4.2E-7", Bid128::new(42, -8)),
        (
            "9.111222333444555666777888999000111E+6144",
            Bid128::new(9111222333444555666777888999000111, 6111),
        ),
        (
            "9.111222333444555666777888999000111E-6143",
            Bid128::new(9111222333444555666777888999000111, -6176),
        ),
        (
            "9111222333444555666777888999000111",
            Bid128::new(9111222333444555666777888999000111, 0),
        ),
        (
            "91112223334445556667778889990001.11",
            Bid128::new(9111222333444555666777888999000111, -2),
        ),
        (
            "9.111222333444555666777888999000111E+35",
            Bid128::new(9111222333444555666777888999000111, 2),
        ),
        (
            "0.000009999999999999999999999999999999999",
            Bid128::new(Bid128::MAX_COEFF, -39),
        ),
        ("9.999E-6140", Bid128::new(9999, Bid128::MIN_EXP)),
        ("1E+6145", Bid128::INFINITY),
        (
            "99999999999999999999999999999999999E+6144",
            Bid128::new(10i128.pow(35) - 1, Bid128::MAX_EXP),
        ),
        (
            "99999999999999999999999999999999999",
            Bid128::new(10i128.pow(35) - 1, 0),
        ),
        (
            "1.000000000000000000000000000000000E+37",
            Bid128::new(1000000000000000000000000000000000, 4),
        ),
    ];

    #[test]
    fn test_parse() {
        for (i, &(input, want)) in STR_TESTS.iter().enumerate() {
            let got: Bid128 = input.parse().unwrap();
            if want.is_nan() {
                assert!(got.is_nan(), "#{i}: parse(\"{input}\") -> {want}");
            } else {
                assert_eq!(got, want, "#{i}: parse(\"{input}\") -> {want}");
            }
        }
    }

    #[test]
    fn test_format() {
        for (i, &(want, input)) in STR_TESTS.iter().enumerate() {
            // let q = Quad::parse(want);
            // assert_eq!(want, q.to_string(), "#{i}");
            // println!("q = {q}");
            let got = input.to_string();
            assert_eq!(got, want, "#{i}: format(\"{input:?}\") -> {want}");
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
