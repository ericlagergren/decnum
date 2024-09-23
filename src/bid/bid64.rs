use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith::arith64, base::impl_dec};
use crate::{
    conv::{self, ParseError},
    util::{self, const_assert},
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
    dpd = crate::dpd::Dpd64,
    prefix = "dd",
}

// To/from reprs.
impl Bid64 {
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

#[cfg(test)]
mod tests {
    use super::*;

    mod dectests {
        use super::*;
        use crate::{
            dectest::{self, Default},
            dpd::Dpd64,
        };

        dectest::impl_backend!(Default<Bid64>, Bid64, Dpd64, u64);
        dectest::dectests!(d64 Default<Bid64>, "dd");
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

    // NB: This takes ~3.5 minutes on an Apple M1.
    #[test]
    #[cfg(feature = "slow-tests")]
    fn test_from_u32() {
        for x in 0..=u32::MAX {
            let got = Bid64::from_u32(x);
            let want = crate::decnumber::Quad::from_u32(x);
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
