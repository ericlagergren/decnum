use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith::arith32, base::impl_dec};
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
pub struct Bid32(
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
    u32,
);
const_assert!(size_of::<Bid32>() == 32 / 8);

impl_dec! {
    name = Bid32,
    ucoeff = u32,
    icoeff = i32,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u16,
    arith = arith32,
    dpd = crate::dpd::Dpd32,
    prefix = "ds",
}

// To/from reprs.
impl Bid32 {
    /// Creates a `Bid32` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_i32(coeff: i32) -> Self {
        Self::new(coeff, 0)
    }

    /// Creates a `Bid32` from `coeff` and an exponent of zero.
    ///
    /// The result is always exact.
    pub const fn from_u32(coeff: u32) -> Self {
        Self::CTX.maybe_rounded(false, 0, coeff)
    }
}

macro_rules! from_unsigned_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid32 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_u32(u32::from(coeff))
            }
        }
    )*)
}
from_unsigned_impl!(u8 u16 u32);

macro_rules! from_signed_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid32 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_i32(i32::from(coeff))
            }
        }
    )*)
}
from_signed_impl!(i8 i16 i32);

#[cfg(test)]
mod tests {
    use super::*;

    // mod dectests {
    //     use super::*;
    //     use crate::dectest::{self, Default};
    //
    //     dectest::impl_backend!(Default<Bid32>, Bid32, u32);
    //     dectest::dectests!(d32 Default<Bid32>, "ds");
    // }

    #[test]
    fn test_exp() {
        for exp in 0..=Bid32::MAX_EXP {
            let d = Bid32::new(0, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(1) d={:024b}", d.to_bits() >> (32 - 24));
            assert_eq!(d.coeff(), 0, "#{exp}");

            let d = Bid32::new(Bid32::MAX_COEFF, exp);
            let got = d.unbiased_exp();
            assert_eq!(got, exp, "(2) d={:024b}", d.to_bits() >> (32 - 24));
            assert_eq!(d.coeff(), Bid32::MAX_COEFF as u32, "#{exp}");
        }
    }

    // NB: This takes ~3.5 minutes on an Apple M1.
    #[test]
    #[cfg(feature = "slow-tests")]
    fn test_from_u32() {
        for x in 0..=u32::MAX {
            let got = Bid32::from_u32(x);
            let want = crate::decnumber::Quad::from_u32(x);
            assert_eq!(got, want, "#{x}");
        }
    }

    #[test]
    fn test_digits() {
        for i in 1..Bid32::DIGITS {
            let v = 10i32.pow(i);
            let got = Bid32::new(v - 1, 0).digits();
            let want = v.ilog10();
            assert_eq!(got, want, "#{}", v - 1);
        }
    }

    #[test]
    fn test_shift() {
        let lhs = Bid32::new(1230, -1);
        let rhs = Bid32::new(12300, -2);
        println!("lhs = {lhs} {}", lhs.unbiased_exp());
        println!("rhs = {rhs} {}", rhs.unbiased_exp());
    }
}
