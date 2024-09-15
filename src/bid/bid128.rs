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
    prefix = "dq",
}

// To/from reprs.
impl Bid128 {
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
    pub const fn const_add(self, rhs: Self) -> Self {
        if self.is_special() || rhs.is_special() {
            if self.is_nan() || rhs.is_nan() {
                // ±NaN + rhs
                // self + ±NaN
                // ±NaN + ±NaN
                return Self::select_nan(self, rhs);
            }

            if self.is_infinite() {
                if rhs.is_infinite() && self.signbit() ^ rhs.signbit() {
                    // +inf + -inf
                    // -inf + +inf
                    return Self::nan(false, 0);
                }
                // ±inf + rhs
                // +inf + +inf
                // -inf + -inf
                return Self::inf(self.signbit());
            }
            debug_assert!(rhs.is_infinite());

            // self + ±inf
            return Self::inf(rhs.signbit());
        };

        // Both are now finite.
        debug_assert!(self.is_finite() && rhs.is_finite());

        if self.biased_exp() == rhs.biased_exp() {
            // Fast path: exponents are the same, so we don't
            // need to rescale either operand.
            let exp = self.unbiased_exp();

            let lhs = self.signed_coeff();
            let rhs = rhs.signed_coeff();

            let sum = lhs + rhs;
            let sign = if sum == 0 {
                // The sign of a zero is also zero unless
                // both operands are negative or the signs
                // differ and the rounding mode is
                // `ToNegativeInf`.
                lhs < 0 && rhs < 0
            } else {
                sum < 0
            };
            return Self::maybe_rounded(sign, exp, sum.unsigned_abs());
        }
        debug_assert!(self.biased_exp() != rhs.biased_exp());

        // The exponents differ, so one operand needs to be
        // rescaled.

        let mut lhs = self;
        let mut rhs = rhs;
        if lhs.biased_exp() < rhs.biased_exp() {
            lhs = rhs;
            rhs = self;
        }
        debug_assert!(rhs.biased_exp() < lhs.biased_exp());

        if lhs.is_zero() {
            // ±0 + rhs
            let mut sum = rhs.canonical();
            if lhs.signbit() ^ rhs.signbit() && sum.is_zero() {
                // If the signs differ and the result is
                // exactly zero, the result is positive
                // unless the rounding mode is to
                // `ToNegativeInf`.
                sum = sum.abs();
            }
            return sum;
        }
        debug_assert!(!lhs.is_zero());

        todo!()
    }

    /// Returns `self / other`.
    ///
    /// This is the same as [`Div`][core::ops::Div], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_div(self, rhs: Self) -> Self {
        self.quorem(rhs).0
    }

    /// Returns `self * other`.
    ///
    /// This is the same as [`Mul`][core::ops::Mul], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_mul(self, rhs: Self) -> Self {
        if self.is_finite() && rhs.is_finite() {
            todo!()
        }

        if self.is_nan() || rhs.is_nan() {
            // ±NaN + rhs
            // self + ±NaN
            // ±NaN + ±NaN
            return Self::select_nan(self, rhs);
        }

        if self.is_infinite() {
            if rhs.is_infinite() && self.signbit() ^ rhs.signbit() {
                // +inf + -inf
                // -inf + +inf
                return Self::nan(false, 0);
            }
            // ±inf + rhs
            // +inf + +inf
            // -inf + -inf
            return Self::inf(self.signbit());
        }
        // self + ±inf
        Self::inf(rhs.signbit())
    }

    /// Returns the quotient `q` and remainder `r` such that
    ///
    /// ```text
    /// q = self/other
    /// r = self%other
    /// ```
    ///
    /// This is the same as [`Div`][core::ops::Div] and
    /// [`Rem`][core::ops::Rem], but can be used in a const
    /// context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn quorem(self, rhs: Self) -> (Self, Self) {
        let sign = self.signbit() ^ rhs.signbit();

        if self.is_finite() && rhs.is_finite() {
            if self.is_zero() {
                if rhs.is_zero() {
                    // 0 / 0
                    let q = Self::nan(false, 0);
                    let r = q;
                    return (q, r);
                }
                // self / 0
                let q = Self::inf(sign);
                let r = Self::inf(self.signbit());
                return (q, r);
            }
            if rhs.is_zero() {
                // 0 / rhs
                let q = Self::from_parts(sign, 0, 0);
                let r =
                    Self::from_parts(self.signbit(), rhs.unbiased_exp() - self.unbiased_exp(), 0);
                return (q, r);
            }

            // self / rhs
            todo!()
        }

        if self.is_nan() || rhs.is_nan() {
            // ±NaN / rhs
            // self / ±NaN
            // ±NaN / ±NaN
            let q = Self::select_nan(self, rhs);
            let r = q;
            return (q, r);
        }

        if self.is_infinite() {
            if rhs.is_infinite() {
                // ±inf / ±inf
                let q = Self::nan(false, 0);
                let r = q;
                return (q, r);
            }
            // ±inf / rhs
            let q = Self::inf(sign);
            let r = Self::inf(self.signbit());
            (q, r)
        } else {
            // self / ±inf
            let q = Self::from_parts(sign, Self::ETINY, 0);
            let r = Self::from_parts(self.signbit(), 0, 0);
            (q, r)
        }
    }

    /// Returns `self % other`.
    ///
    /// This is the same as [`Rem`][core::ops::Rem], but can be
    /// used in a const context.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn const_rem(self, rhs: Self) -> Self {
        self.quorem(rhs).1
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

    /// TODO
    #[no_mangle]
    pub const fn test1(self, rhs: Self) -> bool {
        self.is_nan() || rhs.is_nan()
    }

    /// TODO
    #[no_mangle]
    pub const fn test2(self, rhs: Self) -> bool {
        (self.0 & rhs.0) & Self::COMB_TOP5 == Self::COMB_TOP5
    }
}

macro_rules! from_unsigned_impl {
    ($($ty:ty)*) => ($(
        impl From<$ty> for Bid128 {
            #[inline]
            fn from(coeff: $ty) -> Self {
                Self::from_u128(u128::from(coeff))
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
                Self::from_i128(i128::from(coeff))
            }
        }
    )*)
}
from_signed_impl!(i8 i16 i32 i64 i128);

const fn signbit(sign: bool) -> u128 {
    (sign as u128) << Bid128::SIGN_SHIFT
}

impl Bid128 {
    /// TODO
    #[no_mangle]
    pub const fn total_ord2(self, rhs: Self) -> Ordering {
        if self.signbit() != rhs.signbit() {
            return if self.signbit() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        Ordering::Equal
    }

    /// TODO
    #[no_mangle]
    const fn unpack(self) -> Unpacked {
        let sign = self.signbit();
        if self.is_finite() {
            let exp = self.unbiased_exp();
            let coeff = self.coeff();
            Unpacked::Finite { sign, exp, coeff }
        } else if self.is_snan() {
            Unpacked::SNaN { sign }
        } else if self.is_qnan() {
            Unpacked::QNaN { sign }
        } else {
            Unpacked::Infinite { sign }
        }
    }

    #[no_mangle]
    const fn coeff2(self) -> u128 {
        self.coeff()
    }

    #[no_mangle]
    const fn signed_coeff2(self) -> i128 {
        self.signed_coeff()
    }

    #[no_mangle]
    const fn plus2(self) -> Self {
        if self.is_nan() {
            // ±0 + ±NaN
            Self::nan(self.signbit(), self.payload())
        } else if self.is_infinite() {
            // ±0 + ±inf
            Self::inf(self.signbit())
        } else if self.is_zero() {
            // ±0 + ±0
            self.copy_abs()
        } else {
            // ±0 + self
            self
        }
    }

    #[no_mangle]
    const fn neg2(self) -> Self {
        self.const_neg()
    }

    #[no_mangle]
    const fn canonical2(self) -> Self {
        self.canonical()
    }
}

/// TODO
#[allow(dead_code, reason = "TODO")]
enum Unpacked {
    QNaN { sign: bool },
    SNaN { sign: bool },
    Infinite { sign: bool },
    Finite { sign: bool, exp: i16, coeff: u128 },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_idk() {
        let x = Bid128::parse("1.00000000000000000000000000000000E-6143").unwrap();
        println!("x = {x}");
        println!("x = {}", x.class());
        println!("special = {}", x.is_special());
        println!("zero = {}", x.is_zero());
        println!("adj = {}", x.adjusted_exp());
        println!("min = {}", Bid128::MIN_EXP);
        assert!(false);
    }

    #[test]
    fn test_exp() {
        for mut want in Bid128::MIN_EXP..=Bid128::MAX_EXP {
            if want > Bid128::EMAX_LESS_PREC {
                want = Bid128::EMAX_LESS_PREC;
            }

            let d = Bid128::new(0, want);
            let got = d.unbiased_exp();
            assert_eq!(got, want, "(1) d={:024b}", d.to_bits() >> (128 - 24));
            assert_eq!(d.coeff(), 0, "#{want}");

            let d = Bid128::new(Bid128::MAX_COEFF, want);
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
            let want = crate::decnumber::Quad::from_u32(x);
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

    #[test]
    fn test_special_ord() {
        let qnan = Bid128::nan(false, 0);
        let snan = Bid128::snan(false, 0);
        let inf = Bid128::inf(false);
        let max = Bid128::MAX;
        let min = Bid128::MIN;
        let zero = Bid128::zero();

        impl Bid128 {
            const fn sign_mag(self) -> i128 {
                let mut left = self.to_bits() as i128;
                left ^= (((left >> 127) as u128) >> 1) as i128;
                left
            }
        }

        println!("qNaN = {:>3}", qnan.special_bits());
        println!("sNaN = {:>3}", snan.special_bits());
        println!(" inf = {:>3}", inf.special_bits());
        println!(" max = {:>3}", max.special_bits());
        println!(" min = {:>3}", min.special_bits());
        println!("zero = {:>3}", zero.special_bits());

        println!("");

        println!("qNaN = {:>39}", qnan.to_bits());
        println!("sNaN = {:>39}", snan.to_bits());
        println!(" inf = {:>39}", inf.to_bits());
        println!(" max = {:>39}", max.to_bits());
        println!(" min = {:>39}", min.to_bits());
        println!("zero = {:>39}", zero.to_bits());

        println!("");

        println!("qNaN = {:>39}", qnan.sign_mag());
        println!("sNaN = {:>39}", snan.sign_mag());
        println!(" inf = {:>39}", inf.sign_mag());
        println!(" max = {:>39}", max.sign_mag());
        println!(" min = {:>39}", min.sign_mag());
        println!("zero = {:>39}", zero.sign_mag());

        assert!(false);
    }
}
