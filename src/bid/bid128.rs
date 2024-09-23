use core::{cmp::Ordering, fmt, mem::size_of, num::FpCategory, str};

use super::{arith::arith128, base::impl_dec};
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
    dpd = crate::dpd::Dpd128,
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
    const fn biased_exp2(self) -> u16 {
        let mut exp = self.0 >> Self::FORM1_EXP_SHIFT;
        if self.is_form2() {
            exp >>= 2;
        }
        (exp as u16) & Self::EXP_MASK
    }

    #[no_mangle]
    const fn biased_exp3(self) -> u16 {
        if self.is_form1() {
            // exp = G[0:w+1]
            ((self.0 & Self::FORM1_EXP_MASK) >> Self::FORM1_EXP_SHIFT) as u16
        } else {
            // exp = G[2:w+3]
            ((self.0 & Self::FORM2_EXP_MASK) >> Self::FORM2_EXP_SHIFT) as u16
        }
    }

    #[no_mangle]
    const fn test_quantize(self, rhs: Self) -> Self {
        Self::new(0, rhs.unbiased_exp())
    }

    #[no_mangle]
    const fn test_from_u64(x: u64) -> Self {
        Self::from_u64(x)
    }

    #[no_mangle]
    const fn test_from_i64(x: i64) -> Self {
        Self::from_i64(x)
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

    mod dectests {
        use super::*;
        use crate::{
            dectest::{self, Default},
            dpd::Dpd128,
        };

        dectest::impl_backend!(Default<Bid128>, Bid128, Dpd128, u128);
        dectest::dectests!(d128 Default<Bid128>, "dq");
    }

    #[test]
    fn test_idk() {
        let x = Bid128::parse("9.999999999999999999999999999999999E+6144").unwrap();
        let y = x.to_dpd();
        println!("x {:0128b}", x);
        println!("y {:0128b}", y);
        println!("x = {} {:016b} {x:?}", x.biased_exp(), x.biased_exp());
        println!("y = {} {:016b} {y:?}", y.biased_exp(), y.biased_exp());
        //println!("z = {:?}", y.to_bid());
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
        let mid = Bid128::new(Bid128::MAX_COEFF / 2, Bid128::EMAX_LESS_PREC / 2);
        let zero = Bid128::zero();

        // impl Bid128 {
        //     const fn sign_mag(self) -> i128 {
        //         let mut left = self.to_bits() as i128;
        //         left ^= (((left >> 127) as u128) >> 1) as i128;
        //         left
        //     }
        // }

        let got = crate::bid::util::const_cmp_u8(snan.special_ord(), qnan.special_ord());
        println!("got = {got:?}");

        println!("qNaN = {:08b}", qnan.special_bits());
        println!("sNaN = {:08b}", snan.special_bits());
        println!(" inf = {:08b}", inf.special_bits());
        println!(" max = {:08b}", max.special_bits());
        println!(" min = {:08b}", min.special_bits());
        println!(" mid = {:08b}", mid.special_bits());
        println!("zero = {:08b}", zero.special_bits());

        println!("");

        println!("qNaN = {:>3}", qnan.special_bits());
        println!("sNaN = {:>3}", snan.special_bits());
        println!(" inf = {:>3}", inf.special_bits());
        println!(" max = {:>3}", max.special_bits());
        println!(" min = {:>3}", min.special_bits());
        println!(" mid = {:>3}", mid.special_bits());
        println!("zero = {:>3}", zero.special_bits());

        println!("");

        println!("qNaN = {:08b}", qnan.special_ord());
        println!("sNaN = {:08b}", snan.special_ord());
        println!(" inf = {:08b}", inf.special_ord());
        println!(" max = {:08b}", max.special_ord());
        println!(" min = {:08b}", min.special_ord());
        println!(" mid = {:08b}", mid.special_ord());
        println!("zero = {:08b}", zero.special_ord());

        println!("");

        println!("qNaN = {:>3}", qnan.special_ord());
        println!("sNaN = {:>3}", snan.special_ord());
        println!(" inf = {:>3}", inf.special_ord());
        println!(" max = {:>3}", max.special_ord());
        println!(" min = {:>3}", min.special_ord());
        println!(" mid = {:>3}", mid.special_ord());
        println!("zero = {:>3}", zero.special_ord());

        // println!("qNaN = {:>39}", qnan.to_bits());
        // println!("sNaN = {:>39}", snan.to_bits());
        // println!(" inf = {:>39}", inf.to_bits());
        // println!(" max = {:>39}", max.to_bits());
        // println!(" min = {:>39}", min.to_bits());
        // println!("zero = {:>39}", zero.to_bits());

        // println!("");

        // println!("qNaN = {:>39}", qnan.sign_mag());
        // println!("sNaN = {:>39}", snan.sign_mag());
        // println!(" inf = {:>39}", inf.sign_mag());
        // println!(" max = {:>39}", max.sign_mag());
        // println!(" min = {:>39}", min.sign_mag());
        // println!("zero = {:>39}", zero.sign_mag());

        assert!(false);
    }
}
