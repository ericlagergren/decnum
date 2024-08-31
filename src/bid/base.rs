macro_rules! impl_dec {
    (
        name = $name:ident,
        ucoeff = $ucoeff:ty,
        icoeff = $icoeff:ty,
        biased_exp = $biased:ty,
        unbiased_exp = $unbiased:ty,
        comb = $comb:ty,
        arith = $arith:ident $(,)?
    ) => {
        $crate::bid::base::impl_dec_internal!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_pub!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_impls!($name);
        $crate::bid::dtoa::impl_dtoa!($name, $arith);
        $crate::bid::atod::impl_atod!($name, $ucoeff, $unbiased, $arith);
    };
}
pub(crate) use impl_dec;

macro_rules! impl_dec_internal {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        // Internal stuff.
        impl $name {
            const K: u32 = (size_of::<$name>() * 8) as u32;
            const S: u32 = 1;
            const W: u32 = Self::K / 16 + 4;
            const G: u32 = Self::W + 5;
            const T: u32 = 15 * (Self::K / 16) - 10;
            const P: u32 = 9 * (Self::K / 32) - 2;

            const BYTES: usize = (Self::K / 8) as usize;

            /// The bias added to the encoded exponent in order to
            /// convert it to the "actual" exponent.
            const BIAS: $unbiased = Self::EMAX + (Self::P as $unbiased) - 2;

            /// The maxmimum value of the biased encoded exponent.
            const LIMIT: $biased = (3 * (1 << Self::W)) - 1;

            /// The maximum allowed unbiased exponent.
            const EMAX: $unbiased = 3 * (1 << (Self::W - 1));

            /// The minimum allowed unbiased exponent for
            /// a normal value.
            const EMIN: $unbiased = 1 - Self::EMAX;

            /// The minimum unbiased exponent for a subnormal
            /// value.
            const ETINY: $unbiased = Self::EMIN - ((Self::P as $unbiased) - 1);

            /// The maximum adjusted exponent.
            const ADJ_EMAX: $unbiased = Self::MAX_EXP - ((Self::MAX_PREC as $unbiased) - 1);

            /// The maximum adjusted exponent.
            const ADJ_EMIN: $unbiased = Self::MIN_EXP - ((Self::MAX_PREC as $unbiased) - 1);

            const MAX_PREC: u32 = Self::P;

            const SIGN_SHIFT: u32 = Self::K - Self::S;
            const SIGN_MASK: $ucoeff = 1 << Self::SIGN_SHIFT;

            const COMB_BITS: u32 = Self::G;
            const COMB_SHIFT: u32 = Self::K - Self::S - Self::G;

            // Top N bits of the combination field.
            const COMB_TOP2: $ucoeff = 0x3 << (Self::SIGN_SHIFT - 2);
            const COMB_TOP4: $ucoeff = 0xf << (Self::SIGN_SHIFT - 4);
            const COMB_TOP5: $ucoeff = 0x1f << (Self::SIGN_SHIFT - 5);
            const COMB_TOP6: $ucoeff = 0x3f << (Self::SIGN_SHIFT - 6);

            const EXP_BITS: u32 = Self::W + 2;
            const EXP_MASK: $biased = (1 << Self::EXP_BITS) - 1;

            const FORM1_EXP_MASK: $ucoeff = (Self::EXP_MASK as $ucoeff) << Self::FORM1_EXP_SHIFT;
            const FORM1_EXP_SHIFT: u32 = Self::SIGN_SHIFT - Self::EXP_BITS;

            const FORM2_EXP_MASK: $ucoeff = Self::FORM1_EXP_MASK >> 2;
            const FORM2_EXP_SHIFT: u32 = Self::FORM1_EXP_SHIFT + 2;

            /// The number of bits in the form one coefficient.
            const FORM1_COEFF_BITS: u32 = 3 + Self::T;
            /// Gathers the bits in the form one coefficient.
            const FORM1_COEFF_MASK: $ucoeff = (1 << Self::FORM1_COEFF_BITS) - 1;

            /// The number of bits in the form two coefficient.
            const FORM2_COEFF_BITS: u32 = 1 + Self::T;
            /// Gathers the bits in the form two coefficient.
            const FORM2_COEFF_MASK: $ucoeff = (1 << Self::FORM2_COEFF_BITS) - 1;
            /// The implicit bits in the form two coefficient.
            const FORM2_IMPLICIT_COEFF_BITS: $ucoeff = 0x8 << Self::T;

            /// The number of bits required to represent
            /// [`MAX_COEFF`][Self::MAX_COEFF].
            const MAX_COEFF_BITS: u32 = super::$arith::bitlen(Self::MAX_COEFF as $ucoeff);
            const MAX_COEFF_MASK: $ucoeff = (1 << Self::MAX_COEFF_BITS) - 1;

            const COEFF_BITS: u32 = Self::T;
            const COEFF_MASK: $ucoeff = (1 << Self::COEFF_BITS) - 1;

            const PAYLOAD_MASK: $ucoeff = Self::COEFF_MASK;

            const MAX_SCALEB_N: u32 = 2 * (Self::EMAX as u32 + Self::MAX_PREC);

            const fn signbit(self) -> bool {
                (self.0 & Self::SIGN_MASK) != 0
            }

            /// Is this form one?
            const fn is_form1(self) -> bool {
                self.0 & Self::COMB_TOP2 != Self::COMB_TOP2
            }

            /// Is this form two?
            const fn is_form2(self) -> bool {
                !self.is_form1()
            }

            /// Returns the biased exponment.
            ///
            /// If the number is finite, the result is in [0,
            /// [`LIMIT`][Self::LIMIT]].
            const fn biased_exp(self) -> $biased {
                // The exponent only has meaning for finite numbers.
                debug_assert!(self.is_finite());

                let exp = if self.is_form2() {
                    // exp = G[2:w+3]
                    ((self.0 & Self::FORM2_EXP_MASK) >> Self::FORM2_EXP_SHIFT) as $biased
                } else {
                    // exp = G[0:w+1]
                    ((self.0 & Self::FORM1_EXP_MASK) >> Self::FORM1_EXP_SHIFT) as $biased
                };
                debug_assert!(exp & !Self::EXP_MASK == 0);
                debug_assert!(exp <= Self::LIMIT);

                exp
            }

            /// Returns the unbiased exponent.
            ///
            /// If the number is finite, the result is in
            /// [[`ETINY`][Self::ETINY], [`EMAX`][Self::EMAX]].
            const fn unbiased_exp(self) -> $unbiased {
                const_assert!($name::LIMIT < <$unbiased>::MAX as $biased);
                const_assert!(<$unbiased>::MAX - ($name::LIMIT as $unbiased) > $name::BIAS);

                // The exponent only has meaning for finite numbers.
                debug_assert!(self.is_finite());

                // `self.biased_exp()` is in [0, LIMIT] and
                // `LIMIT < <$unbiased>::MAX`, so the cast cannot
                // wrap.
                //
                // The subtraction cannot wrap since
                //    LIMIT + BIAS < <$unbiased>::MAX
                //    0 - BIAS > <$unbiased>::MIN
                #[allow(clippy::cast_possible_wrap)]
                let exp = (self.biased_exp() as $unbiased) - Self::BIAS;

                if self.is_finite() {
                    // SAFETY: `self.unbiased_exp()` returns an
                    // integer in [0, LIMIT]. Subtracting `BIAS`
                    // TODO
                    unsafe {
                        assume(exp >= Self::ETINY);
                        assume(exp <= Self::EMAX);
                    }
                }
                exp
            }

            /// Returns the adjusted exponent.
            ///
            /// This is `exp + digits - 1`.
            const fn adjusted_exp(self) -> $unbiased {
                // The exponent only has meaning for finite numbers.
                debug_assert!(self.is_finite());

                const_assert!($name::DIGITS <= <$unbiased>::MAX as u32);
                // `self.digits() as $unbiased` does not wrap
                // because it is in [1, DIGITS], and `DIGITS <=
                // <$unbiased>::MAX`.
                #[allow(clippy::cast_possible_wrap)]
                let digits = self.digits() as $unbiased;

                self.unbiased_exp() + digits - 1
            }

            /// Returns the full coefficient.
            const fn coeff(self) -> $ucoeff {
                // The coefficient only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                let coeff = if self.is_form2() {
                    // 100 || G[w+4] || T
                    Self::FORM2_IMPLICIT_COEFF_BITS | (self.0 & Self::FORM2_COEFF_MASK)
                } else {
                    // G[w+2:w+4] || T
                    self.0 & Self::FORM1_COEFF_MASK
                };

                // See 3.2(c)(2).
                if coeff > Self::MAX_COEFF as $ucoeff {
                    0
                } else {
                    coeff
                }
            }

            /// Returns a NaN's diagnostic information.
            const fn diagnostic(self) -> $ucoeff {
                // The coefficient only has meaning for NaNs.
                debug_assert!(self.is_nan());

                self.0 & Self::PAYLOAD_MASK
            }

            const fn with_biased_exp(mut self, exp: $biased) -> Self {
                debug_assert!(exp <= Self::LIMIT);

                if self.is_form1() {
                    self.0 &= !Self::FORM1_EXP_MASK;
                    self.0 |= (exp as $ucoeff) << Self::FORM1_EXP_SHIFT;
                } else {
                    self.0 &= !Self::FORM2_EXP_MASK;
                    self.0 |= (exp as $ucoeff) << Self::FORM2_EXP_SHIFT;
                }
                self
            }

            /// Creates a rounded number.
            const fn rounded(sign: bool, mut exp: $unbiased, mut coeff: $ucoeff) -> Self {
                // This method also works if we don't need to
                // round, but for performance reasons we always
                // check first.
                debug_assert!(Self::need_round(coeff, exp));

                const fn max(x: $unbiased, y: $unbiased) -> $unbiased {
                    if x < y {
                        y
                    } else {
                        x
                    }
                }

                let mut digits = $arith::digits(coeff) as $unbiased;
                let mut drop = max(digits - Self::DIGITS as i16, Self::ETINY - exp);
                if drop > 0 {
                    exp += drop;

                    let mut d = 0;
                    while drop > 0 {
                        d = coeff % 10;
                        coeff /= 10;
                        digits -= 1;
                        drop -= 1;
                    }

                    // Round half even: up if d > 5 or the new
                    // LSD is odd.
                    if d > 5 || (d == 5 && (coeff % 10) != 0) {
                        // NB: This is where we'd mark inexact.
                        coeff += 1;
                        if coeff > Self::MAX_COEFF as $ucoeff {
                            // We went from 999... to 100..., so
                            // chop off a trailing digit.
                            coeff /= 10;
                            digits -= 1;
                            exp += 1;
                        }
                    }
                }

                let adj = exp + (digits - 1);
                if exp < Self::EMIN && adj < Self::EMIN {
                    // NB: This is where we'd mark underflow.
                    if adj < Self::ETINY {
                        // Subnormal < ETINY, so exp = ETINY and
                        // the coeff is rounded.
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
                        exp = Self::ADJ_EMAX; // clamped
                    } else if adj > Self::EMAX {
                        // NB: This is where we'd mark overflow.
                        return Self::inf(sign);
                    } else {
                        let shift = exp - (Self::EMAX - (Self::MAX_PREC - 1) as i16);
                        if shift > 0 {
                            coeff *= (10 as $ucoeff).pow(shift as u32);
                            exp -= shift;
                        }
                    }
                }
                debug_assert!(adj <= Self::EMAX);

                // adj is in [ETINY, EMAX].

                Self::from_parts(sign, exp, coeff)
            }

            /// Does `(coeff, exp)` need to be rounded?
            const fn need_round(coeff: $ucoeff, exp: $unbiased) -> bool {
                coeff > Self::MAX_COEFF as $ucoeff || exp < Self::ADJ_EMIN || exp > Self::ADJ_EMAX
            }

            /// Creates a finite number from the sign, unbiased
            /// exponent, an coefficient.
            pub(crate) const fn from_parts(sign: bool, exp: $unbiased, coeff: $ucoeff) -> Self {
                debug_assert!(coeff <= Self::MAX_COEFF as $ucoeff);
                debug_assert!(exp >= Self::ADJ_EMIN);
                debug_assert!(exp <= Self::ADJ_EMAX);
                debug_assert!(!Self::need_round(coeff, exp));

                // TODO(eric): If `exp` is valid then this cannot
                // overflow. Maybe make sure of it?
                #[allow(clippy::cast_sign_loss)]
                let biased = (exp + Self::BIAS) as $biased;

                let mut bits = 0;
                if Self::need_form2(coeff) {
                    // s 1100eeeeee (100)t tttttttttt tttttttttt
                    // s 1101eeeeee (100)t tttttttttt tttttttttt
                    // s 1110eeeeee (100)t tttttttttt tttttttttt
                    bits |= signbit(sign);
                    bits |= Self::COMB_TOP2;
                    bits |= (biased as $ucoeff) << Self::FORM2_EXP_SHIFT;
                    bits |= coeff & Self::FORM2_COEFF_MASK;
                } else {
                    // s 00eeeeee   (0)ttt tttttttttt tttttttttt
                    // s 01eeeeee   (0)ttt tttttttttt tttttttttt
                    // s 10eeeeee   (0)ttt tttttttttt tttttttttt
                    bits |= signbit(sign);
                    bits |= (biased as $ucoeff) << Self::FORM1_EXP_SHIFT;
                    bits |= coeff & Self::FORM1_COEFF_MASK;
                }
                Self::from_bits(bits)
            }

            // Do we need to use form two?
            const fn need_form2(coeff: $ucoeff) -> bool {
                // Form one is 3+T bits with an implicit leading 0b0.
                // Form two is 4+T bits with an implicit leading 0b100.
                if Self::MAX_COEFF_BITS <= Self::FORM1_COEFF_BITS {
                    // The max coefficient fits in 3+T bits, so
                    // we don't need form 2.
                    false
                } else {
                    // Is the MSB set (implying we need bit 4)?
                    (coeff >> (Self::MAX_COEFF_BITS - 1)) & 0x1 != 0
                }
            }
        }
    };
}
pub(crate) use impl_dec_internal;

macro_rules! impl_dec_pub {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        // Misc.
        impl $name {
            /// The largest value that can be represented by this
            /// type.
            pub const MAX: Self = Self::new(Self::MAX_COEFF, Self::MAX_EXP);

            /// The smallest value that can be represented by
            /// this type.
            pub const MIN: Self = Self::new(Self::MIN_COEFF, Self::MAX_EXP);

            /// The smallest positive value that can be
            /// represented by this type.
            pub const MIN_POSITIVE: Self = Self::new(Self::MAX_COEFF, Self::MIN_EXP);

            /// The largest allowed coefficient.
            pub const MAX_COEFF: $icoeff = (10 as $icoeff).pow(Self::DIGITS) - 1;

            /// The smallestallowed coefficient.
            pub const MIN_COEFF: $icoeff = -Self::MAX_COEFF;

            /// The maximum allowed exponent.
            pub const MAX_EXP: $unbiased = Self::EMAX;

            /// The smallest allowed exponent.
            pub const MIN_EXP: $unbiased = Self::EMIN;

            /// The number of base 10 significant digits.
            pub const DIGITS: u32 = Self::MAX_PREC;

            /// Not a Number (NaN).
            ///
            /// # Note
            ///
            /// Do not use this constant to determine whether
            /// a number is NaN. Use [`is_nan`][Self::is_nan]
            /// instead.
            pub const NAN: Self = Self::nan(false);

            /// Infinity (∞).
            ///
            /// # Note
            ///
            /// Do not use this constant to determine whether
            /// a number is infinity. Use
            /// [`is_infinite`][Self::is_infinite] instead.
            pub const INFINITY: Self = Self::inf(false);

            /// Negative infinity (−∞).
            ///
            /// # Note
            ///
            /// Do not use this constant to determine whether
            /// a number is infinity. Use
            /// [`is_infinite`][Self::is_infinite] instead.
            pub const NEG_INFINITY: Self = Self::inf(true);

            /// Reports whether the number is neither infinite
            /// nor NaN.
            pub const fn is_finite(self) -> bool {
                !self.is_special()
            }

            /// Reports whether the number is infinite or NaN.
            const fn is_special(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN.
                self.0 & Self::COMB_TOP4 == Self::COMB_TOP4
            }

            /// Reports whether the number is a NaN.
            pub const fn is_nan(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN. The fifth bit
                // signals NaN.
                self.0 & Self::COMB_TOP5 == Self::COMB_TOP5
            }

            /// Reports whether the number is a quiet NaN.
            pub const fn is_qnan(self) -> bool {
                // When the number is a NaN, the sixth
                // combination bit signals whether the NaN is
                // signaling.
                self.0 & Self::COMB_TOP6 == Self::COMB_TOP5
            }

            /// Reports whether the number is a signaling NaN.
            pub const fn is_snan(self) -> bool {
                // When the number is a NaN, the sixth
                // combination bit signals whether the NaN is
                // signaling.
                self.0 & Self::COMB_TOP6 == Self::COMB_TOP6
            }

            /// Reports whether the number is either positive or negative
            /// infinity.
            pub const fn is_infinite(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN. The fifth bit
                // signals NaN.
                self.0 & Self::COMB_TOP5 == Self::COMB_TOP4
            }

            /// Reports whether the number is neither zero,
            /// infinite, subnormal, or NaN.
            pub const fn is_normal(self) -> bool {
                if self.is_special() || self.is_zero() {
                    return false;
                }
                debug_assert!(self.is_finite());

                self.adjusted_exp() > Self::MIN_EXP
            }

            /// Reports whether the number is subnormal.
            pub const fn is_subnormal(self) -> bool {
                if self.is_special() || self.is_zero() {
                    return false;
                }
                debug_assert!(self.is_finite());

                self.adjusted_exp() <= Self::MIN_EXP
            }

            /// Reports whether the number is positive, including
            /// `+0.0`.
            pub const fn is_sign_positive(self) -> bool {
                !self.is_sign_negative()
            }

            /// Reports whether the number is negative, including
            /// `-0.0`.
            pub const fn is_sign_negative(self) -> bool {
                self.signbit()
            }

            /// Reports whether the number is `-0.0` or `+0.0`.
            pub const fn is_zero(self) -> bool {
                // Covers the coefficient and form one.
                const MASK1: $ucoeff = (0x7 << $name::COMB_SHIFT) | $name::COEFF_MASK;
                // Covers form two and specials.
                const MASK2: $ucoeff = 0x18 << $name::COMB_SHIFT;
                (self.0 & MASK1) == 0 && (self.0 & MASK2) != MASK2
            }

            /// Returns the floating point category for the
            /// number.
            pub const fn classify(self) -> FpCategory {
                // TODO(eric): Optimize this.
                if self.is_nan() {
                    FpCategory::Nan
                } else if self.is_infinite() {
                    FpCategory::Infinite
                } else if self.is_zero() {
                    FpCategory::Zero
                } else if self.is_normal() {
                    FpCategory::Normal
                } else {
                    FpCategory::Subnormal
                }
            }

            /// Returns the number of significant digits in the
            /// number.
            ///
            /// If the number is infinity or zero, it returns 1.
            ///
            /// The result will always be in [1,
            /// [`DIGITS`][Self::DIGITS]].
            ///
            /// TODO: NaN should return the number of digits in
            /// the payload.
            pub const fn digits(self) -> u32 {
                if self.is_finite() {
                    $arith::digits(self.coeff())
                } else {
                    1
                }
            }

            /// Returns the unbiased exponent.
            ///
            /// If the number is infinite or NaN, it returns
            /// `None`.
            pub const fn exponent(self) -> Option<$unbiased> {
                if self.is_finite() {
                    Some(self.unbiased_exp())
                } else {
                    None
                }
            }

            /// Reports whether `self == other`.
            ///
            /// - If either number is NaN, it returns `false`.
            /// - +0.0 and -0.0 are considered equal.
            ///
            /// This is a const version of [`PartialEq`].
            pub fn const_eq(self, other: Self) -> bool {
                if cfg!(debug_assertions) {
                    println!("const_eq({self}, {other})");
                }
                if self.is_nan() || other.is_nan() {
                    // NaN != NaN
                    return false;
                }
                // Neither are NaN.

                if self.to_bits() == other.to_bits() {
                    // Obvious case: same bits.
                    return true;
                }
                // Bits differ.

                if self.signbit() ^ other.signbit() {
                    // +0 == -0
                    // -0 == +0
                    // +x != -y
                    // -x != +y
                    return self.is_zero() && other.is_zero();
                }
                // Signs are the same.
                debug_assert!(self.signbit() == other.signbit());

                if self.is_infinite() || other.is_infinite() {
                    // +inf == +inf
                    // -inf == -inf
                    return self.is_finite() == other.is_finite();
                }
                // Both are finite.
                debug_assert!(self.is_finite() && other.is_finite());

                if self.is_zero() || other.is_zero() {
                    // +0 == -0
                    // -0 == +0
                    return self.is_zero() && other.is_zero();
                }
                // Both are non-zero.
                debug_assert!(!self.is_zero() && !other.is_zero());

                if cfg!(debug_assertions) {
                    println!("lhs = {self}");
                    println!("rhs = {other}");
                }

                // Bias doesn't matter for this comparison.
                let shift = self.biased_exp().abs_diff(other.biased_exp()) as u32;
                if shift >= Self::DIGITS {
                    // The shift is larger than the maximum
                    // precision, so the coefficients do not
                    // overlap.
                    return false;
                }
                // `shift` is in [0, DIGITS].

                // Align the coefficients. For example:
                //
                // 123.40 // coeff = 12340, exp = -2
                // 123.4  // coeff = 1234, exp = -1
                //
                // 12340 // coeff = 12340, exp = 0
                // 1234  // coeff = 1234, exp = 1

                if cfg!(debug_assertions) {
                    println!(
                        "shift = {}",
                        self.biased_exp() as i16 - other.biased_exp() as i16,
                    );

                    println!("lhs = {self}");
                    println!("rhs = {other}");
                }

                if shift == 0 {
                    return self.coeff() == other.coeff();
                }
                debug_assert!(self.biased_exp() != other.biased_exp());

                if self.biased_exp() > other.biased_exp() {
                    $arith::const_eq_shifted(self.coeff(), other.coeff(), shift)
                } else {
                    $arith::const_eq_shifted(other.coeff(), self.coeff(), shift)
                }
            }

            /// Returns the ordering between `self` and `other`.
            ///
            /// - If either number is NaN, it returns `None`.
            /// - +0.0 and -0.0 are considered equal.
            ///
            /// This is a const version of [`PartialOrd`].
            pub fn const_partial_cmp(self, other: Self) -> Option<Ordering> {
                if cfg!(debug_assertions) {
                    println!("partial_cmp({self}, {other})");
                }
                if self.is_nan() || other.is_nan() {
                    // NaN != NaN
                    return None;
                }
                // Neither are NaN.

                if self.signbit() ^ other.signbit() {
                    return if self.is_zero() && other.is_zero() {
                        Some(Ordering::Equal) // 0 == 0
                    } else if self.signbit() {
                        Some(Ordering::Less) // -x < +x
                    } else {
                        Some(Ordering::Greater) // +x > -x
                    };
                }
                // Signs are the same.

                if self.is_infinite() && other.is_infinite() {
                    // +inf cmp +inf
                    // -inf cmp -inf
                    return Some(Ordering::Equal);
                }
                // Both are finite.
                debug_assert!(self.is_finite() && other.is_finite());

                if self.is_zero() || other.is_zero() {
                    if cfg!(debug_assertions) {
                        println!("lhs is zero = {}", self.is_zero());
                        println!("rhs is zero = {}", other.is_zero());
                    }
                    return if !self.is_zero() {
                        Some(Ordering::Greater) // x > 0
                    } else if !other.is_zero() {
                        Some(Ordering::Less) // 0 < x
                    } else {
                        Some(Ordering::Equal) // 0 == 0
                    };
                }
                // Both are non-zero.
                debug_assert!(!self.is_zero() && !other.is_zero());

                // Bias doesn't matter for this comparison.
                let shift = self.biased_exp().abs_diff(other.biased_exp()) as u32;
                if shift >= Self::DIGITS {
                    // The shift is larger than the maximum
                    // precision, so the coefficients do not
                    // overlap. Therefore, the larger exponent is
                    // the larger number.
                    return if self.biased_exp() < other.biased_exp() {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    };
                }
                // `shift` is in [0, DIGITS].

                if cfg!(debug_assertions) {
                    println!("lhs exp = {}", self.biased_exp());
                    println!("rhs exp = {}", other.biased_exp());
                    println!("shift = {shift}");
                }

                if shift == 0 {
                    return Some($arith::const_cmp(self.coeff(), other.coeff()));
                }
                debug_assert!(self.biased_exp() != other.biased_exp());

                if self.biased_exp() > other.biased_exp() {
                    Some($arith::const_cmp_shifted(
                        self.coeff(),
                        other.coeff(),
                        shift,
                    ))
                } else {
                    Some($arith::const_cmp_shifted(
                        other.coeff(),
                        self.coeff(),
                        shift,
                    ))
                }
            }

            /// Returns the total ordering between `self` and
            /// `other`.
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
            /// The ordering established by this function does
            /// not always agree with [`PartialOrd`] and
            /// [`PartialEq`]. For example, they consider
            /// negative and positive zero equal, while
            /// `const_total_cmp` doesn't.
            pub const fn const_total_cmp(self, other: Self) -> Ordering {
                let mut lhs = self.to_bits() as $icoeff;
                let mut rhs = other.to_bits() as $icoeff;

                const BITS: u32 = <$icoeff>::BITS;

                lhs ^= (((lhs >> (BITS - 1)) as $ucoeff) >> 1) as $icoeff;
                rhs ^= (((rhs >> (BITS - 1)) as $ucoeff) >> 1) as $icoeff;

                if lhs < rhs {
                    Ordering::Less
                } else if lhs > rhs {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
        }

        // To/from repr.
        impl $name {
            /// Creates a number from its coefficient and
            /// exponent.
            pub const fn new(coeff: $icoeff, exp: $unbiased) -> Self {
                let sign = coeff < 0;
                let coeff = coeff.unsigned_abs();
                if !Self::need_round(coeff, exp) {
                    // Fast path: `coeff` and `exp` are obviously
                    // valid.
                    Self::from_parts(sign, exp, coeff)
                } else {
                    // Slow path: we have to round.
                    //
                    // Prevent the compiler from inlining
                    // `Self::rounded`. Otherwise, `Self::new`
                    // becomes too large and prevents other
                    // methods that call `Self::new` from being
                    // properly optimized. For example, compare
                    // `Bid128::from_i64` if the compiler inlines
                    // `Self::rounded` into `Self::new`
                    //
                    // ```text
                    // decnum::bid::bid128::Bid128::from_i64:
                    // Lfunc_begin13:
                    // 	asr x1, x0, #63
                    // 	mov w2, #0
                    // 	b decnum::bid::bid128::Bid128::new
                    // ```
                    //
                    // and if it doesn't
                    //
                    // ```text
                    // decnum::bid::bid128::Bid128::from_i64:
                    // Lfunc_begin13:
                    // 	mov x1, x0
                    // 	cmp x0, #0
                    // 	cneg x0, x0, mi
                    // 	mov x8, #3476778912330022912
                    // 	bfxil x1, x8, #0, #63
                    // 	ret
                    // ```
                    #[inline(never)]
                    const fn rounded(sign: bool, exp: $unbiased, coeff: $ucoeff) -> $name {
                        $name::rounded(sign, exp, coeff)
                    }
                    rounded(sign, exp, coeff)
                }
            }

            /// Creates a number from its raw bits.
            ///
            /// ```rust
            /// use decnum::Bid128;
            ///
            /// let got = Bid128::from_bits(0x2207c0000000000000000000000000a5);
            /// let want = "12.5".parse::<Bid128>().unwrap();
            /// assert_eq!(v, "12.5");
            /// ```
            pub const fn from_bits(bits: $ucoeff) -> Self {
                Self(bits)
            }

            /// Creates a number from a little-endian byte array.
            pub const fn from_le_bytes(bytes: [u8; Self::BYTES]) -> Self {
                Self::from_bits(<$ucoeff>::from_le_bytes(bytes))
            }

            /// Creates a number from a big-endian byte array.
            pub const fn from_be_bytes(bytes: [u8; Self::BYTES]) -> Self {
                Self::from_bits(<$ucoeff>::from_be_bytes(bytes))
            }

            /// Creates a number from a native-endian byte array.
            pub const fn from_ne_bytes(bytes: [u8; Self::BYTES]) -> Self {
                Self::from_bits(<$ucoeff>::from_ne_bytes(bytes))
            }

            /// Raw transmutation to the number's raw bit
            /// representation.
            pub const fn to_bits(self) -> $ucoeff {
                self.0
            }
        }
    };
}
pub(crate) use impl_dec_pub;

macro_rules! impl_dec_impls {
    ($name:ident) => {
        impl ::core::cmp::PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.const_eq(*other)
            }
        }

        impl ::core::cmp::PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                self.const_partial_cmp(*other)
            }
        }

        impl ::core::iter::Product for $name {
            fn product<I: ::core::iter::Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::new(1, 0), |a, b| a * b)
            }
        }
        impl<'a> ::core::iter::Product<&'a $name> for $name {
            fn product<I: ::core::iter::Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::new(1, 0), |a, b| a * b)
            }
        }

        impl ::core::iter::Sum for $name {
            fn sum<I: ::core::iter::Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), |a, b| a + b)
            }
        }
        impl<'a> ::core::iter::Sum<&'a $name> for $name {
            fn sum<I: ::core::iter::Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), |a, b| a + b)
            }
        }
    };
}
pub(crate) use impl_dec_impls;