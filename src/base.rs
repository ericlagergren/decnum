macro_rules! impl_dec {
    (
        name = $name:ident,
        ucoeff = $ucoeff:ty,
        scoeff = $scoeff:ty,
        biased_exp = $biased:ty,
        unbiased_exp = $unbiased:ty,
        comb = $comb:ty,
        arith = $arith:ident $(,)?
    ) => {
        $crate::base::impl_dec_internal!(
            $name, $ucoeff, $scoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::base::impl_dec_impls!($name);
    };
}
pub(crate) use impl_dec;

macro_rules! impl_dec_internal {
    (
        $name:ident,
        $ucoeff:ty,
        $scoeff:ty,
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

            const MAX_SCALEB_N: u32 = 2 * (Self::EMAX as u32 + Self::MAX_PREC);

            const fn signbit(self) -> bool {
                (self.0 & Self::SIGN_MASK) != 0
            }

            /// Is this form one or form two?
            const fn is_form2(self) -> bool {
                self.0 & Self::COMB_TOP2 == Self::COMB_TOP2
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
            /// [[`ETIN`][Self::ETIN], [`MAX_EXP`][Self::MAX_EXP]].
            const fn unbiased_exp(self) -> $unbiased {
                const_assert!($name::LIMIT < <$unbiased>::MAX as $biased);
                const_assert!(<$unbiased>::MAX - ($name::LIMIT as $unbiased) > $name::BIAS);

                // The exponent only has meaning for finite numbers.
                debug_assert!(self.is_finite());

                // `self.exp()` is in [0, LIMIT] and LIMIT
                // < <$unbiased>::MAX, so the cast cannot wrap.
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
                        assume(exp <= Self::MAX_EXP);
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
                // The coefficient only has meaning for finite numbers.
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

            const fn with_biased_exp(mut self, exp: $biased) -> Self {
                debug_assert!(exp <= Self::LIMIT);

                if self.is_form2() {
                    self.0 &= !Self::FORM2_EXP_MASK;
                    self.0 |= (exp as $ucoeff) << Self::FORM2_EXP_SHIFT;
                } else {
                    self.0 &= !Self::FORM1_EXP_MASK;
                    self.0 |= (exp as $ucoeff) << Self::FORM1_EXP_SHIFT;
                }
                self
            }

            /// Creates a finite number from the sign, unbiased
            /// exponent, an coefficient.
            pub(crate) const fn from_parts(sign: bool, exp: $unbiased, coeff: $ucoeff) -> Self {
                debug_assert!(coeff <= Self::MAX_COEFF as $ucoeff);
                debug_assert!(exp >= Self::ADJ_EMIN);
                debug_assert!(exp <= Self::ADJ_EMAX);

                // TODO(eric): If `exp` is valid then this cannot
                // overflow. Maybe make sure of it?
                #[allow(clippy::cast_sign_loss)]
                let biased = (exp + Self::BIAS) as $biased;

                // Do we need to use form two?
                //
                // Form one is 3+T bits with an implicit leading 0b0.
                // Form two is 4+T bits with an implicit leading 0b100.
                //
                // This used to be
                //    const fn need_form2(coeff) -> bool { ... }
                // but the compiler wasn't able to notice that
                // `MAX_COEFF_BITS <= Self::FORM1_COEFF_BITS` is
                // constant and was generating a bunch of extra
                // code.
                let form2 = if Self::MAX_COEFF_BITS <= Self::FORM1_COEFF_BITS {
                    // The max coefficient fits in 3+T bits, so
                    // we don't need form 2.
                    false
                } else {
                    // Is the MSB set (implying we need bit 4)?
                    (coeff & Self::MAX_COEFF_MASK) >> (Self::MAX_COEFF_BITS - 1) != 0
                };

                let mut bits = 0;
                if form2 {
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
        }
    };
}
pub(crate) use impl_dec_internal;

macro_rules! impl_dec_impls {
    ($name:ident) => {
        impl ::core::ops::Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self::Output {
                self.const_add(rhs)
            }
        }

        impl ::core::ops::AddAssign for $name {
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs;
            }
        }

        impl ::core::ops::Mul for $name {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self::Output {
                self.const_mul(rhs)
            }
        }

        impl ::core::ops::MulAssign for $name {
            fn mul_assign(&mut self, rhs: Self) {
                *self = *self * rhs;
            }
        }

        impl ::core::ops::Neg for $name {
            type Output = Self;
            fn neg(self) -> Self::Output {
                self.const_neg()
            }
        }

        impl ::core::ops::Sub for $name {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self::Output {
                self.const_sub(rhs)
            }
        }

        impl ::core::ops::SubAssign for $name {
            fn sub_assign(&mut self, rhs: Self) {
                *self = *self - rhs;
            }
        }

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

        impl ::core::str::FromStr for $name {
            type Err = ParseError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $name::parse(s)
            }
        }

        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::Default);
                write!(f, "{str}")
            }
        }

        impl ::core::fmt::Binary for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::Binary::fmt(&self.to_bits(), f)
            }
        }

        impl ::core::fmt::LowerExp for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::LowerExp);
                ::core::write!(f, "{str}")
            }
        }

        impl ::core::fmt::UpperExp for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::UpperExp);
                ::core::write!(f, "{str}")
            }
        }
    };
}
pub(crate) use impl_dec_impls;
