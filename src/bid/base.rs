macro_rules! impl_dec {
    (
        name = $name:ident,
        ucoeff = $ucoeff:ty,
        icoeff = $icoeff:ty,
        biased_exp = $biased:ty,
        unbiased_exp = $unbiased:ty,
        comb = $comb:ty,
        arith = $arith:ident,
        dpd = $dpd:ty,
        prefix = $prefix:literal $(,)?
    ) => {
        $crate::bid::base::impl_dec_internal!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_consts!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_to_from_repr!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith, $dpd,
        );
        $crate::bid::base::impl_dec_arith!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_misc!(
            $name, $ucoeff, $icoeff, $biased, $unbiased, $comb, $arith
        );
        $crate::bid::base::impl_dec_misc2!(
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
            /// The storage width in bits.
            pub(crate) const K: u32 = (size_of::<$name>() * 8) as u32;
            /// The size of the sign bit in bits.
            const S: u32 = 1;
            /// The width of the exponent in bits.
            pub(crate) const W: u32 = Self::K / 16 + 4;
            /// The width of the combination field in bits.
            #[allow(dead_code, reason = "For documentation purposes")]
            const G: u32 = Self::W + 5;
            /// The width of the trailing significand in bits.
            const T: u32 = 15 * (Self::K / 16) - 10;
            /// The number of digits of precision.
            const P: u32 = 9 * (Self::K / 32) - 2;

            /// The storage width in bytes.
            pub(crate) const BYTES: usize = (Self::K / 8) as usize;

            /// The bias added to the encoded exponent in order
            /// to convert it to the "actual" exponent.
            pub(crate) const BIAS: $unbiased = Self::EMAX + (Self::P as $unbiased) - 2;

            /// The maxmimum value of the biased encoded
            /// exponent.
            pub(crate) const LIMIT: $biased = (3 * (1 << Self::W)) - 1;

            /// The maximum allowed adjusted exponent.
            pub(crate) const EMAX: $unbiased = 3 * (1 << (Self::W - 1));

            /// The minimum allowed adjusted exponent for
            /// a normal value.
            pub(crate) const EMIN: $unbiased = 1 - Self::EMAX;

            /// The minimum unbiased exponent for a subnormal
            /// value.
            pub(crate) const ETINY: $unbiased = Self::EMIN - ((Self::P as $unbiased) - 1);

            /// The maximum adjusted exponent for a full-length
            /// coefficient.
            pub(crate) const EMAX_LESS_PREC: $unbiased =
                Self::MAX_EXP - ((Self::MAX_PREC as $unbiased) - 1);

            /// The minimum adjusted exponent for a full-length
            /// coefficient.
            pub(crate) const EMIN_LESS_PREC: $unbiased =
                Self::MIN_EXP - ((Self::MAX_PREC as $unbiased) - 1);

            /// The number of digits of precision.
            pub(crate) const MAX_PREC: u32 = Self::P;

            /// The shift needed to set the sign bit.
            pub(crate) const SIGN_SHIFT: u32 = Self::K - Self::S;
            /// Masks just the sign bit.
            const SIGN_MASK: $ucoeff = 1 << Self::SIGN_SHIFT;

            // Top N bits of the combination field.
            //
            // - Top 4 set: inf
            // - Top 5 set: qnan
            // - Top 6 set: snan
            pub(crate) const COMB_TOP2: $ucoeff = 0x3 << (Self::SIGN_SHIFT - 2);
            pub(crate) const COMB_TOP4: $ucoeff = 0xf << (Self::SIGN_SHIFT - 4);
            pub(crate) const COMB_TOP5: $ucoeff = 0x1f << (Self::SIGN_SHIFT - 5);
            pub(crate) const COMB_TOP6: $ucoeff = 0x3f << (Self::SIGN_SHIFT - 6);

            /// The number of bits in the exponent.
            pub(crate) const EXP_BITS: u32 = Self::W + 2;
            /// Masks only the used bits in an exponent.
            ///
            /// NB: This does *not* mask bits in the combination
            /// field.
            pub(crate) const EXP_MASK: $biased = (1 << Self::EXP_BITS) - 1;

            /// Masks the exponent in the combination field for
            /// a form one number.
            const FORM1_EXP_MASK: $ucoeff = (Self::EXP_MASK as $ucoeff) << Self::FORM1_EXP_SHIFT;
            /// The shift to set the exponent for a form one
            /// number.
            const FORM1_EXP_SHIFT: u32 = Self::SIGN_SHIFT - Self::EXP_BITS;

            /// Masks the exponent in the combination field for
            /// a form two number.
            const FORM2_EXP_MASK: $ucoeff = Self::FORM1_EXP_MASK >> 2;
            /// The shift to set the exponent for a form Two
            /// number.
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
            const MAX_COEFF_BITS: u32 = $arith::bitlen(Self::MAX_COEFF as $ucoeff);

            /// The number of bits in the trailing significand.
            pub(crate) const COEFF_BITS: u32 = Self::T;
            /// MAsks the trailing significand field.
            pub(crate) const COEFF_MASK: $ucoeff = (1 << Self::COEFF_BITS) - 1;

            /// Masks a NaN's payload.
            pub(crate) const PAYLOAD_MASK: $ucoeff = Self::COEFF_MASK;
            /// The maximum number of digits in a NaN's payload.
            const PAYLOAD_DIGITS: u32 = $arith::digits(Self::PAYLOAD_MASK);
            /// The maximum allowed NaN payload.
            const PAYLOAD_MAX: $ucoeff = Self::PAYLOAD_MASK;

            /// A mask for the bits (all except [G6:Gw+4]) that
            /// are allowed to be set for a canonical NaN.
            const CANONICAL_NAN: $ucoeff = Self::SIGN_MASK | Self::COMB_TOP6 | Self::PAYLOAD_MASK;

            /// A mask for the bits (all except [G5:Gw+4] as well
            /// as the trailing significant field) that are
            /// allowed to be set for a canonical infinity.
            const CANONICAL_INF: $ucoeff = Self::SIGN_MASK | Self::COMB_TOP4;

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

            /// Reports whether the number is infinite or NaN.
            const fn is_special(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN.
                self.0 & Self::COMB_TOP4 == Self::COMB_TOP4
            }

            /// Reports whether the number is finite or infinite.
            const fn is_numeric(self) -> bool {
                !self.is_nan()
            }

            /// Returns the top six bits in the combination
            /// field.
            ///
            /// These bits have the following ordering:
            ///
            /// ```text
            /// sNaN > qNaN > inf > finite
            /// ```
            const fn special_bits(self) -> u8 {
                const SHIFT: u32 = $name::SIGN_SHIFT - 6;
                const MASK: $ucoeff = $name::COMB_TOP6;

                ((self.0 & MASK) >> SHIFT) as u8
            }

            /// Returns the top six bits in the combination
            /// field with the following ordering:
            ///
            /// ```text
            /// qNaN > sNaN > inf > finite
            /// ```
            ///
            /// (The same ordering required by `total_cmp`.)
            const fn special_ord(self) -> u8 {
                //   sNaN = 0b00111111
                //   qNaN = 0b00111110
                //    inf = 0b00111100
                // finite = 0b00xxxxyy
                //
                // (Where `xxxx` is anything other than `1111`
                // and `yy` is anything.)
                //
                // Flipping the LSB reverses sNaN and qNaN
                // without violating the ordering.
                self.special_bits() ^ 1
            }

            /// Returns the biased exponment.
            ///
            /// If the number is finite, the result is in [0,
            /// [`LIMIT`][Self::LIMIT]].
            const fn biased_exp(self) -> $biased {
                // The exponent only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                let exp = if self.is_form1() {
                    // exp = G[0:w+1]
                    ((self.0 & Self::FORM1_EXP_MASK) >> Self::FORM1_EXP_SHIFT) as $biased
                } else {
                    // exp = G[2:w+3]
                    ((self.0 & Self::FORM2_EXP_MASK) >> Self::FORM2_EXP_SHIFT) as $biased
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
                const_assert!($name::LIMIT.checked_add_signed($name::BIAS).is_some());

                // The exponent only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                // `self.biased_exp()` is in [0, LIMIT] and
                // `LIMIT <= <$unbiased>::MAX`, so the cast
                // cannot wrap.
                //
                // The subtraction cannot wrap since
                //    LIMIT + BIAS <= <$unbiased>::MAX
                //    0 - BIAS > <$unbiased>::MIN
                #[allow(clippy::cast_possible_wrap)]
                let exp = (self.biased_exp() as $unbiased) - Self::BIAS;

                debug_assert!(exp >= Self::ETINY);
                debug_assert!(exp <= Self::EMAX);

                exp
            }

            /// Returns the adjusted exponent.
            ///
            /// This is `exp + digits - 1`.
            const fn adjusted_exp(self) -> $unbiased {
                // The exponent only has meaning for finite
                // numbers.
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
            ///
            /// NB: This may be out of range.
            const fn raw_coeff(self) -> $ucoeff {
                // The coefficient only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                if self.is_form1() {
                    // G[w+2:w+4] || T
                    self.0 & Self::FORM1_COEFF_MASK
                } else {
                    // 100 || G[w+4] || T
                    Self::FORM2_IMPLICIT_COEFF_BITS | (self.0 & Self::FORM2_COEFF_MASK)
                }
            }

            /// Returns the full coefficient.
            const fn coeff(self) -> $ucoeff {
                // The coefficient only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                let coeff = self.raw_coeff();

                // See 3.2(c)(2).
                if coeff > Self::MAX_COEFF as $ucoeff {
                    0
                } else {
                    coeff
                }
            }

            /// Returns the signed coefficient.
            #[allow(dead_code)] // TODO
            const fn signed_coeff(self) -> $icoeff {
                // The coefficient only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                let coeff = self.coeff();
                if self.signbit() {
                    -(coeff as $icoeff)
                } else {
                    coeff as $icoeff
                }
            }

            /// Returns a NaN's diagnostic information.
            const fn payload(self) -> $ucoeff {
                // The coefficient only has meaning for NaNs.
                debug_assert!(self.is_nan());

                self.0 & Self::PAYLOAD_MASK
            }

            /// TODO: keep this?
            const fn with_unbiased_exp(self, exp: $unbiased) -> Self {
                // TODO(eric): debug assertions
                #[allow(clippy::cast_sign_loss, reason = "TODO")]
                self.with_biased_exp((exp + Self::BIAS) as $biased)
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

            /// Creates a rounded number from its sign, unbiased
            /// exponent, and coefficient.
            const fn rounded(sign: bool, exp: $unbiased, coeff: $ucoeff) -> Self {
                let (mut coeff, mut exp, digits) = Self::round(coeff, exp);
                let adj = exp + (digits as $unbiased - 1);
                if exp < Self::EMIN && adj < Self::EMIN {
                    // NB: This is where we'd mark underflow.
                    if adj < Self::ETINY {
                        // Subnormal < ETINY, so exp = ETINY and
                        // the coeff is rounded.
                        //
                        // TODO(eric): Round to 0, don't hard
                        // code 0.
                        return Self::from_parts(sign, Self::ETINY, 0);
                    }
                    debug_assert!(adj >= Self::ETINY);
                }
                debug_assert!(exp >= Self::EMIN);
                debug_assert!(adj >= Self::EMIN);

                if exp > Self::EMAX_LESS_PREC {
                    if coeff == 0 {
                        exp = Self::EMAX_LESS_PREC; // clamped
                    } else if adj > Self::EMAX {
                        // NB: This is where we'd mark overflow.
                        return Self::inf(sign);
                    } else {
                        let shift = exp - (Self::EMAX - (Self::MAX_PREC - 1) as i16);
                        if shift > 0 {
                            // `shift > 0`, so there isn't any
                            // sign to lose.
                            #[allow(clippy::cast_sign_loss)]
                            let e = shift as u32;
                            coeff *= (10 as $ucoeff).pow(e);
                            exp -= shift;
                        }
                    }
                }
                debug_assert!(adj <= Self::EMAX);

                // adj is in [ETINY, EMAX].

                Self::from_parts(sign, exp, coeff)
            }

            /// Rounds `(coeff, exp)`.
            const fn round(mut coeff: $ucoeff, mut exp: $unbiased) -> ($ucoeff, $unbiased, u32) {
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

                let mut digits = $arith::digits(coeff);
                // Figure out how many digits we need to drop.
                let mut drop = max(
                    digits as $unbiased - Self::DIGITS as $unbiased,
                    Self::ETINY - exp,
                );
                if false && drop > 0 {
                    exp += drop;
                    let rem;
                    (coeff, rem) = $arith::shr(coeff, drop as u32);
                    digits -= drop as u32;
                    if rem > 0 {}
                } else if drop > 0 {
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
                (coeff, exp, digits)
            }

            /// Calls [`from_parts`][Self::from_parts] or
            /// [`rounded`][Self::rounded], depending whether or
            /// not rounding is needed.
            const fn maybe_rounded(sign: bool, exp: $unbiased, coeff: $ucoeff) -> Self {
                if !Self::need_round_fast(coeff, exp) {
                    // Fast path: `coeff` and `exp` are obviously
                    // valid.
                    Self::from_parts(sign, exp, coeff)
                } else {
                    // Slow path: we (probably) have to round.
                    Self::rounded(sign, exp, coeff)
                }
            }

            /// Does `(coeff, exp)` definintely need to be
            /// rounded?
            const fn need_round_fast(coeff: $ucoeff, exp: $unbiased) -> bool {
                coeff > Self::MAX_COEFF as $ucoeff
                    || exp < Self::EMIN_LESS_PREC
                    || exp > Self::EMAX_LESS_PREC
            }

            /// Does `(coeff, exp)` need to be rounded?
            const fn need_round(coeff: $ucoeff, exp: $unbiased) -> bool {
                let digits = $arith::digits(coeff);
                if digits > Self::DIGITS {
                    // Too many digits.
                    return true;
                }
                if exp < Self::ETINY {
                    // `exp` is too small.
                    return true;
                }
                let _adj = exp + (digits as $unbiased - 1);
                false
            }

            /// Creates a canonical finite number from the sign,
            /// unbiased exponent, an coefficient.
            ///
            /// The result is exact and unrounded.
            pub(crate) const fn from_parts(sign: bool, exp: $unbiased, coeff: $ucoeff) -> Self {
                debug_assert!(coeff <= Self::MAX_COEFF as $ucoeff);
                debug_assert!(exp >= Self::EMIN_LESS_PREC);
                debug_assert!(exp <= Self::EMAX_LESS_PREC);
                debug_assert!(!Self::need_round(coeff, exp));

                // TODO(eric): If `exp` is valid then this cannot
                // overflow. Maybe make sure of it?
                #[allow(clippy::cast_sign_loss)]
                let biased = (exp + Self::BIAS) as $biased;

                // Do we need to encode the coefficient using
                // form two?
                //
                // Form one is 3+T bits with an implicit leading 0b0.
                // Form two is 4+T bits with an implicit leading 0b100.
                let need_form2 = if Self::MAX_COEFF_BITS <= Self::FORM1_COEFF_BITS {
                    // The max coefficient fits in 3+T bits, so
                    // we don't need form 2.
                    false
                } else {
                    // Is the MSB set (implying we need bit 4)?
                    (coeff >> (Self::MAX_COEFF_BITS - 1)) & 0x1 != 0
                };

                let mut bits = 0;
                if need_form2 {
                    // s 1100eeeeee (100)t tttttttttt tttttttttt
                    // s 1101eeeeee (100)t tttttttttt tttttttttt
                    // s 1110eeeeee (100)t tttttttttt tttttttttt
                    bits |= (sign as $ucoeff) << Self::SIGN_SHIFT;
                    bits |= Self::COMB_TOP2;
                    bits |= (biased as $ucoeff) << Self::FORM2_EXP_SHIFT;
                    bits |= coeff & Self::FORM2_COEFF_MASK;
                } else {
                    // s 00eeeeee   (0)ttt tttttttttt tttttttttt
                    // s 01eeeeee   (0)ttt tttttttttt tttttttttt
                    // s 10eeeeee   (0)ttt tttttttttt tttttttttt
                    bits |= (sign as $ucoeff) << Self::SIGN_SHIFT;
                    bits |= (biased as $ucoeff) << Self::FORM1_EXP_SHIFT;
                    bits |= coeff & Self::FORM1_COEFF_MASK;
                }
                // TODO: $crate::bid::canonical!(bits)
                Self(bits)
            }

            /// Creates a canonical infinity.
            pub(crate) const fn inf(sign: bool) -> Self {
                let mut bits = 0;
                bits |= (sign as $ucoeff) << Self::SIGN_SHIFT;
                bits |= Self::COMB_TOP4;
                $crate::bid::canonical!(bits)
            }

            /// Creates a canonical quiet NaN.
            pub(crate) const fn nan(sign: bool, payload: $ucoeff) -> Self {
                debug_assert!(payload <= Self::PAYLOAD_MAX);

                let mut bits = 0;
                bits |= (sign as $ucoeff) << Self::SIGN_SHIFT;
                bits |= Self::COMB_TOP5;
                bits |= payload;
                $crate::bid::canonical!(bits)
            }

            /// Creates a canonical signaling NaN.
            pub(crate) const fn snan(sign: bool, payload: $ucoeff) -> Self {
                debug_assert!(payload <= Self::PAYLOAD_MAX);

                let mut bits = 0;
                bits |= (sign as $ucoeff) << Self::SIGN_SHIFT;
                bits |= Self::COMB_TOP6;
                bits |= payload;
                $crate::bid::canonical!(bits)
            }

            /// Creates a canonical zero.
            const fn zero() -> Self {
                Self::new(0, 0)
            }

            /// Creates a NaN from either `lhs` or `rhs` per
            /// [Arithmetic operation rules][rules].
            ///
            /// One of the two arguments *must* be NaN.
            ///
            /// [rules]: https://speleotrove.com/decimal/daops.html
            pub(super) const fn select_nan(lhs: Self, rhs: Self) -> Self {
                debug_assert!(lhs.is_nan() || rhs.is_nan());

                let nan = if lhs.is_snan() {
                    lhs
                } else if rhs.is_snan() {
                    rhs
                } else if lhs.is_nan() {
                    lhs
                } else {
                    rhs
                };
                Self::nan(nan.signbit(), nan.payload())
            }
        }
    };
}
pub(crate) use impl_dec_internal;

macro_rules! impl_dec_consts {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        impl $name {
            /// The largest value that can be represented by this
            /// type.
            pub const MAX: Self = Self::new(Self::MAX_COEFF, Self::EMAX_LESS_PREC);

            /// The smallest value that can be represented by
            /// this type.
            pub const MIN: Self = Self::new(Self::MIN_COEFF, Self::EMIN_LESS_PREC);

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
            pub const NAN: Self = Self::nan(false, 0);

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
        }
    };
}
pub(crate) use impl_dec_consts;

macro_rules! impl_dec_arith {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        // Arithmetic operations.
        // <https://speleotrove.com/decimal/daops.html>
        impl $name {
            /// Returns the absolute value of `self`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn abs(self) -> Self {
                if self.is_nan() {
                    Self::select_nan(self, self)
                } else {
                    self.copy_abs()
                }
            }

            /// Reports whether `self == other`.
            ///
            /// - If either number is NaN, it returns `false`.
            /// - +0.0 and -0.0 are considered equal.
            ///
            /// This is a const version of [`PartialEq`].
            pub const fn const_eq(self, other: Self) -> bool {
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

                if self.signbit() != other.signbit() {
                    // ±x == ±y
                    return self.is_zero() && other.is_zero();
                }
                // Signs are the same.
                debug_assert!(self.signbit() == other.signbit());

                if self.is_infinite() || other.is_infinite() {
                    // ±inf == ±inf
                    return self.is_finite() == other.is_finite();
                }
                // Both are finite.
                debug_assert!(self.is_finite() && other.is_finite());

                if self.is_zero() || other.is_zero() {
                    // ±0 == ±0
                    return self.is_zero() && other.is_zero();
                }
                // Both are non-zero.
                debug_assert!(!self.is_zero() && !other.is_zero());

                // Bias doesn't matter for this comparison.
                let shift = self.biased_exp().abs_diff(other.biased_exp()) as u32;
                if shift >= Self::DIGITS {
                    // The shift is larger than the maximum
                    // precision, so the coefficients do not
                    // overlap.
                    return false;
                }
                // `shift` is in [0, DIGITS].

                if shift == 0 {
                    self.coeff() == other.coeff()
                } else if self.biased_exp() > other.biased_exp() {
                    $arith::const_eq_shifted(self.coeff(), other.coeff(), shift)
                } else {
                    $arith::const_eq_shifted(other.coeff(), self.coeff(), shift)
                }
            }

            /// Returns the ordering between `self` and `rhs`.
            ///
            /// - If either number is NaN, it returns `None`.
            /// - +0.0 and -0.0 are considered equal.
            ///
            /// This is a const version of [`PartialOrd`].
            pub const fn const_partial_cmp(self, rhs: Self) -> Option<Ordering> {
                if self.is_nan() || rhs.is_nan() {
                    // NaN != NaN
                    return None;
                }
                // Neither are NaN.
                debug_assert!(!self.is_nan() && !rhs.is_nan());

                Some(self.partial_cmp_numeric(rhs))
            }

            const fn partial_cmp_numeric(self, rhs: Self) -> Ordering {
                debug_assert!(self.is_numeric() && rhs.is_numeric());

                if self.signbit() != rhs.signbit() {
                    return if self.is_zero() && rhs.is_zero() {
                        // ±0 == ±0
                        Ordering::Equal
                    } else if self.signbit() {
                        // -x < +x
                        Ordering::Less
                    } else {
                        // +x > -x
                        Ordering::Greater
                    };
                }
                // Signs are the same.
                debug_assert!(self.signbit() == rhs.signbit());

                let ord = self.partial_cmp_numeric_abs(rhs);
                if self.signbit() {
                    ord.reverse()
                } else {
                    ord
                }
            }

            const fn partial_cmp_numeric_abs(self, rhs: Self) -> Ordering {
                debug_assert!(self.signbit() == rhs.signbit());

                if self.to_bits() == rhs.to_bits() {
                    // Obvious case: same bits.
                    return Ordering::Equal;
                }
                // Bits differ.

                if self.is_infinite() || rhs.is_infinite() {
                    return $crate::bid::util::const_cmp_u8(self.special_ord(), rhs.special_ord());
                }
                // Both are finite.
                debug_assert!(self.is_finite() && rhs.is_finite());

                if self.is_zero() || rhs.is_zero() {
                    return if !self.is_zero() {
                        // x > 0
                        Ordering::Greater
                    } else if !rhs.is_zero() {
                        // 0 < x
                        Ordering::Less
                    } else {
                        // +0 == +0
                        // -0 == -0
                        Ordering::Equal
                    };
                }
                // Both are non-zero.
                debug_assert!(!self.is_zero() && !rhs.is_zero());

                // Bias doesn't matter for this comparison.
                let shift = self.biased_exp().abs_diff(rhs.biased_exp()) as u32;
                if shift >= Self::DIGITS {
                    // The shift is larger than the maximum
                    // precision, so the coefficients do not
                    // overlap. Therefore, the larger exponent is
                    // the larger number.
                    return if self.biased_exp() < rhs.biased_exp() {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                }
                // `shift` is in [0, DIGITS].

                if shift == 0 {
                    $arith::const_cmp(self.coeff(), rhs.coeff())
                } else if self.biased_exp() > rhs.biased_exp() {
                    $arith::const_cmp_shifted(self.coeff(), rhs.coeff(), shift)
                } else {
                    $arith::const_cmp_shifted(rhs.coeff(), self.coeff(), shift).reverse()
                }
            }

            /// Only used by dectest.
            #[cfg(test)]
            pub(crate) fn compare(self, rhs: Self) -> Self {
                use Ordering::*;
                match self.const_partial_cmp(rhs) {
                    Some(Greater) => Self::new(1, 0), // +1
                    Some(Less) => Self::new(-1, 0),   // -1
                    Some(Equal) => Self::zero(),      // +0
                    None => Self::select_nan(self, rhs),
                }
            }

            /// Only used by dectest.
            #[cfg(test)]
            pub(crate) fn compare_sig(mut self, mut rhs: Self) -> Self {
                /// The bits set for an sNaN.
                const SNAN_MASK: $ucoeff = $name::COMB_TOP6;
                if self.is_nan() {
                    self = $crate::bid::canonical!(self.0 | SNAN_MASK)
                }
                if rhs.is_nan() {
                    rhs = $crate::bid::canonical!(rhs.0 | SNAN_MASK)
                }
                self.compare(rhs)
            }

            /// Only used by dectest.
            #[cfg(test)]
            pub(crate) fn compare_total(self, rhs: Self) -> Self {
                if cfg!(debug_assertions) {
                    println!("compare_total({self}, {rhs})");
                }
                use Ordering::*;
                match self.total_cmp(rhs) {
                    Greater => Self::new(1, 0), // +1
                    Less => Self::new(-1, 0),   // -1
                    Equal => Self::zero(),      // +0
                }
            }

            /// Returns `-self`.
            ///
            /// This is equivalent to `0 - self`.
            ///
            /// This is the same as [`Neg`][core::ops::Neg], but
            /// can be used in a const context.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn const_neg(self) -> Self {
                if self.is_nan() {
                    // ±0 - ±NaN
                    Self::nan(self.signbit(), self.payload())
                } else if self.is_zero() {
                    // ±0 - ±0
                    self.copy_abs()
                } else {
                    // ±0 - self
                    self.copy_neg().canonical()
                }
            }

            /// Returns `self - other`.
            ///
            /// This is the same as [`Sub`][core::ops::Sub], but
            /// can be used in a const context.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn const_sub(self, rhs: Self) -> Self {
                // x - y = x + -y
                self.const_add(rhs.const_neg())
            }

            /// Returns the natural logarithm of `self`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn ln(self) -> Self {
                todo!()
            }

            /// Returns the base 10 logarithm of `self`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn log10(self) -> Self {
                todo!()
            }

            /// Returns the maximum of `self` and `rhs`.
            ///
            /// If one operand is qNaN and the other is a finite
            /// number, it returns the finite number.
            ///
            /// See IEEE 754-2008 `maxNum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub fn max(self, rhs: Self) -> Self {
                if cfg!(debug_assertions) {
                    println!("max({self}, {rhs})");
                    println!("cmp({self},{rhs})={:?}", self.const_partial_cmp(rhs));
                }
                let max = if self.is_numeric() && rhs.is_numeric() {
                    // Both are numeric, so `total_cmp` ensures
                    // that +0 > -0, etc.
                    use Ordering::*;
                    match self.total_cmp(rhs) {
                        Greater | Equal => self,
                        Less => rhs,
                    }
                } else if self.is_numeric() && rhs.is_qnan() {
                    self
                } else if self.is_qnan() && rhs.is_numeric() {
                    rhs
                } else {
                    // `select_nan` returns a canonical number.
                    return Self::select_nan(self, rhs);
                };
                max.canonical()
            }

            /// Returns the maximum of the absolute values of
            /// `self` and `rhs`.
            ///
            /// If one operand is qNaN and the other is a finite
            /// number, it returns the finite number.
            ///
            /// See IEEE 754-2008 `maxNum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            #[cfg(test)]
            pub fn max_mag(self, rhs: Self) -> Self {
                if self.is_nan() || rhs.is_nan() {
                    self.max(rhs)
                } else {
                    use Ordering::*;
                    match self.copy_abs().partial_cmp_numeric(rhs.copy_abs()) {
                        Greater => self,
                        Less => rhs,
                        Equal => self.copy_abs().max(rhs.copy_abs()),
                    }
                }
            }

            /// Returns the maximum of `self` and `rhs`.
            ///
            /// Unlike [`max`][Self::max], this returns qNaN if
            /// either operand is NaN.
            ///
            /// See IEEE 754-2019 `maximum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub fn maximum(self, rhs: Self) -> Self {
                if cfg!(debug_assertions) {
                    println!("maximum({self}, {rhs})");
                    println!("cmp({self}, {rhs})={:?}", self.const_partial_cmp(rhs));
                }
                if self.is_numeric() && rhs.is_numeric() {
                    // Both are numeric, so `total_cmp` ensures
                    // that +0 > -0, etc.
                    use Ordering::*;
                    let max = match self.total_cmp(rhs) {
                        Greater | Equal => self,
                        Less => rhs,
                    };
                    max.canonical()
                } else {
                    Self::nan(false, 0)
                }
            }

            /// Returns the minimum of `self` and `rhs`.
            ///
            /// If one operand is qNaN and the other is a finite
            /// number, it returns the finite number.
            ///
            /// See IEEE 754-2008 `minNum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub fn min(self, rhs: Self) -> Self {
                if cfg!(debug_assertions) {
                    println!("min({self}, {rhs})");
                    println!("cmp({self}, {rhs})={:?}", self.const_partial_cmp(rhs));
                }
                let min = if self.is_numeric() && rhs.is_numeric() {
                    // Both are numeric, so `total_cmp` ensures
                    // that +0 > -0, etc.
                    use Ordering::*;
                    match self.total_cmp(rhs) {
                        Less | Equal => self,
                        Greater => rhs,
                    }
                } else if self.is_numeric() && rhs.is_qnan() {
                    self
                } else if self.is_qnan() && rhs.is_numeric() {
                    rhs
                } else {
                    // `select_nan` returns a canonical number.
                    return Self::select_nan(self, rhs);
                };
                min.canonical()
            }

            /// Returns the minimum of the absolute values of
            /// `self` and `rhs`.
            ///
            /// If one operand is qNaN and the other is a finite
            /// number, it returns the finite number.
            ///
            /// See IEEE 754-2008 `minNum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            #[cfg(test)]
            pub fn min_mag(self, rhs: Self) -> Self {
                if self.is_nan() || rhs.is_nan() {
                    self.min(rhs)
                } else {
                    use Ordering::*;
                    match self.copy_abs().partial_cmp_numeric(rhs.copy_abs()) {
                        Less => self,
                        Greater => rhs,
                        Equal => self.copy_abs().min(rhs.copy_abs()),
                    }
                }
            }

            /// Returns the minimum of `self` and `rhs`.
            ///
            /// Unlike [`min`][Self::min], this returns qNaN if
            /// either operand is NaN.
            ///
            /// See IEEE 754-2019 `minimum`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub fn minimum(self, rhs: Self) -> Self {
                if cfg!(debug_assertions) {
                    println!("minimum({self}, {rhs})");
                    println!("cmp({self},{rhs})={:?}", self.const_partial_cmp(rhs));
                }
                if self.is_numeric() && rhs.is_numeric() {
                    // Both are numeric, so `total_cmp` ensures
                    // that +0 > -0, etc.
                    use Ordering::*;
                    let min = match self.total_cmp(rhs) {
                        Less | Equal => self,
                        Greater => rhs,
                    };
                    min.canonical()
                } else {
                    Self::nan(false, 0)
                }
            }

            /// Returns `(self * a) + b` without any intermediate
            /// rounding.
            ///
            /// This is also known as "fused multiply add."
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn mul_add(self, _a: Self, _b: Self) -> Self {
                todo!()
            }

            /// Returns the largest representable number that is
            /// smaller than `self`.
            ///
            /// If `self` is `-Infinity`, it returns `-Infinity`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn next_minus(self) -> Self {
                if self.is_nan() {
                    return Self::select_nan(self, self);
                }
                if !self.signbit() && self.is_infinite() {
                    return Self::MAX;
                }
                // TODO(eric): round to -inf, not half-even.
                const TINY: $name = <$name>::new(-1, $name::ETINY);
                let mut next = self.const_add(TINY);
                if next.is_zero() {
                    next = next.copy_neg();
                }
                next
            }

            /// Returns the largest representable number that is
            /// larger than `self`.
            ///
            /// If `self` is `+Infinity`, it returns `+Infinity`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn next_plus(self) -> Self {
                if self.is_nan() {
                    return Self::select_nan(self, self);
                }
                if self.signbit() && self.is_infinite() {
                    return Self::MIN;
                }
                // TODO(eric): round to +inf, not half-even.
                const TINY: $name = <$name>::new(1, $name::ETINY);
                let mut next = self.const_add(TINY);
                if next.is_zero() {
                    next = next.copy_neg();
                }
                next
            }

            /// Returns the closest representable number to
            /// `self` that is in the direction of `rhs`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn next_toward(self, _rhs: Self) -> Self {
                todo!()
            }

            /// Returns a number equal (before rounding) to
            /// `self` and with the same sign as `self`, but with
            /// the exponent of `rhs`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub fn quantize(self, rhs: Self) -> Self {
                if self.is_special() || rhs.is_special() {
                    return if self.is_nan() || rhs.is_nan() {
                        Self::select_nan(self, rhs)
                    } else if self.is_infinite() && rhs.is_infinite() {
                        Self::nan(false, 0)
                    } else {
                        Self::inf(self.signbit())
                    };
                }

                if self.biased_exp() == rhs.biased_exp() {
                    // Already have the same exponent, so nothing
                    // to do.
                    return self.canonical();
                }

                if self.is_zero() {
                    return Self::new(0, rhs.unbiased_exp());
                }

                let diff = self.biased_exp().abs_diff(rhs.biased_exp()) as u32;
                debug_assert!(diff != 0);

                if cfg!(debug_assertions) {
                    println!("lhs = {} {}", self.biased_exp(), self.unbiased_exp());
                    println!("rhs = {} {}", rhs.biased_exp(), rhs.unbiased_exp());
                    println!("diff = {diff}");
                    println!("coeff = {} ({})", self.coeff(), self.digits());
                }

                if diff > Self::DIGITS {
                    // Too many digits.
                    return Self::nan(false, 0);
                }
                if self.biased_exp() < rhs.biased_exp() && self.digits() < diff {
                    return Self::new(0, rhs.unbiased_exp());
                }

                let coeff = if self.biased_exp() > rhs.biased_exp() {
                    if cfg!(debug_assertions) {
                        println!("{:?}", $arith::shl(self.coeff(), diff as u32));
                    }
                    $arith::shl(self.coeff(), diff).0
                } else {
                    $arith::shr(self.coeff(), diff).0
                };
                if cfg!(debug_assertions) {
                    println!("coeff = {coeff}");
                    println!("exp = {}", rhs.unbiased_exp());
                }
                Self::maybe_rounded(self.signbit(), rhs.unbiased_exp(), coeff)
            }

            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            #[cfg(test)]
            pub(crate) fn round_to_integral_exact(self) -> Self {
                if self.is_nan() {
                    Self::select_nan(self, self)
                } else if self.is_infinite() || self.unbiased_exp() >= 0 {
                    self
                } else {
                    // quantize(1e+0)
                    self.quantize(Self::new(1, 0))
                }
            }

            /// Returns the square root of `self`.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn sqrt(self) -> Self {
                if self.is_nan() {
                    // sqrt(±NaN)
                    return Self::select_nan(self, self);
                }
                let ideal = self.unbiased_exp() / 2;
                if self.is_zero() {
                    // sqrt(±0) == 0
                    return Self::from_parts(self.signbit(), ideal, 0);
                }
                if self.signbit() {
                    // sqrt(-x) == NaN
                    return Self::nan(false, 0);
                }
                if self.is_infinite() {
                    // sqrt(+inf) == +inf
                    return Self::inf(false);
                }

                const APPROX1: $name = $name::new(256, -3);
                const APPROX2: $name = $name::new(819, -3);
                const APPROX3: $name = $name::new(819, -4);
                const APPROX4: $name = $name::new(256, -1);
                const PT5: $name = $name::new(5, -1);

                let xprec = self.digits();
                let mut e = self.unbiased_exp() + xprec as $unbiased;
                let mut f = self.with_unbiased_exp(e);

                let mut approx = if e % 2 == 0 {
                    // approx := 0.259 + 0.819 * f
                    APPROX2.mul_add(f, APPROX1)
                } else {
                    // f := f/1-
                    f = f.with_unbiased_exp(f.unbiased_exp() - 1);
                    // e := e+1
                    e += 1;
                    // approx := 0.0819 + 2.59 * f
                    APPROX4.mul_add(f, APPROX3)
                };

                let mut p = 3;
                while p < $name::MAX_PREC {
                    p = 2 * p - 2;
                    if p > $name::MAX_PREC {
                        p = $name::MAX_PREC;
                    }
                    // approx := 0.5*(approx + f/approx)
                    approx = f.const_div(approx).const_add(approx).const_mul(PT5);
                }
                approx.with_unbiased_exp(e / 2)
            }
        }
    };
}
pub(crate) use impl_dec_arith;

macro_rules! impl_dec_misc {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        // Misc operations.
        // <https://speleotrove.com/decimal/damisc.html>
        impl $name {
            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn and(self, _rhs: Self) -> Self {
                todo!()
            }

            /// Converts the number to its canonical encoding.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn canonical(self) -> Self {
                if self.is_nan() {
                    $crate::bid::canonical!(self.0 & Self::CANONICAL_NAN)
                } else if self.is_infinite() {
                    $crate::bid::canonical!(self.0 & Self::CANONICAL_INF)
                } else if self.raw_coeff() > Self::MAX_COEFF as $ucoeff {
                    Self::zero()
                } else {
                    self
                }
            }

            #[cfg(test)]
            pub(crate) const fn class(self) -> &'static str {
                use FpCategory::*;
                match self.classify() {
                    Nan => {
                        if self.is_snan() {
                            "sNaN"
                        } else {
                            "NaN"
                        }
                    }
                    Infinite => {
                        if self.signbit() {
                            "-Infinity"
                        } else {
                            "+Infinity"
                        }
                    }
                    Zero => {
                        if self.signbit() {
                            "-Zero"
                        } else {
                            "+Zero"
                        }
                    }
                    Normal => {
                        if self.signbit() {
                            "-Normal"
                        } else {
                            "+Normal"
                        }
                    }
                    Subnormal => {
                        if self.signbit() {
                            "-Subnormal"
                        } else {
                            "+Subnormal"
                        }
                    }
                }
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

            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn const_not(self) -> Self {
                todo!()
            }

            /// Returns the absolute value of `self`.
            ///
            /// Unlike [`abs`][Self::abs], this operation has no
            /// special NaN handling and may return
            /// a non-canonical result.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn copy_abs(self) -> Self {
                Self(self.0 & !Self::SIGN_MASK)
            }

            /// Returns `-self`.
            ///
            /// Unlike [`neg`][core::ops::Neg], this operation
            /// has no special NaN handling and may return
            /// a non-canonical result.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn copy_neg(self) -> Self {
                Self(self.0 ^ Self::SIGN_MASK)
            }

            /// Returns `self` with the same sign as `rhs`.
            ///
            /// This operation has no special NaN handling and
            /// may return a non-canonical result.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn copy_sign(self, rhs: Self) -> Self {
                let mut bits = self.0;
                bits &= !Self::SIGN_MASK;
                bits |= (rhs.0 & Self::SIGN_MASK);
                Self(bits)
            }

            /// Reports whether the number is in its canonical
            /// format.
            pub const fn is_canonical(self) -> bool {
                if self.is_nan() {
                    self.0 & !Self::CANONICAL_NAN == 0
                } else if self.is_infinite() {
                    self.0 & !Self::CANONICAL_INF == 0
                } else {
                    self.raw_coeff() <= Self::MAX_COEFF as $ucoeff
                }
            }

            /// Reports whether the number is neither infinite
            /// nor NaN.
            pub const fn is_finite(self) -> bool {
                !self.is_special()
            }

            /// Reports whether the number is either positive or
            /// negative infinity.
            pub const fn is_infinite(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN. The fifth bit
                // signals NaN.
                self.0 & Self::COMB_TOP5 == Self::COMB_TOP4
            }

            /// Reports whether the number is a NaN.
            pub const fn is_nan(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN. The fifth bit
                // signals NaN.
                self.0 & Self::COMB_TOP5 == Self::COMB_TOP5
            }

            /// Reports whether the number is neither zero,
            /// infinite, subnormal, or NaN.
            pub const fn is_normal(self) -> bool {
                if self.is_special() || self.is_zero() {
                    return false;
                }
                debug_assert!(self.is_finite());

                // TODO(eric): non-canonical?

                self.adjusted_exp() >= Self::MIN_EXP
            }

            /// Reports whether the number is a quiet NaN.
            pub const fn is_qnan(self) -> bool {
                // When the number is a NaN, the sixth
                // combination bit signals whether the NaN is
                // signaling.
                self.0 & Self::COMB_TOP6 == Self::COMB_TOP5
            }

            /// Reports whether the number is negative, including
            /// `-0.0`.
            pub const fn is_sign_negative(self) -> bool {
                self.signbit()
            }

            /// Reports whether the number is positive, including
            /// `+0.0`.
            pub const fn is_sign_positive(self) -> bool {
                !self.is_sign_negative()
            }

            /// Reports whether the number is a signaling NaN.
            pub const fn is_snan(self) -> bool {
                // When the number is a NaN, the sixth
                // combination bit signals whether the NaN is
                // signaling.
                self.0 & Self::COMB_TOP6 == Self::COMB_TOP6
            }

            /// Reports whether the number is subnormal.
            pub const fn is_subnormal(self) -> bool {
                !self.is_special() && !self.is_zero() && !self.is_normal()
            }

            /// Reports whether the number is `-0.0` or `+0.0`.
            pub const fn is_zero(self) -> bool {
                // A number is zero if it is finite and the
                // coefficient is zero.
                if !self.is_finite() {
                    return false;
                }
                // NB: Checking `self.is_form1` helps the
                // compiler generate much better code.
                if !self.is_form1() {
                    return false;
                }
                // We're finite and using form one, so check that
                // the coefficient is zero. However, we also have
                // to account for the fact that a coefficient
                // greater than `MAX_COEFF` is treated as if it
                // were zero.
                //
                // NB: The compiler generates worse code for the
                // obvious version.
                const MAX_COEFF: $ucoeff = $name::MAX_COEFF as $ucoeff;
                let diff = (MAX_COEFF as $ucoeff).checked_sub(self.raw_coeff());
                matches!(diff, None | Some(MAX_COEFF))
            }

            /// Returns an integer that is the exponent of the
            /// magnitude of the most significant digit.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn logb(self) -> Self {
                todo!()
            }

            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn or(self, _rhs: Self) -> Self {
                todo!()
            }

            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            #[cfg(test)]
            pub(crate) fn plus(self) -> Self {
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

            /// Returns the base in which arithmetic is effected.
            pub const fn radix() -> u32 {
                10
            }

            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn rotate(self, _rhs: Self) -> Self {
                todo!()
            }

            /// Reports whether `self` and `rhs` have the same
            /// exponent.
            ///
            /// If either operand is an infinity or a NaN, it
            /// only returns true if both operands are infinity
            /// or NaN.
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn same_quantum(self, rhs: Self) -> bool {
                if self.is_finite() && rhs.is_finite() {
                    self.biased_exp() == rhs.biased_exp()
                } else {
                    // At least one operand is non-finite. This
                    // helps the compiler generate better code
                    // than doing it the obvious way.
                    //
                    // Right shifting by one discards the sNaN
                    // bit.
                    self.special_bits() >> 1 == rhs.special_bits() >> 1
                }
            }

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
                let mut exp = self.biased_exp() + n as $biased;
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
            pub const fn shift(self, _rhs: Self) -> Self {
                todo!()
            }

            /// Returns the total ordering between `self` and
            /// `rhs`.
            ///
            /// The values are ordered as follows:
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
            /// `total_cmp` doesn't.
            ///
            /// See IEEE 754-2008 `totalOrder`.
            pub const fn total_cmp(self, rhs: Self) -> Ordering {
                if self.signbit() != rhs.signbit() {
                    return if self.signbit() {
                        // -x < +x
                        Ordering::Less
                    } else {
                        // +x > -x
                        Ordering::Greater
                    };
                }
                // Signs are the same.
                debug_assert!(self.signbit() == rhs.signbit());

                let ord = self.total_cmp_abs(rhs);
                return if self.signbit() { ord.reverse() } else { ord };
            }

            /// `totalOrder`, but without comparing signs.
            const fn total_cmp_abs(self, rhs: Self) -> Ordering {
                debug_assert!(self.signbit() == rhs.signbit());

                if self.to_bits() == rhs.to_bits() {
                    // Same bits, so obviously equal.
                    return Ordering::Equal;
                }

                if !self.is_finite() || !rhs.is_finite() {
                    return match $crate::bid::util::const_cmp_u8(
                        self.special_ord(),
                        rhs.special_ord(),
                    ) {
                        Ordering::Equal if self.is_nan() => {
                            // Both are the same type of NaN.
                            // Compare the payloads.
                            let lhs_pl = self.payload();
                            let rhs_pl = rhs.payload();
                            $arith::const_cmp(lhs_pl, rhs_pl)
                        }
                        ord => ord,
                    };
                }
                // Both are finite.
                debug_assert!(self.is_finite() && rhs.is_finite());

                match self.total_cmp_abs_finite(rhs) {
                    Ordering::Equal => match self.biased_exp().checked_sub(rhs.biased_exp()) {
                        Some(0) => Ordering::Equal,
                        Some(_) => Ordering::Greater,
                        None => Ordering::Less,
                    },
                    ord => ord,
                }
            }

            const fn total_cmp_abs_finite(self, rhs: Self) -> Ordering {
                debug_assert!(self.is_finite() && rhs.is_finite());

                if self.is_zero() || rhs.is_zero() {
                    return if !self.is_zero() {
                        // x > 0
                        Ordering::Greater
                    } else if !rhs.is_zero() {
                        // 0 < x
                        Ordering::Less
                    } else {
                        Ordering::Equal
                    };
                }
                // Both are non-zero.
                debug_assert!(!self.is_zero() && !rhs.is_zero());

                // Bias doesn't matter for this comparison.
                let shift = self.biased_exp().abs_diff(rhs.biased_exp()) as u32;
                if shift >= Self::DIGITS {
                    // The shift is larger than the maximum
                    // precision, so the coefficients do not
                    // overlap. Therefore, the larger exponent is
                    // the larger number.
                    return if self.biased_exp() < rhs.biased_exp() {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                }
                // `shift` is in [0, DIGITS].

                if shift == 0 {
                    $arith::const_cmp(self.coeff(), rhs.coeff())
                } else if self.biased_exp() > rhs.biased_exp() {
                    $arith::const_cmp_shifted(self.coeff(), rhs.coeff(), shift)
                } else {
                    $arith::const_cmp_shifted(rhs.coeff(), self.coeff(), shift).reverse()
                }
            }

            /// Equivalent to [`total_cmp`][Self::total_cmp], but
            /// with both signs assumed to be zero.
            pub const fn total_cmp_magnitude(self, rhs: Self) -> Ordering {
                // NB: This is equivalent to
                // `self.abs().total_cmp(rhs.abs())`
                self.total_cmp_abs(rhs)
            }

            /// TODO
            #[must_use = "this returns the result of the operation \
                              without modifying the original"]
            pub const fn xor(self, _rhs: Self) -> Self {
                todo!()
            }
        }
    };
}
pub(crate) use impl_dec_misc;

macro_rules! impl_dec_misc2 {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident $(,)?
    ) => {
        impl $name {
            /// Returns the number of significant digits in the
            /// number.
            ///
            /// If the number is infinity or zero, it returns 1.
            /// If the number is NaN, it returns the number of
            /// digits in the payload.
            ///
            /// The result will always be in [1,
            /// [`DIGITS`][Self::DIGITS]].
            pub const fn digits(self) -> u32 {
                if self.is_finite() {
                    $arith::digits(self.coeff())
                } else if self.is_nan() {
                    $arith::digits(self.payload())
                } else {
                    1 // infinite
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
        }
    };
}
pub(crate) use impl_dec_misc2;

macro_rules! impl_dec_to_from_repr {
    (
        $name:ident,
        $ucoeff:ty,
        $icoeff:ty,
        $biased:ty,
        $unbiased:ty,
        $comb:ty,
        $arith:ident,
        $dpd:ty $(,)?
    ) => {
        // To/from repr.
        impl $name {
            /// Creates a number from its coefficient and
            /// exponent.
            pub const fn new(coeff: $icoeff, exp: $unbiased) -> Self {
                Self::maybe_rounded(coeff < 0, exp, coeff.unsigned_abs())
            }

            /// Creates a number from its raw bits.
            ///
            /// ```rust
            /// use rdfp::d128;
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
                Self(<$ucoeff>::from_le_bytes(bytes))
            }

            /// Creates a number from a big-endian byte array.
            pub const fn from_be_bytes(bytes: [u8; Self::BYTES]) -> Self {
                Self(<$ucoeff>::from_be_bytes(bytes))
            }

            /// Creates a number from a native-endian byte array.
            pub const fn from_ne_bytes(bytes: [u8; Self::BYTES]) -> Self {
                Self(<$ucoeff>::from_ne_bytes(bytes))
            }

            /// Raw transmutation to the number's raw bit
            /// representation.
            pub const fn to_bits(self) -> $ucoeff {
                self.0
            }

            /// Converts the number to a densely packed decimal.
            pub const fn to_dpd(self) -> $dpd {
                if self.is_nan() {
                    let payload = <$dpd>::pack_bin(self.payload());
                    if self.is_snan() {
                        <$dpd>::snan(self.signbit(), payload)
                    } else {
                        <$dpd>::nan(self.signbit(), payload)
                    }
                } else if self.is_infinite() {
                    <$dpd>::inf(self.signbit())
                } else {
                    <$dpd>::from_parts_bin(self.signbit(), self.unbiased_exp(), self.coeff())
                }
            }

            /// Converts the DPD to a number.
            pub const fn from_dpd(dpd: $dpd) -> Self {
                if dpd.is_nan() {
                    if dpd.is_snan() {
                        Self::snan(dpd.signbit(), dpd.payload_bin())
                    } else {
                        Self::nan(dpd.signbit(), dpd.payload_bin())
                    }
                } else if dpd.is_infinite() {
                    Self::inf(dpd.signbit())
                } else {
                    Self::from_parts(dpd.signbit(), dpd.unbiased_exp(), dpd.full_coeff_bin())
                }
            }
        }

        impl From<$dpd> for $name {
            fn from(dpd: $dpd) -> Self {
                Self::from_dpd(dpd)
            }
        }
    };
}
pub(crate) use impl_dec_to_from_repr;

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
