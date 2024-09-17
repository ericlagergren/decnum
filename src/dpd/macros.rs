macro_rules! impl_dpd {
    (
        $(#[$meta:meta])*
        name = $name:ident,
        ucoeff = $ucoeff:ty,
        icoeff = $icoeff:ty,
        biased_exp = $biased:ty,
        unbiased_exp = $unbiased:ty,
        comb = $comb:ty,
        pack = $pack:ident,
        unpack = $unpack:ident,
        bid = $bid:ty,
    ) => {
        $(#[$meta])*
        #[derive(Copy, Clone)]
        #[repr(transparent)]
        pub struct $name($ucoeff);

        // Internal stuff.
        impl $name {
            const SIGN_SHIFT: u32 = <$bid>::SIGN_SHIFT;

            /// The shift needed to the five-bit combination
            /// field.
            const COMB_SHIFT: u32 = <$bid>::K - 1 - 5;

            // Exponent continuation field bits.
            const ECON_BITS: u32 = <$bid>::W;
            const ECON_SHIFT: u32 = <$bid>::K - 1 - 5 - Self::ECON_BITS;

            pub(crate) const fn signbit(self) -> bool {
                const MASK: $ucoeff = 1 << $name::SIGN_SHIFT;
                (self.0 & MASK) != 0
            }

            /// Returns the five-bit combination field.
            const fn comb(self) -> u8 {
                ((self.0 >> Self::COMB_SHIFT) & 0x1f) as u8
            }

            /// Returns the exponent continuation field.
            const fn econ(self) -> $biased {
                const MASK: $ucoeff = (1 << $name::ECON_BITS) - 1;
                ((self.0 >> Self::ECON_SHIFT) & MASK) as $biased
            }

            /// Returns the biased exponment.
            ///
            /// If the number is finite, the result is in [0,
            /// [`LIMIT`][Self::LIMIT]].
            pub(crate) const fn biased_exp(self) -> $biased {
                // The exponent only has meaning for finite
                // numbers.
                debug_assert!(self.is_finite());

                const AB: u8 = 0b11000;
                const CD: u8 = 0b00110;

                let comb = self.comb();
                let msb = match comb & AB {
                    // If bits `ab` are both set, then the MSBs
                    // are encoded in bits `cd`. Otherwise, the
                    // MSBs are encoded in `ab`.
                    AB => (comb  & CD) >>1,
                    b => b >> 3,
                };
                debug_assert!(msb <= 2);

                let exp = ((msb as $biased) << Self::ECON_BITS) | self.econ();

                debug_assert!(exp & !<$bid>::EXP_MASK == 0);
                debug_assert!(exp <= <$bid>::LIMIT);

                exp
            }

            /// Returns the unbiased exponent.
            ///
            /// If the number is finite, the result is in
            /// [`ETINY`, `EMAX`].
            pub(crate) const fn unbiased_exp(self) -> $unbiased {
                $crate::util::const_assert!(<$bid>::LIMIT.checked_add_signed(<$bid>::BIAS).is_some());

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
                let exp = (self.biased_exp() as $unbiased) - <$bid>::BIAS;

                debug_assert!(exp >= <$bid>::ETINY);
                debug_assert!(exp <= <$bid>::EMAX);

                exp
            }

            /// Returns the coefficient, less the MSD, as a DPD.
            const fn coeff(self) -> $ucoeff {
                debug_assert!(self.is_finite());

                self.0 & <$bid>::COEFF_MASK
            }

            /// Returns the coefficient, including the MSD, as
            /// a DPD.
            const fn full_coeff(self) -> $ucoeff {
                debug_assert!(self.is_finite());

                const AB: u8 = 0b11000;
                const CD: u8 = 0b00110;
                const E_: u8 = 0b00001;

                let comb = self.comb();
                let msd = match comb & AB {
                    AB => 0x8 | (comb & E_), // 100e
                    _ => comb & (CD | E_), // 0cde
                };
                // `msd` is either `100e` (9 or 8) or
                // `0cde` (0 through 7).
                debug_assert!(msd <= 9);
                self.coeff() | ((msd as $ucoeff) << <$bid>::COEFF_BITS)
            }

            /// Returns the full coefficient as a binary number.
            pub(crate) const fn full_coeff_bin(self) -> $ucoeff {
                $unpack(self.full_coeff())
            }

            /// Returns the payload.
            const fn payload(self) -> $ucoeff {
                debug_assert!(self.is_nan());

                self.0 & <$bid>::PAYLOAD_MASK
            }

            /// Returns the payload as a binary number.
            pub(crate) const fn payload_bin(self) -> $ucoeff {
                $unpack(self.payload())
            }

            pub(crate) const fn from_parts_bin(sign: bool, exp: $unbiased, bin: $ucoeff) -> Self {
                debug_assert!(bin <= <$bid>::MAX_COEFF as $ucoeff);
                debug_assert!(exp >= <$bid>::EMIN_LESS_PREC);
                debug_assert!(exp <= <$bid>::EMAX_LESS_PREC);

                Self::from_parts_dpd(sign, exp, $pack(bin))
            }

            const fn from_parts_dpd(sign: bool, exp: $unbiased, dpd: $ucoeff) -> Self {
                debug_assert!(exp >= <$bid>::EMIN_LESS_PREC);
                debug_assert!(exp <= <$bid>::EMAX_LESS_PREC);

                // TODO(eric): If `exp` is valid then this cannot
                // overflow. Maybe make sure of it?
                #[allow(clippy::cast_sign_loss)]
                let biased = (exp + <$bid>::BIAS) as $biased;

                let comb = {
                    let msd = ((dpd >> <$bid>::COEFF_BITS) & 0x9) as u8;
                    debug_assert!(msd <= 9);

                    let msb = ((biased >> (<$bid>::EXP_BITS - 2)) & 0x3) as u8;
                    debug_assert!(msb <= 2);

                    // [0, 7] -> 0cde
                    // [8, 9] -> 100e
                    if msd <= 7 {
                        (msb << 3) | msd
                    } else {
                        0x18 | (msb << 1) | msd
                    }
                };

                const LSB: $biased = (1 << (<$bid>::EXP_BITS - 2)) - 1;
                let econ = biased & LSB;
                let coeff = dpd & <$bid>::COEFF_MASK;

                let mut bits = 0;
                bits |= (sign as $ucoeff) << <$bid>::SIGN_SHIFT;
                bits |= (comb as $ucoeff) << Self::COMB_SHIFT;
                bits |= (econ as $ucoeff) << Self::ECON_SHIFT;
                bits |= coeff;
                Self(bits)
            }
        }

        // Public stuff.
        impl $name {
            /// Reports whether the number is neither infinite nor NaN.
            const fn is_finite(self) -> bool {
                !self.is_special()
            }

            /// Reports whether the number is infinite or NaN.
            const fn is_special(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN.
                self.0 & <$bid>::COMB_TOP4 == <$bid>::COMB_TOP4
            }

            /// Reports whether the number is either positive or negative
            /// infinity.
            pub(crate) const fn is_infinite(self) -> bool {
                self.0 & <$bid>::COMB_TOP5 == <$bid>::COMB_TOP4
            }

            /// Reports whether the number is a NaN.
            pub(crate) const fn is_nan(self) -> bool {
                // When the first (top) four bits of the
                // combination field are set, the number is
                // either an infinity or a NaN. The fifth bit
                // signals NaN.
                self.0 & <$bid>::COMB_TOP5 == <$bid>::COMB_TOP5
            }

            /// Reports whether the number is a signaling NaN.
            pub(crate) const fn is_snan(self) -> bool {
                // When the number is a NaN, the sixth
                // combination bit signals whether the NaN is
                // signaling.
                self.0 & <$bid>::COMB_TOP6 == <$bid>::COMB_TOP6
            }

            pub(crate) const fn pack_bin(bin: $ucoeff) -> $ucoeff {
                $pack(bin)
            }
        }

        // To/from reprs.
        impl $name {
            /// Creates a quiet NaN.
            pub(crate) const fn nan(sign: bool, payload: $ucoeff) -> Self {
                let mut bits = 0;
                bits |= (sign as $ucoeff) << <$bid>::SIGN_SHIFT;
                bits |= <$bid>::COMB_TOP5;
                bits |= payload;
                Self(bits)
            }

            /// Creates a signaling NaN.
            pub(crate) const fn snan(sign: bool, payload: $ucoeff) -> Self {
                let mut bits = 0;
                bits |= (sign as $ucoeff) << <$bid>::SIGN_SHIFT;
                bits |= <$bid>::COMB_TOP6;
                bits |= payload;
                Self(bits)
            }

            /// Creates an infinity.
            pub(crate) const fn inf(sign: bool) -> Self {
                let mut bits = 0;
                bits |= (sign as $ucoeff) << <$bid>::SIGN_SHIFT;
                bits |= <$bid>::COMB_TOP4;
                Self(bits)
            }

            /// Creates a number from its raw bits.
            pub const fn from_bits(bits: $ucoeff) -> Self {
                Self(bits)
            }

            /// Creates a number from a little-endian byte array.
            pub const fn from_le_bytes(bytes: [u8; <$bid>::BYTES]) -> Self {
                Self(<$ucoeff>::from_le_bytes(bytes))
            }

            /// Creates a number from a big-endian byte array.
            pub const fn from_be_bytes(bytes: [u8; <$bid>::BYTES]) -> Self {
                Self(<$ucoeff>::from_be_bytes(bytes))
            }

            /// Creates a number from a native-endian byte array.
            pub const fn from_ne_bytes(bytes: [u8; <$bid>::BYTES]) -> Self {
                Self(<$ucoeff>::from_ne_bytes(bytes))
            }

            /// Raw transmutation.
            pub const fn to_bits(self) -> $ucoeff {
                self.0
            }

            /// Converts the number to a little-endian byte
            /// array.
            pub const fn to_le_bytes(self) -> [u8; <$bid>::BYTES] {
                self.0.to_le_bytes()
            }

            /// Converts the number to a big-endian byte array.
            pub const fn to_big_bytes(self) -> [u8; <$bid>::BYTES] {
                self.0.to_be_bytes()
            }

            /// Converts the number to a native-endian byte
            /// array.
            pub const fn to_ne_bytes(self) -> [u8; <$bid>::BYTES] {
                self.0.to_ne_bytes()
            }

            /// Converts the number to a BID.
            pub const fn to_bid(self) -> $bid {
                <$bid>::from_dpd(self)
            }

            /// Converts `bid` to a DPD.
            pub const fn from_bid(bid: $bid) -> Self {
                bid.to_dpd()
            }
        }

        impl From<$bid> for $name {
            fn from(bid: $bid) -> Self {
                Self::from_bid(bid)
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                PartialEq::eq(&self.to_bid(), &other.to_bid())
            }
        }

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                PartialOrd::partial_cmp(&self.to_bid(), &other.to_bid())
            }
        }

        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                self.to_bid().fmt(f)
            }
        }

        impl ::core::fmt::Binary for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::Binary::fmt(&self.0, f)
            }
        }

        impl ::core::fmt::LowerExp for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                self.to_bid().fmt(f)
            }
        }

        impl ::core::fmt::UpperExp for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                self.to_bid().fmt(f)
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                self.to_bid().fmt(f)
            }
        }
    };
}
pub(crate) use impl_dpd;
