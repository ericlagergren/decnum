//! BCD conversion routines.

use core::{
    cmp::Ordering,
    fmt,
    hash::Hash,
    mem::{self, size_of},
    str::{self, FromStr},
};

use super::{dpd, util::assume};

macro_rules! bcd_int_impl {
    (
        $name:ident,
        $digits:literal,
        $bcd:ty,
        $dpd:ty,
        $bin:ty $(,)?
    ) => {
        const _: () = {
            assert!(<$name>::BITS < <$bcd>::BITS as $bcd);
            assert!(<$name>::BITS % 4 == 0);
        };

        #[doc = concat!("A BCD with ", stringify!($digits), " digits.")]
        #[derive(Copy, Clone, Default, Hash, Eq, PartialEq)]
        pub struct $name {
            // The least significant digit is the first nibble.
            bcd: $bcd,
        }

        impl $name {
            /// The maximum number of digits in the BCD.
            pub const DIGITS: usize = $digits;

            /// The number of bits in `bcd` to use.
            const BITS: $bcd = $digits * 4;
            /// A mask covering the bits that may be used.
            const MASK: $bcd = ((1 as $bcd) << Self::BITS) - 1;
            /// The number of 10-bit DPDs this BCD packs into.
            const NUM_DPDS: usize = ((Self::BITS + 9) / 10) as usize;
            /// A mask covering the unused bits in a DPD.
            const INVALID_DPD: $dpd = !(((1 as $dpd) << (Self::NUM_DPDS * 10)) - 1);

            /// The max value for `$bin`.
            #[cfg(test)]
            #[allow(dead_code)]
            const BIN_MAX: $bin = <$bin>::MAX;

            const fn new(bcd: $bcd) -> Self {
                let bcd = Self { bcd };
                bcd.debug_check();
                bcd
            }

            const fn debug_check(self) {
                debug_assert!(self.bcd & !<$name>::MASK == 0);

                /// Reports whether the BCD is valid.
                ///
                /// For a BCD to be valid, each nibble may only
                /// have one of the following bit patterns:
                ///
                /// 0. `0000`
                /// 1. `0001`
                /// 2. `0010`
                /// 3. `0011`
                /// 4. `0100`
                /// 5. `0101`
                /// 6. `0110`
                /// 7. `0111`
                /// 8. `1000`
                /// 9. `1001`
                const fn is_valid(bcd: $bcd) -> bool {
                    /// Construct a bitmask where each nibble is
                    /// the same.
                    macro_rules! mask {
                        ($nibble:literal) => {{
                            const { assert!($nibble <= 0xf) }

                            let mut v = 0;
                            let mut s = 0;
                            while s < <$bcd>::BITS {
                                v |= ($nibble as $bcd) << s;
                                s += 4;
                            }
                            v
                        }};
                    }
                    const MASK1: $bcd = mask!(0b0111); // 0x777...
                    const MASK2: $bcd = mask!(0b0011); // 0x333...
                    const MASK3: $bcd = mask!(0b1000); // 0x888...
                    let half = (bcd >> 1) & MASK1;
                    ((half + MASK2) & MASK3) == 0
                }
                debug_assert!(is_valid(self.bcd));
            }

            /// Returns the all-zero BCD.
            pub const fn zero() -> Self {
                Self::new(0)
            }

            /// Creates a BCD from a binary number.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd10;
            ///
            /// let x = Bcd10::from_bin(u32::MAX).to_bin();
            /// assert_eq!(x, u32::MAX);
            /// ```
            pub const fn from_bin(bin: $bin) -> Self {
                let mut bin = bin as $bcd;
                let mut bcd = 0;
                let mut s = 0;
                while s < Self::BITS {
                    bcd |= (bin % 10) << s;
                    s += 4;
                    bin /= 10;
                }
                Self::new(bcd)
            }

            /// Parses a BCD from a string.
            ///
            /// The string is allowed to contain insignificant
            /// leading zeros.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd10;
            ///
            /// let x = Bcd10::from_str("1234").unwrap();
            /// let y = Bcd10::from_str("01234").unwrap();
            /// assert_eq!(x, y);
            ///
            /// let x: Bcd10 = "1234".parse().unwrap();
            /// let y: Bcd10 = "01234".parse().unwrap();
            /// assert_eq!(x, y);
            /// ```
            pub const fn from_str(s: &str) -> Result<Self, ParseBcdError> {
                let buf = s.as_bytes();
                if buf.len() > Self::DIGITS {
                    return Err(ParseBcdError(()));
                }
                if buf.is_empty() {
                    return Ok(Self::zero());
                }

                let mut bcd = 0;
                let mut i = 0;
                let mut s = (buf.len() - 1) * 4;
                while i < buf.len() {
                    let c = buf[i];
                    if c < b'0' || c > b'9' {
                        return Err(ParseBcdError(()));
                    }
                    let d = (c - b'0') as $bcd;
                    bcd |= d << s;
                    i += 1;
                    // Handle the case where `buf.len() == 1` and
                    // `s` starts out at zero.
                    s = s.saturating_sub(4);
                }
                Ok(Self::new(bcd))
            }

            /// Converts the BCD to a binary number.
            pub const fn to_bin(self) -> $bin {
                self.debug_check();

                let mut bin = 0;
                let mut s = 0;
                let mut p = 1;
                while s < Self::BITS {
                    debug_assert!(p != <$bin>::MAX);

                    bin += (((self.bcd >> s) & 0xf) as $bin) * p;
                    s += 4;
                    p = p.saturating_mul(10);
                }
                bin
            }

            /// Packs the BCD into a DPD.
            pub const fn pack(self) -> $dpd {
                self.debug_check();

                let mut dpd = 0;
                let mut shl = 0;
                let mut shr = 0;
                let mut i = 0;
                while i < <$name>::NUM_DPDS {
                    let bcd = (self.bcd >> shr) & 0xfff;
                    // This check removes the bounds checks from
                    // the call to `dpd:pack`.
                    //
                    // SAFETY: `self.bcd` never has any invalid
                    // digits, so its maximum value is 0x999.
                    unsafe { assume(bcd <= 0x999) }
                    dpd |= (dpd::pack(bcd as u16) as $dpd) << shl;
                    shl += 10;
                    shr += 12;
                    i += 1;
                }
                dpd
            }

            /// Unpacks the DPD into a BCD.
            ///
            /// If the DPD is too large, excess bits are
            /// discarded.
            pub fn unpack(dpd: $dpd) -> Self {
                let mut bcd = 0;
                let mut shl = 0;
                let mut shr = 0;
                let mut i = 0;
                while i < <$name>::NUM_DPDS {
                    let dpd = (dpd >> shr) & 0x3ff;
                    bcd |= (dpd::unpack(dpd as u16) as $bcd) << shl;
                    shr += 10;
                    shl += 12;
                    i += 1;
                }
                Self::new(bcd)
            }

            /// Unpacks the DPD into a BCD.
            ///
            /// Returns `None` if the DPD is too large.
            pub fn try_unpack(dpd: $dpd) -> Option<Self> {
                if dpd & Self::INVALID_DPD != 0 {
                    None
                } else {
                    Some(Self::unpack(dpd))
                }
            }

            /// Reports whether the BCD is zero.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd10;
            ///
            /// assert!(Bcd10::from_bin(0).is_zero());
            /// assert!(!Bcd10::from_bin(1).is_zero());
            /// ```
            pub const fn is_zero(&self) -> bool {
                self.debug_check();

                self.bcd == 0
            }

            /// Encodes the BCD to a string.
            ///
            /// The returned string does not contain
            /// insignificant leading zeros.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd10;
            ///
            /// let bcd = Bcd10::from_bin(1234);
            /// let mut buf = [0u8; Bcd10::DIGITS];
            /// let s = bcd.encode(&mut buf);
            /// assert_eq!(s, "1234");
            /// ```
            pub fn encode<'a>(self, buf: &'a mut [u8; $digits]) -> &'a str {
                self.debug_check();

                let s = self.encode_full(buf).trim_start_matches('0');
                if s.is_empty() {
                    "0"
                } else {
                    s
                }
            }

            /// Encodes the BCD to a string.
            ///
            /// The string contains insignificant leading zeros.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd10;
            ///
            /// let bcd = Bcd10::from_bin(1234);
            /// let mut buf = [0u8; Bcd10::DIGITS];
            /// let s = bcd.encode_full(&mut buf);
            /// assert_eq!(s, "01234");
            /// ```
            pub fn encode_full<'a>(self, buf: &'a mut [u8; $digits]) -> &'a str {
                self.debug_check();

                let mut bcd = self.bcd;
                for c in buf.iter_mut().rev() {
                    let d = (bcd & 0xf) as u8;
                    *c = d + b'0';
                    bcd >>= 4;
                }
                debug_assert!(str::from_utf8(buf).is_ok());

                // SAFETY: The buffer is guaranteed to be ASCII.
                unsafe { str::from_utf8_unchecked(buf) }
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                Ord::cmp(&self.to_bin(), &other.to_bin())
            }
        }
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(Ord::cmp(self, other))
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut buf = [0u8; Self::DIGITS];
                let str = self.encode(&mut buf);
                write!(f, "{str}")
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut buf = [[0, 0]; (Self::DIGITS + 1) / 2];
                let mut bcd = self.bcd;
                for [lo, hi] in &mut buf {
                    *lo = (bcd & 0xf) as u8;
                    *hi = (bcd >> 4) as u8;
                    bcd >>= 8;
                }
                f.debug_struct(stringify!($name))
                    .field("bcd", &buf)
                    .finish()
            }
        }

        impl FromStr for $name {
            type Err = ParseBcdError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <$name>::from_str(s)
            }
        }
    };
}
bcd_int_impl!(Bcd5, 5, u32, u32, u16);
bcd_int_impl!(Bcd10, 10, u64, u64, u32);

/// Converts the 12-bit BCD to a binary number.
pub const fn to_bin(bcd: u16) -> u16 {
    let mut bin = 0;
    let mut s = 0;
    while s < 12 {
        bin += (bcd >> s) & 0xf;
        bin *= 10;
        s += 4;
    }
    bin
}

/// Creates a 12-bit BCD from a binary number.
///
/// # Example
///
/// ```
/// use decnum::bcd;
///
/// let bcd = bcd::from_bin(1234);
/// assert_eq!(bcd, 0x1234);
/// ```
pub const fn from_bin(mut bin: u16) -> u16 {
    let mut bcd = 0;
    let mut s = 0;
    while s < 12 {
        bcd |= (bin % 10) << s;
        s += 4;
        bin /= 10;
    }
    bcd
}

/// Converts a 12-bit BCD to a string.
pub(super) const fn to_str(bcd: u16) -> Str3 {
    let mut w = 0;
    // Rewrite 0x0123 as 0x00030201.
    w |= ((bcd & 0x000f) as u32) << 16;
    w |= ((bcd & 0x00f0) as u32) << 4;
    w |= ((bcd & 0x0f00) as u32) >> 8;
    w |= 0x00303030; // b'0' | b'0'<<8 | ...

    // Using transmute is ugly, but LLVM refuses to optimize
    // a safe version like
    //
    // ```
    // let b = w.to_le_bytes();
    // [b[0], b[1], b[2]]
    // ```
    //
    // SAFETY: `[u8; 3]` is smaller than `[u8; 4]`.
    unsafe { mem::transmute_copy(&w.to_le_bytes()) }
}

/// A 12-bit BCD converted to a three-byte string.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Str3(u32);

impl Str3 {
    pub(super) const fn zero() -> Self {
        Self(0)
    }

    /// Converts the string to bytes.
    pub const fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    /// TODO
    pub const fn len(self) -> usize {
        const MASK: u32 = 0x00303030; // b'0' | b'0'<<8 | ...
        let w = self.0 & !MASK;
        ((w | 0xff000000).trailing_zeros() / 8) as usize
    }

    /// Trims leading '0' bytes from the string.
    pub const fn trimmed(self) -> TrimmedStr3 {
        const MASK: u32 = 0x00303030; // b'0' | b'0'<<8 | ...
        let mut w = self.0 & !MASK;
        // Get rid if insignificant leading zeros. For example,
        // if we convert 0x0042 to 0x00020400, we need to shift
        // off the rightmost byte.
        let zeros = (w | 0xff000000).trailing_zeros() / 8;
        w >>= zeros * 8;
        // Add in the number of significant digits.
        w |= ((3 - zeros) + (w == 0) as u32) << 24;
        w |= MASK;
        TrimmedStr3(w)
    }
}

impl fmt::Display for Str3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let b = &self.to_bytes();
        // SAFETY: Up to `self.len()` bytes are valid UTF-8.
        let s = unsafe { str::from_utf8_unchecked(b) };
        write!(f, "{s}")
    }
}

/// Like [`Str3`], but without leading zeros.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct TrimmedStr3(
    // The first 24 bits are UTF-8 digits.
    // The last 8 bits are the length of the string in [1,3].
    u32,
);

impl TrimmedStr3 {
    /// Returns the length of the string.
    pub const fn len(self) -> usize {
        ((self.0 >> 24) & 0x3) as usize
    }

    /// Converts the string to bytes.
    pub const fn to_bytes(self) -> [u8; 3] {
        const { assert!(size_of::<[u8; 3]>() <= size_of::<u32>()) }
        // Using transmute is ugly, but LLVM refuses to optimize
        // a safe version like
        //
        //    let b = w.to_le_bytes();
        //    [b[0], b[1], b[2]]
        //
        // SAFETY: `[u8; 3]` is smaller than `[u8; 4]`.
        unsafe { mem::transmute_copy(&self.0.to_le_bytes()) }
    }
}

impl fmt::Display for TrimmedStr3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let b = &self.to_bytes();
        // SAFETY: Up to `self.len()` bytes are valid UTF-8.
        let s = unsafe { str::from_utf8_unchecked(b) };
        write!(f, "{s}")
    }
}

macro_rules! impl_is_valid {
    ($name:ident, $ty:ty) => {
        /// Reports whether the BCD is valid.
        ///
        /// For a BCD to be valid, each nibble may only have one
        /// of the following bit patterns:
        ///
        /// 0. `0000`
        /// 1. `0001`
        /// 2. `0010`
        /// 3. `0011`
        /// 4. `0100`
        /// 5. `0101`
        /// 6. `0110`
        /// 7. `0111`
        /// 8. `1000`
        /// 9. `1001`
        pub const fn $name(bcd: $ty) -> bool {
            /// Construct a bitmask where each nibble is the
            /// same.
            macro_rules! mask {
                ($nibble:literal) => {{
                    const { assert!($nibble <= 0xf) }

                    let mut v = 0;
                    let mut s = 0;
                    while s < <$ty>::BITS {
                        v |= ($nibble as $ty) << s;
                        s += 4;
                    }
                    v
                }};
            }
            const MASK1: $ty = mask!(0b0111); // 0x777...
            const MASK2: $ty = mask!(0b0011); // 0x333...
            const MASK3: $ty = mask!(0b1000); // 0x888...
            let half = (bcd >> 1) & MASK1;
            ((half + MASK2) & MASK3) == 0
        }
    };
}
impl_is_valid!(is_valid_u8, u8);
impl_is_valid!(is_valid_u16, u16);
impl_is_valid!(is_valid_u32, u32);
impl_is_valid!(is_valid_u64, u64);
impl_is_valid!(is_valid_u128, u128);

/// Returned when a BCD cannot be parsed from a string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseBcdError(());

impl fmt::Display for ParseBcdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unable to parse BCD")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseBcdError {}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_is_valid {
        (
            $(#[$meta:meta])*
            $name:ident, $int:ty, $is_valid:ident $(,)?
        ) => {
            $(#[$meta])*
            #[test]
            fn $name() {
                /// The obvious method to check whether the BCD
                /// is valid.
                fn is_valid_check(mut bcd: $int) -> bool {
                    while bcd > 0 {
                        let nibble = bcd & 0xf;
                        if nibble > 9 {
                            return false;
                        }
                        bcd >>= 4;
                    }
                    true
                }
                for i in 0..=<$int>::MAX {
                    let want = is_valid_check(i);
                    let got = $is_valid(i);
                    assert_eq!(got, want, "#{i}");
                }
            }
        };
    }
    test_is_valid!(test_u8_is_valid, u8, is_valid_u8);
    test_is_valid!(test_u16_is_valid, u16, is_valid_u16);
    test_is_valid!(
        #[cfg(not(debug_assertions))]
        test_u32_is_valid,
        u32,
        is_valid_u32,
    );

    macro_rules! test_to_from_bin {
        (
            $(#[$meta:meta])*
            $name:ident, $bcd:ty $(,)?
        ) => {
            $(#[$meta])*
            #[test]
            fn $name() {
                let mut prev = <$bcd>::zero();
                for want in 0..=<$bcd>::BIN_MAX {
                    let bcd = <$bcd>::from_bin(want);
                    let got = bcd.to_bin();
                    assert_eq!(got, want);
                    if want == 0 {
                        assert_eq!(prev.cmp(&bcd), Ordering::Equal,
                            "{prev} cmp {bcd}");
                        assert_eq!(bcd.cmp(&prev), Ordering::Equal,
                            "{bcd} cmp {prev}");
                    } else {
                        assert_eq!(prev.cmp(&bcd), Ordering::Less,
                            "{prev} cmp {bcd}");
                        assert_eq!(bcd.cmp(&prev), Ordering::Greater,
                            "{bcd} cmp {prev}");
                    }
                    prev = bcd;
                }
            }
        };
    }
    test_to_from_bin!(test_bcd5_to_from_bin, Bcd5);
    test_to_from_bin!(
        #[cfg(not(debug_assertions))]
        test_bcd10_to_from_bin,
        Bcd10,
    );

    macro_rules! test_encode {
        (
            $(#[$meta:meta])*
            $name:ident, $bcd:ty $(,)?
        ) => {
            $(#[$meta])*
            #[test]
            fn $name() {
                let mut want_buf = itoa::Buffer::new();
                let mut got_buf = [0u8; <$bcd>::DIGITS];
                for i in 0..=<$bcd>::BIN_MAX {
                    let want = want_buf.format(i);
                    let bcd = <$bcd>::from_bin(i);
                    let got = bcd.encode(&mut got_buf);
                    assert_eq!(got, want, "#{i}");

                    // Also check the `FromStr` impl.
                    assert_eq!(got.parse(), Ok(bcd), "#{i}: `FromStr` failed");
                }
            }
        };
    }
    test_encode!(test_bcd5_encode, Bcd5);
    test_encode!(
        #[cfg(not(debug_assertions))]
        test_bcd10_encode,
        Bcd10,
    );

    #[test]
    fn test_bcd10() {
        let want = u32::MAX;
        let got = Bcd10::from_bin(want);
        assert_eq!(got.to_string(), want.to_string());
    }

    macro_rules! test_pack_unpack {
        (
            $(#[$meta:meta])*
            $name:ident, $bcd:ty $(,)?
        ) => {
            $(#[$meta])*
            #[test]
            fn $name() {
                for bin in 0..=<$bcd>::BIN_MAX {
                    let bcd = <$bcd>::from_bin(bin);
                    let dpd = bcd.pack();
                    let got = <$bcd>::try_unpack(dpd);
                    assert_eq!(got, Some(bcd), "#{bin}");
                }
            }
        };
    }
    test_pack_unpack!(test_bcd5_pack_unpack, Bcd5);
    test_pack_unpack!(
        #[cfg(not(debug_assertions))]
        test_bcd10_pack_unpack,
        Bcd10,
    );

    #[test]
    fn test_to_str() {
        for bin in 0..=999 {
            let bcd = from_bin(bin);
            let got = to_str(bcd);
            let sd = if bin < 10 {
                1
            } else if bin < 100 {
                2
            } else {
                3
            };
            let want = [
                ((bin % 1000 / 100) as u8) + b'0',
                ((bin % 100 / 10) as u8) + b'0',
                ((bin % 10) as u8) + b'0',
            ];
            assert_eq!(
                got,
                Str3(want),
                "#{bin}: \"{}\" != \"{}\"",
                str::from_utf8(&got.to_bytes()[..sd as usize]).unwrap(),
                str::from_utf8(&want[..sd as usize]).unwrap(),
            );
        }
    }
}
