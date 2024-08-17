//! BCD conversion routines.

use core::{
    cmp::Ordering,
    fmt,
    hash::Hash,
    hint,
    str::{self, FromStr},
};

use super::{conv, dpd, util::assume};

/// A BCD's bit pattern.
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    /// All digits are small.
    AllSmall = 0x000,
    /// The right digit is large.
    RightLarge = 0x008,
    /// The middle digit is large.
    MiddleLarge = 0x080,
    /// The left digit is large.
    LeftLarge = 0x800,
    /// The right digit is small.
    RightSmall = 0x880,
    /// The middle digit is small.
    MiddleSmall = 0x808,
    /// The left digit is small.
    LeftSmall = 0x088,
    /// All digits are large.
    AllLarge = 0x888,
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Pattern::*;
        match self {
            AllSmall => write!(f, "AllSmall"),
            RightLarge => write!(f, "RightLarge"),
            MiddleLarge => write!(f, "MiddleLarge"),
            LeftLarge => write!(f, "LeftLarge"),
            RightSmall => write!(f, "RightSmall"),
            MiddleSmall => write!(f, "MiddleSmall"),
            LeftSmall => write!(f, "LeftSmall"),
            AllLarge => write!(f, "AllLarge"),
        }
    }
}

/// Classifies a 12-bit BCD for packing into a 10-bit DPD.
pub const fn classify(bcd: u16) -> Pattern {
    use Pattern::*;
    match bcd & 0x888 {
        0x000 => AllSmall,
        0x008 => RightLarge,
        0x080 => MiddleLarge,
        0x800 => LeftLarge,
        0x880 => RightSmall,
        0x808 => MiddleSmall,
        0x088 => LeftSmall,
        0x888 => AllLarge,
        // SAFETY: Given the bits we've set, these are the only
        // possible results.
        _ => unsafe { hint::unreachable_unchecked() },
    }
}

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
                    // The loop condition is `i < buf.len()`, so
                    // this cannot panic.
                    #[allow(clippy::indexing_slicing)]
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
                    // the call to `dpd::pack`.
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
            pub const fn unpack(dpd: $dpd) -> Self {
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
            /// Returns `None` if the DPD is invalid.
            pub const fn try_unpack(dpd: $dpd) -> Option<Self> {
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
            pub fn encode(self, buf: &mut [u8; $digits]) -> &str {
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
            pub fn encode_full(self, buf: &mut [u8; $digits]) -> &str {
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

/// A 34 digit BCD.
#[derive(Copy, Clone, Debug)]
pub(super) struct Bcd34 {
    pub lo: u128, // 32 digits = 128 bits
    pub hi: u8,   // 2 digits = 8 bits
}

impl Bcd34 {
    const fn debug_check(self) {
        debug_assert!(is_valid_u128(self.lo));
        debug_assert!(is_valid_u8(self.hi));
    }

    /// The number of digits in `lo`.
    pub const LO_DIGITS: usize = 32;
    /// The number of digits in `hi`.
    pub const HI_DIGITS: usize = 2;

    /// Returns the zero BCD.
    pub const fn zero() -> Self {
        Self { lo: 0, hi: 0 }
    }

    /// Creates a BCD from a DPD.
    pub const fn unpack(mut dpd: u128) -> Self {
        dpd &= (1 << 114) - 1;

        let mut lo = 0;
        let mut hi = 0;

        hi |= (((dpd >> 110) & 0xf) as u8) << 4;
        let bcd = dpd::unpack(((dpd >> 100) & 0x3ff) as u16);
        hi |= ((bcd & 0xf00) >> 8) as u8;
        lo |= ((bcd & 0x0ff) as u128) << 120;

        let mut i = 0;
        while i < 10 {
            let declet = (dpd >> (100 - (i + 1) * 10)) & 0x3ff;
            let bcd = dpd::unpack(declet as u16);
            lo |= (bcd as u128) << (120 - (i + 1) * 12);
            i += 1;
        }

        debug_assert!(is_valid_u128(lo));
        debug_assert!(is_valid_u8(hi));

        Self { lo, hi }
    }

    /// Packs the BCD into a DPD.
    pub const fn pack(self) -> u128 {
        self.debug_check();

        let mut dpd = 0;
        let mut i = 0;
        while i < 10 {
            let bcd = (self.lo >> (i * 12)) & 0xfff;
            // This check removes the bounds checks from
            // the call to `dpd::pack`.
            //
            // SAFETY: `self.lo` never has any invalid digits, so
            // its maximum value is 0x999.
            unsafe { assume(bcd <= 0x999) }
            dpd |= (dpd::pack(bcd as u16) as u128) << (i * 10);
            i += 1;
        }

        let bcd = (((self.hi & 0x00f) as u16) << 8) | ((self.lo >> 120) as u16);
        // This check removes the bounds checks from the call to
        // `dpd::pack`.
        //
        // SAFETY: `self.hi` and `self.lo` never have any invalid
        // digits, so its maximum value is 0x999.
        unsafe { assume(bcd <= 0x999) }
        dpd |= (dpd::pack(bcd) as u128) << 100;
        dpd |= ((self.hi >> 4) as u128) << 110;

        dpd
    }

    /// Parses a BCD from a string.
    #[no_mangle]
    pub fn parse(s: &str) -> Result<Self, ParseBcdError> {
        let mut s = s.as_bytes();
        if s.is_empty() {
            return Err(ParseBcdError(()));
        }

        // Skip leading zeros.
        while let Some((&b'0', rest)) = s.split_first() {
            s = rest;
        }
        if s.len() > 34 {
            return Err(ParseBcdError(()));
        }
        // `s.len()` is in [0, 34]

        let mut bcd = Self::zero();

        let (mut hi, mut lo): (&[u8], &[u8]) = {
            if s.len() > 32 {
                s.split_at(s.len() - 32)
            } else {
                (&[], s)
            }
        };
        debug_assert!(hi.len() <= Self::HI_DIGITS);
        debug_assert!(lo.len() <= Self::LO_DIGITS);

        // Max 2 iters = 2 digits
        while let Some((&c, rest)) = hi.split_first() {
            let d = c.wrapping_sub(b'0');
            if d >= 10 {
                return Err(ParseBcdError(()));
            }
            bcd.hi <<= 4;
            bcd.hi |= d;
            hi = rest;
        }

        // Max floor(34/4) = 8 iters = 32 digits
        while let Some((chunk, rest)) = lo.split_first_chunk() {
            let Ok(s) = Str4::try_from_bytes(*chunk) else {
                // Not four ASCII digits.
                return Err(ParseBcdError(()));
            };
            bcd.lo <<= 16;
            bcd.lo |= s.to_bcd() as u128;
            lo = rest;
        }

        // Max 3 iters = 3 digits
        while let Some((&c, rest)) = lo.split_first() {
            let d = c.wrapping_sub(b'0');
            if d >= 10 {
                return Err(ParseBcdError(()));
            }
            bcd.lo <<= 4;
            bcd.lo |= d as u128;
            lo = rest;
        }

        bcd.debug_check();

        Ok(bcd)
    }

    /// Shifts the BCD to the left by `shift` digits.
    ///
    /// In other words, it multiplies the BCD by `10^shift`.
    ///
    /// `shift` must be in [0, 34].
    pub const fn shift(self, shift: u16) -> Self {
        debug_assert!(shift <= 34);
        self.debug_check();

        let shift = shift * 4; // bits
        if shift > 128 {
            Self {
                hi: self.hi << (shift - 128),
                lo: 0,
            }
        } else {
            // TODO(eric): 128-shift can overflow for shift=128
            Self {
                hi: (self.hi << shift) | ((self.lo >> (128 - shift)) as u8),
                lo: self.lo << shift,
            }
        }
    }

    /// Compares `self` and `other`.
    pub const fn const_cmp(self, other: Self) -> Ordering {
        self.debug_check();

        match self.hi.checked_sub(other.hi) {
            Some(0) => {}
            Some(_) => return Ordering::Greater,
            None => return Ordering::Less,
        }
        match self.lo.checked_sub(other.lo) {
            Some(0) => Ordering::Equal,
            Some(_) => Ordering::Greater,
            None => Ordering::Less,
        }
    }
}

impl Eq for Bcd34 {}
impl PartialEq for Bcd34 {
    fn eq(&self, other: &Self) -> bool {
        self.lo == other.lo && self.hi == other.hi
    }
}
impl Ord for Bcd34 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.const_cmp(*other)
    }
}
impl PartialOrd for Bcd34 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl fmt::Display for Bcd34 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { lo, hi } = *self;
        if hi > 0 {
            write!(f, "{:x}", hi)?;
        }
        write!(f, "{:x}", lo)?;
        Ok(())
    }
}

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

/// A 12-bit BCD converted to a three-byte ASCII string.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Str3(u32);

impl Str3 {
    pub(super) const fn zero() -> Self {
        Self(0)
    }

    /// Reads a string from three ASCII bytes in little-endian
    /// order.
    ///
    /// The fourth byte is discarded.
    pub const fn try_from_u32(v: u32) -> Option<Self> {
        if !conv::is_3digits(v) {
            None
        } else {
            Some(Self(v))
        }
    }

    /// Reads a string from three ASCII bytes.
    ///
    /// The fourth byte is discarded.
    pub const fn try_from_bytes(b: [u8; 4]) -> Option<Self> {
        Self::try_from_u32(u32::from_le_bytes(b))
    }

    /// Converts a 12-bit BCD to a string.
    pub const fn from_bcd(bcd: u16) -> Self {
        // Rewrite 0x0123 as 0x00030201.
        let mut w = 0;
        w |= ((bcd & 0x000f) as u32) << 16;
        w |= ((bcd & 0x00f0) as u32) << 4;
        w |= ((bcd & 0x0f00) as u32) >> 8;
        w |= 0x00303030; // b'0' | b'0'<<8 | ...
        Self(w)
    }

    /// Converts the string to bytes.
    ///
    /// The first three digits are valid ASCII.
    pub const fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    /// Converts the string into a 12-bit BCD.
    pub const fn to_bcd(self) -> u16 {
        let mut w = 0;
        w |= ((self.0 & 0x00000f) << 8) as u16;
        w |= ((self.0 & 0x000f00) >> 4) as u16;
        w |= ((self.0 & 0x0f0000) >> 16) as u16;
        w & 0x0fff
    }

    const fn zero_digits(self) -> u32 {
        let mut w = self.0;
        w &= 0xffcfcfcf; // to unpacked BCD
        w |= 0xff000000; // only check the BCD
        w.trailing_zeros() / 8
    }

    /// Like [`to_bytes`][Self::to_bytes], but shifts the digits
    /// to remove insignificant zeros.
    ///
    /// The first [`digits`][Self::digits] digits are valid
    /// ASCII.
    pub const fn to_trimmed_bytes(self) -> [u8; 4] {
        let zeros = self.zero_digits() * 8;
        (self.0 >> zeros).to_le_bytes()
    }

    /// Returns the number of significant digits in the BCD.
    ///
    /// It returns 0 for "000".
    ///
    /// The result is always in [0,3].
    pub const fn digits(self) -> usize {
        (3 - self.zero_digits()) as usize
    }
}

impl fmt::Display for Str3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let b = &self.to_bytes();
        // SAFETY: Up to three bytes are valid ASCII.
        let s = unsafe { str::from_utf8_unchecked(&b[..3]) };
        write!(f, "{s}")
    }
}

/// A string containing four ASCII digits.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Str4(u32);

impl Str4 {
    /// Reads a string from four ASCII digits in little-endian
    /// order.
    pub const fn try_from_u32(v: u32) -> Result<Self, InvalidDigit> {
        let mask = conv::check_4digits(v);
        if mask == 0 {
            Ok(Self(v))
        } else {
            Err(InvalidDigit(mask))
        }
    }

    /// Reads a string from four ASCII digits.
    pub const fn try_from_bytes(b: [u8; 4]) -> Result<Self, InvalidDigit> {
        Self::try_from_u32(u32::from_le_bytes(b))
    }

    /// Creates a string from a 16-bit BCD.
    pub const fn from_bcd(bcd: u16) -> Self {
        debug_assert!(is_valid_u16(bcd));

        // Rewrite 0x00001234
        //      as 0x04030201
        let mut w = 0;
        w |= ((bcd & 0x000f) as u32) << 24;
        w |= ((bcd & 0x00f0) as u32) << 12;
        w |= (bcd & 0x0f00) as u32;
        w |= ((bcd & 0xf000) as u32) >> 12;
        w |= 0x30303030; // b'0' | b'0'<<8 | ...
        Self(w)
    }

    /// Converts the string to four ASCII digits.
    pub const fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    /// Converts the string to a 16-bit BCD.
    pub const fn to_bcd(self) -> u16 {
        // Rewrite 0x04030201
        //      as 0x00001234
        let mut w = 0;
        w |= ((self.0 & 0x0f000000) >> 24) as u16;
        w |= ((self.0 & 0x000f0000) >> 12) as u16;
        w |= (self.0 & 0x00000f00) as u16;
        w |= ((self.0 & 0x0000000f) << 12) as u16;
        debug_assert!(is_valid_u16(w));
        w
    }

    const fn zero_digits(self) -> u32 {
        let mut w = self.0;
        w &= 0xcfcfcfcf; // to unpacked BCD
        w.trailing_zeros() / 8
    }

    /// Like [`to_bytes`][Self::to_bytes], but shifts the digits
    /// to remove insignificant zeros.
    ///
    /// The first [`digits`][Self::digits] digits are valid
    /// ASCII.
    pub const fn to_trimmed_bytes(self) -> [u8; 4] {
        let zeros = self.zero_digits() * 8;
        (self.0 >> zeros).to_le_bytes()
    }

    /// Returns the number of significant digits in the BCD.
    ///
    /// It returns 0 for "0000".
    ///
    /// The result is always in [0, 4].
    pub const fn digits(self) -> usize {
        (4 - self.zero_digits()) as usize
    }
}

impl fmt::Display for Str4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let b = &self.to_bytes();
        let s = unsafe { str::from_utf8_unchecked(b) };
        write!(f, "{s}")
    }
}

/// An invalid digit.
#[derive(Copy, Clone, Debug)]
pub struct InvalidDigit(u32);

impl InvalidDigit {
    /// Returns the invalid digit.
    pub const fn digit(self) -> u8 {
        // a b c d
        // 4 8 8 8 = 28
        //   4 8 8 = 20
        //     4 8 = 12
        //       4 = 4
        let ntz = self.0.trailing_zeros() - 4;
        (self.0 >> (ntz - 4)) as u8
    }

    /// Returns the index of the invalid digit.
    pub const fn idx(self) -> usize {
        // a b c d
        // 4 8 8 8 = 28
        //   4 8 8 = 20
        //     4 8 = 12
        //       4 = 4
        let ntz = self.0.trailing_zeros() - 4;
        (ntz / 8) as usize
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

    /// Test [`Str3`].
    #[test]
    fn test_str3() {
        for bin in 0..=999 {
            let bcd = from_bin(bin);
            let got = Str3::from_bcd(bcd);
            let sd = if bin == 0 {
                0
            } else if bin < 10 {
                1
            } else if bin < 100 {
                2
            } else {
                3
            };
            let want = u32::from_le_bytes([
                ((bin % 1000 / 100) as u8) + b'0',
                ((bin % 100 / 10) as u8) + b'0',
                ((bin % 10) as u8) + b'0',
                0,
            ]);
            assert_eq!(got, Str3(want), "#{bin}");
            assert_eq!(got.to_bcd(), bcd, "#{bin}");
            assert_eq!(got.digits(), sd, "#{bin}");
        }
    }

    /// Test [`Str4`].
    #[test]
    fn test_str4() {
        const fn from_bin(mut bin: u16) -> u16 {
            let mut bcd = 0;
            let mut s = 0;
            while s < 16 {
                bcd |= (bin % 10) << s;
                s += 4;
                bin /= 10;
            }
            bcd
        }

        for bin in 0..=9999 {
            let bcd = from_bin(bin);
            let got = Str4::from_bcd(bcd);
            let sd = if bin == 0 {
                0
            } else if bin < 10 {
                1
            } else if bin < 100 {
                2
            } else if bin < 1000 {
                3
            } else {
                4
            };
            let want = u32::from_le_bytes([
                ((bin % 10000 / 1000) as u8) + b'0',
                ((bin % 1000 / 100) as u8) + b'0',
                ((bin % 100 / 10) as u8) + b'0',
                ((bin % 10) as u8) + b'0',
            ]);
            assert_eq!(got, Str4(want), "#{bin}");
            assert_eq!(got.to_bcd(), bcd, "#{bin}");
            assert_eq!(got.digits(), sd, "#{bin}");
        }
    }

    #[test]
    fn test_bcd34() {
        static TESTS: &[(u128, u128, Ordering)] = &[
            (0, 0, Ordering::Equal),
            (1, 0, Ordering::Greater),
            (1, 1, Ordering::Equal),
            (1, 2, Ordering::Less),
            (21, 30, Ordering::Less),
            (30, 21, Ordering::Greater),
            (123, 123, Ordering::Equal),
            (123, 122, Ordering::Greater),
            (12345, 12345, Ordering::Equal),
            (10u128.pow(30) - 1, 10u128.pow(30) - 1, Ordering::Equal),
            (10u128.pow(31) - 1, 10u128.pow(31) - 1, Ordering::Equal),
            (10u128.pow(32) - 1, 10u128.pow(32) - 1, Ordering::Equal),
            (10u128.pow(33) - 1, 10u128.pow(33) - 1, Ordering::Equal),
            (10u128.pow(34) - 1, 10u128.pow(34) - 1, Ordering::Equal),
            (10u128.pow(34) - 2, 10u128.pow(34) - 1, Ordering::Less),
            (10u128.pow(34) - 1, 10u128.pow(33) - 1, Ordering::Greater),
            (
                9111222333444555666777888999000111,
                9111222333444555666777888999000111,
                Ordering::Equal,
            ),
            (
                8111222333444555666777888999000111,
                9111222333444555666777888999000111,
                Ordering::Less,
            ),
        ];
        for (i, &(lhs_bin, rhs_bin, want)) in TESTS.iter().enumerate() {
            let lhs_dpd = dpd::pack_bin_u113(lhs_bin);
            let lhs = Bcd34::unpack(lhs_dpd);
            let rhs_dpd = dpd::pack_bin_u113(rhs_bin);
            let rhs = Bcd34::unpack(rhs_dpd);

            let got = lhs.const_cmp(rhs);
            assert_eq!(got, want, "#{i}: cmp({lhs}, {rhs})");

            let got = rhs.const_cmp(lhs);
            assert_eq!(got, want.reverse(), "#{i}: cmp({rhs}, {lhs})");

            assert_eq!(lhs.pack(), lhs_dpd, "#{i}");
            assert_eq!(rhs.pack(), rhs_dpd, "#{i}");

            assert_eq!(Bcd34::parse(&lhs.to_string()).unwrap(), lhs, "#{i}");
            assert_eq!(Bcd34::parse(&rhs.to_string()).unwrap(), rhs, "#{i}");
        }
    }
}
