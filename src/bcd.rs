//! BCD conversion routines.

use core::{
    cmp::Ordering,
    fmt,
    hash::Hash,
    str::{self, FromStr},
};

use super::dpd;

macro_rules! bcd_int_impl {
    (
        $name:ident,
        $digits:literal,
        $ty:ty,
        $bin:ty $(,)?
    ) => {
        const _: () = {
            assert!(<$name>::BITS < <$ty>::BITS as $ty);
            assert!(<$name>::BITS % 4 == 0);
        };

        #[doc = concat!("A BCD with ", stringify!($digits), " digits.")]
        #[derive(Copy, Clone, Default, Hash, Eq, PartialEq)]
        pub struct $name {
            // The least significant digit is the first nibble.
            bcd: $ty,
        }

        impl $name {
            /// The maximum number of digits in the BCD.
            pub const DIGITS: usize = $digits;

            /// The number of bits in `bcd` to use.
            const BITS: $ty = $digits * 4;
            const MASK: $ty = ((1 as $ty) << Self::BITS) - 1;

            /// The max value for `$bin`.
            #[cfg(test)]
            #[allow(dead_code)]
            const BIN_MAX: $bin = <$bin>::MAX;

            /// Returns the all-zero BCD.
            pub const fn zero() -> Self {
                Self { bcd: 0 }
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
                let mut bin = bin as $ty;
                let mut bcd = 0;
                let mut s = 0;
                while s < Self::BITS {
                    bcd |= (bin % 10) << s;
                    s += 4;
                    bin /= 10;
                }
                Self { bcd }
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
                    let d = (c - b'0') as $ty;
                    bcd |= d << s;
                    i += 1;
                    s -= 4;
                }
                Ok(Self { bcd })
            }

            /// Converts the BCD to a binary number.
            pub const fn to_bin(self) -> $bin {
                let mut bin = 0;
                let mut s = 0; // shift
                while s < Self::BITS {
                    bin += ((self.bcd >> s) & 0xf) as $bin;
                    bin *= 10;
                    s += 4;
                }
                bin
            }

            /// Packs the BCD into a DPD.
            pub const fn pack(self) -> $bin {
                let mut dpd = 0;
                let mut shl = 0;
                let mut shr = 0;
                let mut i = 0;
                while i < Self::DIGITS {
                    let bcd = (self.bcd >> shr) & 0xfff;
                    dpd |= (dpd::pack(bcd as u16) as $bin) << shl;
                    shl += 10;
                    shr += 12;
                    i += 1;
                }
                dpd
            }

            /// TODO
            pub const fn pack2(self) -> $bin {
                let mut dpd = 0;
                let mut shl = 0;
                let mut shr = 0;
                let mut i = 0;
                while i < Self::DIGITS {
                    let bcd = (self.bcd >> shr) & 0xfff;
                    dpd |= (super::tables::BCD2DPD[bcd as usize] as $bin) << shl;
                    shl += 10;
                    shr += 12;
                    i += 1;
                }
                dpd
            }

            /// TODO
            pub const fn pack3(self) -> $bin {
                let mut dpd = 0;
                let mut shl = 0;
                let mut shr = 0;
                let mut i = 0;
                while i < Self::DIGITS {
                    let bcd = (self.bcd >> shr) & 0xfff;
                    dpd |= (bcd2dpd(bcd as u16) as $bin) << shl;
                    shl += 10;
                    shr += 12;
                    i += 1;
                }
                dpd
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
bcd_int_impl!(Bcd5, 5, u32, u16);
bcd_int_impl!(Bcd10, 10, u64, u32);

macro_rules! bit {
    ($x:ident, $idx:literal) => {{
        (($x >> $idx) & 1) == 1
    }};
}
const fn bcd2dpd(arg: u16) -> u16 {
    let a = bit!(arg, 11);
    let b = bit!(arg, 10);
    let c = bit!(arg, 9);
    let d = bit!(arg, 8);
    let e = bit!(arg, 7);
    let f = bit!(arg, 6);
    let g = bit!(arg, 5);
    let h = bit!(arg, 4);
    let i = bit!(arg, 3);
    let j = bit!(arg, 2);
    let k = bit!(arg, 1);
    let m = bit!(arg, 0);

    let p = b | (a & j) | (a & f & i);
    let q = c | (a & k) | (a & g & i);
    let r = d;
    let s = (f & (!a | !i)) | (!a & e & j) | (e & i);
    let t = g | (!a & e & k) | (a & i);
    let u = h;
    let v = a | e | i;
    let w = a | (e & i) | (!e & j);
    let x = e | (a & i) | (!a & k);
    let y = m;

    (y as u16)
        | ((x as u16) << 1)
        | ((w as u16) << 2)
        | ((v as u16) << 3)
        | ((u as u16) << 4)
        | ((t as u16) << 5)
        | ((s as u16) << 6)
        | ((r as u16) << 7)
        | ((q as u16) << 8)
        | ((p as u16) << 9)
}

/// Converts the three-digit BCD to a binary number.
pub const fn to_bin(bcd: u16) -> u16 {
    let mut z = 0; // result
    let mut s = 0; // shift
    while s < 12 {
        z += (bcd >> s) & 0xf;
        z *= 10;
        s += 4;
    }
    z
}

/// Creates a three-digit BCD from a binary number.
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

/*
/// `$digits` is the number of decimal digits in `<$ty>::MAX`.
macro_rules! bcd_bytes_impl {
    (
        $name:ident,
        $digits:literal,
        $ty:ty,
        $to_bin:ident,
        $from_bin:ident $(,)?
    ) => {
        #[doc = concat!("A BCD with ", stringify!($digits), " digits.")]
        #[derive(Copy, Clone, Hash, Eq, PartialEq)]
        pub struct $name {
            /// The most significant digits are in `bcd[0]` and
            /// the least significant digits are in
            /// `bcd[bcd.len()-1]`.
            ///
            /// For example, given the number 12345, the lower
            /// half of `bcd[0]` contains `5` and the upper half
            /// contains `4`. The lower half of `bcd[1]` contains
            /// `3` and the upper half contains `2`. The lower
            /// half of `bcd[2]` contains `1` and all remaining
            /// bits in `bcd` are 0.
            bcd: [u8; Self::SIZE],
        }

        impl $name {
            /// The maximum number of digits in the BCD.
            pub const DIGITS: usize = $digits;

            /// The size of the internal array.
            ///
            /// Each digit only requires a nibble.
            const SIZE: usize = ($digits + 1) / 2;

            /// Returns the all-zero BCD.
            pub const fn zero() -> Self {
                Self {
                    bcd: [0u8; Self::SIZE],
                }
            }

            /// Creates a BCD from a binary number.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd5;
            ///
            /// let x = Bcd5::from_bin(1234).to_bin();
            /// assert_eq!(x, 1234);
            /// ```
            pub const fn from_bin(mut bin: $ty) -> Self {
                let mut bcd = [0u8; Self::SIZE];
                let mut i = 0;
                while i < bcd.len() {
                    let lo = (bin % 10) as u8;
                    bin /= 10;
                    let hi = (bin % 10) as u8;
                    bin /= 10;
                    bcd[i] = (hi << 4) | lo;
                    i += 1;
                }
                Self { bcd }
            }

            /// Parses a BCD from a string.
            ///
            /// The string is allowed to contain insignificant
            /// leading zeros.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd5;
            ///
            /// let x = Bcd5::from_str("1234").unwrap();
            /// let y = Bcd5::from_str("01234").unwrap();
            /// assert_eq!(x, y);
            ///
            /// let x: Bcd5 = "1234".parse().unwrap();
            /// let y: Bcd5 = "01234".parse().unwrap();
            /// assert_eq!(x, y);
            /// ```
            pub const fn from_str(s: &str) -> Result<Self, ParseBcdError> {
                let s = s.as_bytes();
                if s.len() > Self::DIGITS {
                    return Err(ParseBcdError(()));
                }
                if s.is_empty() {
                    return Ok(Self {
                        bcd: [0u8; Self::SIZE],
                    });
                }

                let mut bcd = [0u8; Self::SIZE];

                let mut i = 0;
                let mut j = s.len() - 1;
                while i < s.len() {
                    let c = s[i];
                    if c < b'0' || c > b'9' {
                        return Err(ParseBcdError(()));
                    }
                    let d = c - b'0';
                    if j % 2 == 0 {
                        bcd[j / 2] |= d; // lo
                    } else {
                        bcd[j / 2] |= d << 4; // hi
                    }
                    j = j.saturating_sub(1);
                    i += 1;
                }
                Ok(Self { bcd })
            }

            /// Converts the BCD to a binary number.
            pub const fn to_bin(&self) -> $ty {
                let mut bin = 0; // result
                let mut p = 1; // powers of 10
                let mut i = 0; // index
                while i < self.bcd.len() {
                    let lo = (self.bcd[i] & 0xf) as $ty;
                    let hi = (self.bcd[i] >> 4) as $ty;
                    bin += (lo * p) + (hi * p * 10);
                    i += 1;
                    p = p.wrapping_mul(100);
                }
                bin
            }

            /// Reports whether the BCD is zero.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd5;
            ///
            /// assert!(Bcd5::from_bin(0).is_zero());
            /// assert!(!Bcd5::from_bin(1).is_zero());
            /// ```
            pub const fn is_zero(&self) -> bool {
                // If the LSD is zero, then the BCD is zero.
                self.bcd[0] == 0
            }

            /// Encodes the BCD to a string.
            ///
            /// The returned string does not contain
            /// insignificant leading zeros.
            ///
            /// # Example
            ///
            /// ```
            /// use decnum::bcd::Bcd5;
            ///
            /// let bcd = Bcd5::from_bin(1234);
            /// let mut buf = [0u8; Bcd5::DIGITS];
            /// let s = bcd.encode(&mut buf);
            /// assert_eq!(s, "1234");
            /// ```
            pub fn encode<'a>(&self, buf: &'a mut [u8; $digits]) -> &'a str {
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
            /// use decnum::bcd::Bcd5;
            ///
            /// let bcd = Bcd5::from_bin(1234);
            /// let mut buf = [0u8; Bcd5::DIGITS];
            /// let s = bcd.encode_full(&mut buf);
            /// assert_eq!(s, "01234");
            /// ```
            pub fn encode_full<'a>(&self, buf: &'a mut [u8; $digits]) -> &'a str {
                for (d, v) in self
                    .bcd
                    .iter()
                    .flat_map(|d| {
                        let lo = (d & 0xf) as u8;
                        let hi = (d >> 4) as u8;
                        [lo, hi]
                    })
                    .zip(buf.iter_mut().rev())
                {
                    *v = d + b'0';
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
                let mut buf = [[0, 0]; Self::SIZE];
                for (d, v) in self
                    .bcd
                    .iter()
                    .map(|d| {
                        let lo = (d & 0xf) as u8;
                        let hi = (d >> 4) as u8;
                        [lo, hi]
                    })
                    .zip(buf.iter_mut())
                {
                    *v = d;
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
bcd_bytes_impl!(Bcd20, 20, u64, to_u64, from_u64);
bcd_bytes_impl!(Bcd39, 39, u128, to_u128, from_u128);
*/

macro_rules! is_valid {
    ($name:ident, $ty:ty) => {
        /// Reports whether the BCD is valid.
        ///
        /// For a BCD to be valid, each nibble must have one of
        /// the following bit patterns:
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
is_valid!(is_valid_u8, u8);
is_valid!(is_valid_u16, u16);
is_valid!(is_valid_u32, u32);
is_valid!(is_valid_u64, u64);
is_valid!(is_valid_u128, u128);

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

    macro_rules! test_exhaustive {
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
    test_exhaustive!(test_bcd5_exhaustive, Bcd5);
    test_exhaustive!(
        #[cfg(not(debug_assertions))]
        test_bcd10_exhaustive,
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
}
