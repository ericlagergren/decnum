//! BCD conversion routines.

use core::fmt;

/// Returns the number of digits in an `n`-bit BCD.
pub const fn digits(bits: u32) -> usize {
    (bits / 4) as usize
}

macro_rules! conv_impl {
    ($name:ident, $ty:ty, $bcd2bin:ident, $bin2bcd:ident) => {
        /// A BCD.
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct $name([u8; Self::DIGITS]);

        impl $name {
            /// The number of digits in the BCD.
            pub const DIGITS: usize = digits(<$ty>::BITS);

            /// Converts a binary number to a BCD.
            pub fn from_bin(mut bin: $ty) -> Self {
                let mut bcd = [0u8; Self::DIGITS];
                let mut i = 0;
                while i < bcd.len() {
                    let lo = (bin % 10) as u8;
                    bin /= 10;
                    let hi = (bin % 10) as u8;
                    bin /= 10;
                    bcd[i] = (hi << 4) | lo;
                    println!("#{i}: {:#02x}", bcd[i]);
                    i += 1;
                }
                println!("{:#02x?}", &bcd[..]);
                Self(bcd)
            }

            /// Converts the BCD to a binary number.
            pub const fn to_bin(&self) -> $ty {
                let mut z = 0; // result
                let mut p = 1; // powers of 10
                let mut i = 0; // index
                while i < self.0.len() {
                    let lo = (self.0[i] & 0xf) as $ty;
                    let hi = (self.0[i] >> 4) as $ty;
                    z += (lo * p) + (hi * p * 10);
                    i += 1;
                    p *= 100;
                }
                z
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut skip = true;
                for d in self.0.iter().rev() {
                    let hi = d >> 4;
                    if hi != 0 || !skip {
                        write!(f, "{hi}")?;
                        skip = false;
                    }
                    let lo = d & 0xf;
                    if lo != 0 || !skip {
                        write!(f, "{lo}")?;
                        skip = false;
                    }
                }
                Ok(())
            }
        }

        /// Converts a binary number to a BCD.
        pub const fn $bin2bcd(mut bin: $ty) -> $ty {
            // Number of decimal digits that this integer can
            // support.
            const DIGITS: u32 = <$ty>::BITS / 4;
            debug_assert!({
                let mut nd = if bin == 0 { 1 } else { bin.ilog10() };
                if (10 as $ty).pow(nd) >= bin {
                    nd += 1;
                }
                nd <= DIGITS
            });

            let mut bcd = 0;
            let mut s = 0;
            loop {
                bcd |= (bin % 10) << s;
                s += 4;
                if s >= <$ty>::BITS as $ty {
                    break;
                }
                bin /= 10;
            }
            bcd
        }

        /// Converts a BCD to a binary number.
        pub const fn $bcd2bin(bcd: $ty) -> $ty {
            let mut z = 0; // result
            let mut p = 1; // powers of 10
            let mut s = 0; // shift
            loop {
                z += ((bcd >> s) & 0xf) * p;
                s += 4;
                if s >= <$ty>::BITS as $ty {
                    break;
                }
                p *= 10;
            }
            z
        }
    };
}
conv_impl!(Bcd2, u8, to_u8, from_u8);
conv_impl!(Bcd4, u16, to_u16, from_u16);
conv_impl!(Bcd8, u32, to_u32, from_u32);
conv_impl!(Bcd16, u64, to_u64, from_u64);
conv_impl!(Bcd32, u128, to_u128, from_u128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bcd16() {
        let want = u64::MAX;
        let got = Bcd16::from_bin(want);
        assert_eq!(got.to_string(), want.to_string());
    }

    #[test]
    fn test_u8_exhaustive() {
        for want in 0..=u8::MAX {
            let got = to_u8(from_u8(want));
            assert_eq!(got, want);
        }
    }

    #[test]
    fn test_u16_exhaustive() {
        for want in 0..=u16::MAX {
            let got = to_u16(from_u16(want));
            assert_eq!(got, want);
        }
    }

    // #[test]
    // fn test_u32_exhaustive() {
    //     for want in 0..=u32::MAX {
    //         let got = to_u32(from_u32(want));
    //         assert_eq!(got, want);
    //     }
    // }

    #[test]
    fn test_conv() {
        let want = 1234567890_12345;
        let got = to_u64(from_u64(want));
        assert_eq!(got, want);
    }

    #[test]
    fn test_conv2() {
        let want = 1234567890_123456;
        let got = Bcd16::from_bin(want).to_bin();
        assert_eq!(got, want);
    }
}
