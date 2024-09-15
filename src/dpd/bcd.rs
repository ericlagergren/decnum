//! BCD conversion routines.

use core::{fmt, hint};

/// A BCD's bit pattern.
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(super) enum Pattern {
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
pub(super) const fn classify(bcd: u16) -> Pattern {
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

/// Converts the 16-bit BCD to a binary number.
pub(super) const fn to_bin(bcd: u16) -> u16 {
    let bcd = {
        // abcd -> cdab
        let rev = bcd.swap_bytes();
        // cdab -> dcba
        ((rev & 0x0f0f) << 4) | ((rev & 0xf0f0) >> 4)
    };
    let mut bin = 0;
    let mut s = 0;
    while s < 16 {
        bin *= 10;
        bin += (bcd >> s) & 0xf;
        s += 4;
    }
    bin
}

/// Creates a 16-bit BCD from a binary number.
pub(super) const fn from_bin(bin: u16) -> u16 {
    debug_assert!(bin <= 9999);

    // h/t: https://stackoverflow.com/a/78270881/2967113
    const MASK: u64 = 0x0FFFFE1FFFF87FFF;
    let mut x = (bin as u64) * 0x000418A051EC0CCD;
    let mut y = (x & MASK) * 10;
    x &= !MASK;
    y &= !MASK;
    let mut bcd = 0;
    bcd += y >> 15;
    bcd += y >> 33;
    bcd += y >> 52;
    bcd += x >> 48;
    bcd as u16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_from_bin() {
        for bin in 0..=9999 {
            let bcd = from_bin(bin);
            let got = to_bin(bcd);
            assert_eq!(got, bin, "{bcd:04x}");
        }
    }
}
