use core::{fmt, mem::MaybeUninit, str};

use super::bid::{Bid128, Bid32, Bid64};

mod private {
    use super::{Buffer, Fmt};
    use crate::bid::{Bid128, Bid32, Bid64};

    pub trait Sealed {
        fn write(self, buf: &mut Buffer, fmt: Fmt) -> &str;
    }

    impl Sealed for Bid128 {
        fn write(self, buf: &mut Buffer, fmt: Fmt) -> &str {
            match fmt {
                Fmt::UpperExp => {
                    todo!()
                }
                Fmt::LowerExp => {
                    todo!()
                }
                Fmt::Default => self.format(buf),
            }
        }
    }

    impl Sealed for Bid64 {
        fn write(self, buf: &mut Buffer, fmt: Fmt) -> &str {
            match fmt {
                Fmt::UpperExp => {
                    todo!()
                }
                Fmt::LowerExp => {
                    todo!()
                }
                Fmt::Default => self.format(buf),
            }
        }
    }

    impl Sealed for Bid32 {
        fn write(self, buf: &mut Buffer, fmt: Fmt) -> &str {
            match fmt {
                Fmt::UpperExp => {
                    todo!()
                }
                Fmt::LowerExp => {
                    todo!()
                }
                Fmt::Default => self.format(buf),
            }
        }
    }
}
use private::Sealed;

/// A floating point decimal number.
pub trait Number: Sealed {}

impl Number for Bid32 {}
impl Number for Bid64 {}
impl Number for Bid128 {}

/// A buffer for converting floating point decimals to text.
#[derive(Copy, Debug)]
pub struct Buffer {
    pub(crate) buf: [MaybeUninit<u8>; Self::MAX_STR_LEN],
}

impl Buffer {
    pub(crate) const MAX_STR_LEN: usize = 48;

    /// Creates a `Buffer`.
    pub const fn new() -> Self {
        Self {
            buf: [MaybeUninit::uninit(); Self::MAX_STR_LEN],
        }
    }

    #[allow(dead_code)] // false positive?
    pub(crate) const fn len() -> usize {
        Self::MAX_STR_LEN
    }

    /// Prints the decimal to the buffer.
    ///
    /// The decimal is printed in scientific notation.
    pub fn format<D: Number>(&mut self, d: D, fmt: Fmt) -> &str {
        d.write(self, fmt)
    }
}

impl Clone for Buffer {
    // The internals are hidden, so this is an easy perf win.
    #[allow(clippy::non_canonical_clone_impl)]
    fn clone(&self) -> Self {
        Self::new()
    }
}

impl Default for Buffer {
    fn default() -> Self {
        Self::new()
    }
}

/// Controls how decimals are printed to [`Buffer`].
#[derive(Copy, Clone, Debug, Default)]
pub enum Fmt {
    /// Use the default format.
    #[default]
    Default,
    /// Use scientific notation with an uppercase `e`.
    UpperExp,
    /// Use scientific notation with a lowercase `e`.
    LowerExp,
}

/// An error returned when parsing a decimal from a string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    kind: ErrorKind,
    #[cfg(test)]
    reason: &'static str,
}

impl ParseError {
    const fn new(kind: ErrorKind, _reason: &'static str) -> Self {
        Self {
            kind,
            #[cfg(test)]
            reason: _reason,
        }
    }

    pub(crate) const fn empty() -> Self {
        Self::new(ErrorKind::Empty, "")
    }

    pub(crate) const fn invalid(reason: &'static str) -> Self {
        Self::new(ErrorKind::Invalid, reason)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(test)]
        {
            write!(f, "{}: {}", self.kind, self.reason)
        }

        #[cfg(not(test))]
        self.kind.fmt(f)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum ErrorKind {
    Empty,
    Invalid,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "cannot parse decimal from empty string"),
            Self::Invalid => write!(f, "invalid decimal literal"),
        }
    }
}

/// Reports whether `a == b` using ASCII case folding.
pub(crate) const fn equal_fold_ascii(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let (Some(lhs), Some(rhs)) = (a.split_first_chunk(), b.split_first_chunk()) {
        if to_ascii_lower8(u64::from_le_bytes(*lhs.0))
            != to_ascii_lower8(u64::from_le_bytes(*rhs.0))
        {
            return false;
        }
        a = lhs.1;
        b = rhs.1;
    }
    while let (Some(lhs), Some(rhs)) = (a.split_first(), b.split_first()) {
        if to_ascii_lower(*lhs.0) != to_ascii_lower(*rhs.0) {
            return false;
        }
        a = lhs.1;
        b = rhs.1;
    }
    true
}

/// Converts eight characters to their lowercase ASCII
/// equivalent.
///
/// Characters that are not uppercase ASCII letters are left
/// unchanged.
const fn to_ascii_lower8(s: u64) -> u64 {
    // Taken from BIND 9
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/lib/isc/include/isc/ascii.h#L62
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/LICENSE
    const MASK: u64 = 0x0101010101010101;
    let heptets = s & (0x7F * MASK);
    let is_gt_z = heptets + ((0x7F - b'Z') as u64) * MASK;
    let is_ge_a = heptets + ((0x80 - b'A') as u64) * MASK;
    let is_ascii = !s & (0x80 * MASK);
    let is_upper = is_ascii & (is_ge_a ^ is_gt_z);
    s | is_upper >> 2
}

/// Converts four characters to their lowercase ASCII
/// equivalent.
///
/// Characters that are not uppercase ASCII letters are left
/// unchanged.
const fn to_ascii_lower4(s: u32) -> u32 {
    // Taken from BIND 9
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/lib/isc/include/isc/ascii.h#L62
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/LICENSE
    const MASK: u32 = 0x01010101;
    let heptets = s & (0x7F * MASK);
    let is_ascii = !s & (0x80 * MASK);
    let is_gt_z = heptets + ((0x7F - b'Z') as u32) * MASK;
    let is_ge_a = heptets + ((0x80 - b'A') as u32) * MASK;
    let is_upper = (is_ge_a ^ is_gt_z) & is_ascii;
    s | (is_upper >> 2)
}

/// Converts three characters to their lowercase ASCII
/// equivalent.
///
/// Characters that are not uppercase ASCII letters are left
/// unchanged.
const fn to_ascii_lower3(s: u32) -> u32 {
    // Taken from BIND 9
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/lib/isc/include/isc/ascii.h#L62
    // https://gitlab.isc.org/isc-projects/bind9/-/blob/8a09d54d6befaf3e35a59c48b926da893303a375/LICENSE
    const MASK: u32 = 0x01010101;
    let heptets = s & (0x7F * MASK);
    let is_ascii = !s & (0x80 * MASK);
    let is_gt_z = heptets + ((0x7F - b'Z') as u32) * MASK;
    let is_ge_a = heptets + ((0x80 - b'A') as u32) * MASK;
    let is_upper = (is_ge_a ^ is_gt_z) & is_ascii;
    s | (is_upper >> 2)
}

/// Converts `c` to its lowercase ASCII equivalent.
///
/// If `c` is not an uppercase ASCII letter then `c` remains
/// unchanged.
const fn to_ascii_lower(c: u8) -> u8 {
    // This is a const initializer, so panicking is okay.
    #[allow(clippy::indexing_slicing)]
    const TABLE: [u8; 256] = {
        let mut table = [0u8; 256];
        let mut i = 0;
        while i < table.len() {
            table[i] = (i as u8).to_ascii_lowercase();
            i += 1;
        }
        table
    };
    // `c` has 256 possible values and so does `TABLE`, so this
    // cannot panic.
    #[allow(clippy::indexing_slicing)]
    TABLE[c as usize]
}
