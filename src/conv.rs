use core::{fmt, mem::MaybeUninit};

use super::{
    bid::{Bid128, Bid64},
    dpd::Dpd128,
};

mod private {
    use super::{Buffer, Fmt};
    use crate::{
        bid::{Bid128, Bid64},
        dpd::Dpd128,
    };

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

    impl Sealed for Dpd128 {
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

impl Number for Bid128 {}
impl Number for Bid64 {}
impl Number for Dpd128 {}

/// A buffer for converting floating point decimals to text.
#[derive(Copy, Clone, Debug)]
pub struct Buffer {
    pub(super) buf: [MaybeUninit<u8>; Self::MAX_STR_LEN],
}

impl Buffer {
    const MAX_STR_LEN: usize = "-9.999999999999999999999999999999999E+6144".len();

    /// Creates a `Buffer`.
    pub const fn new() -> Self {
        Self {
            buf: [MaybeUninit::uninit(); Self::MAX_STR_LEN],
        }
    }

    #[allow(dead_code)] // false positive?
    pub(super) const fn len() -> usize {
        Self::MAX_STR_LEN
    }

    /// Prints the decimal to the buffer.
    ///
    /// The decimal is printed in scientific notation.
    pub fn format<D: Number>(&mut self, d: D, fmt: Fmt) -> &str {
        d.write(self, fmt)
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

    pub(super) const fn empty() -> Self {
        Self::new(ErrorKind::Empty, "")
    }

    pub(super) const fn invalid(reason: &'static str) -> Self {
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

/// Is `v` three digits?
pub(super) const fn is_3digits(v: u32) -> bool {
    let a = v.wrapping_add(0x0046_4646);
    let b = v.wrapping_sub(0x0030_3030);
    (a | b) & 0x0080_8080 == 0
}

// /// Is `v` four digits?
// pub(super) const fn is_4digits(v: u32) -> bool {
//     check_4digits(v) == 0
// }

/// Returns a mask over the digits in `v`.
///
/// Each byte is 0x00 if it is a digit, or 0x80 otherwise.
pub(super) const fn check_4digits(v: u32) -> u32 {
    let a = v.wrapping_add(0x4646_4646);
    let b = v.wrapping_sub(0x3030_3030);
    (a | b) & 0x8080_8080
}

/// Reports whether `a == b` using ASCII case folding.
pub(super) const fn equal_fold(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if !a[i].eq_ignore_ascii_case(&b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_3digits() {
        for d in 0..=u32::MAX {
            let b = d.to_le_bytes();
            let want = b[..3].iter().all(|b| matches!(b, b'0'..=b'9'));
            let got = is_3digits(d);
            assert_eq!(got, want, "{:?}", &b[..3]);
        }
    }
}
