use core::{fmt, mem::MaybeUninit};

use super::dec128::d128;

mod private {
    use super::{Buffer, Fmt};
    use crate::dec128::d128;

    pub trait Sealed {
        fn write(self, buf: &mut Buffer, fmt: Fmt) -> &str;
    }

    impl Sealed for d128 {
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
pub trait Decimal: Sealed {}

impl Decimal for d128 {}

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
    pub fn format<D: Decimal>(&mut self, d: D, fmt: Fmt) -> &str {
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
}

impl ParseError {
    pub(super) const fn empty() -> Self {
        Self {
            kind: ErrorKind::Empty,
        }
    }

    pub(super) const fn invalid(_reason: &'static str) -> Self {
        Self {
            kind: ErrorKind::Invalid,
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
