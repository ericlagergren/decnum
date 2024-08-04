use core::{fmt, mem::MaybeUninit};

use super::dec128::d128;

const MAX_STR_LEN: usize = "-9.999999999999999999999999999999999E+6144".len();

mod private {
    use core::mem::MaybeUninit;

    use super::MAX_STR_LEN;

    pub trait Sealed {
        fn format(self, buf: &[MaybeUninit<u8>; MAX_STR_LEN]);
    }
}

pub trait Decimal: Sealed {}

/// TODO
pub struct Buffer {
    buf: [MaybeUninit<u8>; MAX_STR_LEN],
}

impl Buffer {
    /// Creates a `Buffer`.
    pub const fn new() -> Self {
        Self {
            buf: [MaybeUninit::<u8>::uninit(); MAX_STR_LEN],
        }
    }

    /// TODO
    pub fn format<D: Decimal>(&mut self, d: D) -> &str {
        d.format(&mut self.buf)
    }
}

/// TODO
#[derive(Copy, Clone, Default, Eq, PartialEq)]
pub enum Fmt {
    /// TODO
    #[default]
    Default,
    /// TODO
    UpperExp,
    /// TODO
    LowerExp,
}

/// A decimal converted to scientific notation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SciStr {
    buf: [u8; d128::MAX_STR_LEN],
}

impl SciStr {
    /// TODO
    pub const fn as_str(&self) -> &str {
        todo!()
    }
}

impl fmt::Display for SciStr {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

/// A decimal converted to engineering notation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct EngStr {}

impl EngStr {
    /// TODO
    pub const fn as_str(&self) -> &str {
        todo!()
    }
}

impl fmt::Display for EngStr {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
