use core::fmt;

/// A decimal converted to scientific notation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SciStr {}

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
