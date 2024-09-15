#![allow(dead_code, reason = "TODO")]

use core::cmp::Ordering;

use super::arith128;

#[derive(Copy, Clone, Debug)]
#[allow(non_camel_case_types)]
pub(super) struct u256 {
    lo: u128,
    hi: u128,
}

impl u256 {
    /// Creates a `u256`.
    pub const fn new(lo: u128) -> Self {
        Self { lo, hi: 0 }
    }

    /// Creates a `u256`.
    pub const fn from_parts(hi: u128, lo: u128) -> Self {
        Self { hi, lo }
    }

    /// Reports whether `self == other`.
    pub const fn const_cmp(self, other: Self) -> Ordering {
        match arith128::const_cmp(self.hi, other.hi) {
            Ordering::Equal => arith128::const_cmp(self.lo, other.lo),
            ord => ord,
        }
    }

    /// Reports whether `self == other`.
    pub const fn const_cmp128(self, other: u128) -> Ordering {
        if self.hi != 0 {
            Ordering::Greater
        } else {
            arith128::const_cmp(self.lo, other)
        }
    }

    /// Reports whether `self == other`.
    pub const fn const_eq(self, other: Self) -> bool {
        self.hi == other.hi && self.lo == other.lo
    }

    /// Reports whether `self == other`.
    pub const fn const_eq128(self, other: u128) -> bool {
        self.hi == 0 && self.lo == other
    }
}
