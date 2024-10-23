#![allow(dead_code, reason = "TODO")]

use core::cmp::Ordering;

use super::arith128;

#[derive(Copy, Clone, Debug)]
#[allow(non_camel_case_types)]
pub struct u256 {
    pub lo: u128,
    pub hi: u128,
}

impl u256 {
    const fn zero() -> Self {
        Self { lo: 0, hi: 0 }
    }

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

    pub const fn bitlen(self) -> u32 {
        arith128::bitlen(self.hi) + arith128::bitlen(self.lo)
    }

    pub const fn const_shl(self, n: u32) -> Self {
        if n > 128 {
            Self {
                lo: 0,
                hi: self.lo << (n - 128),
            }
        } else {
            Self {
                lo: self.lo << n,
                hi: (self.hi << n) | (self.lo >> (128 - n)),
            }
        }
    }

    pub const fn const_shr(self, n: u32) -> Self {
        if n > 128 {
            Self {
                lo: self.hi >> (n - 128),
                hi: 0,
            }
        } else {
            Self {
                lo: (self.lo >> n) | (self.hi >> (128 - n)),
                hi: self.hi >> n,
            }
        }
    }
}
