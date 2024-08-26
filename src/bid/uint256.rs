use core::cmp::Ordering;

use super::arith128;

#[derive(Copy, Clone, Debug)]
#[allow(non_camel_case_types)]
pub(super) struct u256 {
    lo: u128,
    hi: u128,
}

impl u256 {
    /// Reports whether `self == other`.
    pub const fn const_cmp(self, other: Self) -> Ordering {
        match arith128::const_cmp(self.hi, other.hi) {
            Ordering::Equal => arith128::const_cmp(self.lo, other.lo),
            ord => ord,
        }
    }

    /// Reports whether `self == other`.
    pub const fn const_eq(self, other: Self) -> bool {
        self.hi == other.hi && self.lo == other.lo
    }

    pub const fn mulu128(self, other: u128) -> Self {
        self.lo.carrying_mul(other);
    }
}
