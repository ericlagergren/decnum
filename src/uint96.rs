use core::{
    cmp::Ordering,
    fmt,
    hash::Hash,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

#[repr(C)]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct u96 {
    lo: u64,
    hi: u32,
}

impl u96 {
    const MASK: u128 = !((1u128 << 96) - 1);

    /// The largest value that can be represented by this type.
    pub const MAX: Self = Self {
        lo: u64::MAX,
        hi: u32::MAX,
    };
    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self { lo: 0, hi: 0 };

    /// Creates a new [`u96`].
    pub const fn new(v: u128) -> Self {
        debug_assert!(v & Self::MASK == 0);

        Self {
            lo: v as u64,
            hi: (v >> 64) as u32,
        }
    }

    const fn to_u128(self) -> u128 {
        (self.lo as u128) | ((self.hi as u128) << 64)
    }

    /// Returns `self + other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_add(self, other: Self) -> Option<Self> {
        let (lo, c) = self.lo.overflowing_add(other.lo);
        let hi = match self.hi.checked_add(other.hi) {
            Some(hi) => hi,
            None => return None,
        };
        match hi.checked_add(c as u32) {
            Some(hi) => Some(Self { lo, hi }),
            None => None,
        }
    }

    /// Returns `self + other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn wrapping_add(self, other: Self) -> Self {
        let (lo, c) = self.lo.overflowing_add(other.lo);
        let hi = self.hi.wrapping_add(other.hi).wrapping_add(c as u32);
        Self { lo, hi }
    }

    /// Returns `self & other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn bitand(self, other: Self) -> Self {
        Self {
            lo: self.lo & other.lo,
            hi: self.hi & other.hi,
        }
    }

    /// Returns `self | other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn bitor(self, other: Self) -> Self {
        Self {
            lo: self.lo | other.lo,
            hi: self.hi | other.hi,
        }
    }
}

impl Add for u96 {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        if cfg!(debug_assertions) {
            self.checked_add(other).unwrap()
        } else {
            self.wrapping_add(other)
        }
    }
}

impl AddAssign for u96 {
    fn add_assign(&mut self, other: Self) {
        if cfg!(debug_assertions) {
            *self = self.checked_add(other).unwrap()
        } else {
            *self = self.wrapping_add(other)
        }
    }
}

impl BitAnd for u96 {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        self.bitand(other)
    }
}

impl BitAndAssign for u96 {
    fn bitand_assign(&mut self, other: Self) {
        *self = self.bitand(other);
    }
}

impl BitOr for u96 {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        self.bitor(other)
    }
}

impl BitOrAssign for u96 {
    fn bitor_assign(&mut self, other: Self) {
        *self = self.bitor(other);
    }
}

impl PartialEq<u64> for u96 {
    fn eq(&self, other: &u64) -> bool {
        self.hi == 0 && self.lo == *other
    }
}

impl PartialOrd<u64> for u96 {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        if self.hi != 0 {
            Some(Ordering::Greater)
        } else {
            PartialOrd::partial_cmp(&self.lo, other)
        }
    }
}

impl fmt::Display for u96 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_u128().fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! u96 {
        ($v:literal) => {{
            u96::new($v)
        }};
    }

    #[test]
    fn test_wrapping_add() {
        let tests = [
            (u96!(0), u96!(0), u96!(0)),
            (u96!(1), u96!(0), u96!(1)),
            (u96!(1), u96!(1), u96!(2)),
            (u96::MAX, u96!(1), u96!(0)),
            (u96::MAX, u96!(2), u96!(1)),
        ];
        for (i, (x, y, want)) in tests.into_iter().enumerate() {
            let got = x.wrapping_add(y);
            assert_eq!(got, want, "#{i}");
        }
    }
}
