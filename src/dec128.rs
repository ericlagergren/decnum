use core::ops::Add;

use super::uint96::u96;

//const SIGNBIT: u16 = 1 << 15;

/// A 128-bit decimal.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct d128 {
    _unused: u16,
    flags: u16,
    val: u96,
}

impl d128 {
    /// The largest value that can be represented by this type.
    pub const MAX: Self = Self::new(79228162514264337593543950335);
    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self::new(-79228162514264337593543950335);

    const fn new(_v: i128) -> Self {
        Self {
            _unused: 0,
            flags: 0,
            val: u96::MIN,
        }
        // if v < 0 {
        //     Self {
        //         _unused: 0,
        //         flags: SIGNBIT,
        //         val: u96::new(v.unsigned_abs()),
        //     }
        // } else {
        //     Self {
        //         _unused: 0,
        //         flags: 0,
        //         val: u96::new(v.unsigned_abs()),
        //     }
        // }
    }

    /// Returns `self + other`.
    #[must_use = "this returns the result of the operation \
                      without modifying the original"]
    pub const fn checked_add(self, _other: Self) -> Option<Self> {
        None
    }
}

impl Add for d128 {
    type Output = Self;

    fn add(self, _other: Self) -> Self::Output {
        todo!()
    }
}
