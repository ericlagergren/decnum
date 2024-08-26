#![cfg(test)]

use core::{fmt, mem};

use dfp_number_sys::{bid128_000 as sys, BID128 as _BID128, RM_NEAREST_EVEN};

use crate::bid::Bid128;

#[derive(Copy, Clone, Debug)]
pub struct BID128(_BID128);

impl BID128 {
    pub fn new(coeff: i128, exp: i16) -> Self {
        let x = if coeff <= i64::MAX as i128 {
            sys::bid128_from_int64(coeff as i64)
        } else {
            let mut buf = itoa::Buffer::new();
            let mut flags = 0;
            sys::bid128_from_string(buf.format(coeff), RM_NEAREST_EVEN, &mut flags)
        };
        Self(sys::bid128_scalbn(x, exp as i32))
    }

    pub fn parse(s: &str) -> Self {
        let mut flags = 0;
        Self(sys::bid128_from_string(s, RM_NEAREST_EVEN, &mut flags))
    }
}

impl fmt::Display for BID128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut flags = 0;
        sys::bid128_to_string(self.0, &mut flags).fmt(f)
    }
}

impl PartialEq<Bid128> for BID128 {
    fn eq(&self, other: &Bid128) -> bool {
        let lhs: u128 = unsafe { mem::transmute_copy(self) };
        let rhs = other.to_bits();
        lhs == rhs
    }
}

impl PartialEq<BID128> for Bid128 {
    fn eq(&self, other: &BID128) -> bool {
        other == self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let x = BID128::new(10i128.pow(34) - 1, 6112);
        println!("x = {x}");
    }
}
