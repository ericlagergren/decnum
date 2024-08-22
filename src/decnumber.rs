#![cfg(test)]

use core::ffi::c_int;

use decnumber_sys::*;

use crate::{bid::Bid128, dpd::Dpd128};

#[derive(Copy, Clone, Debug)]
pub struct Quad(decQuad);

impl Quad {
    pub fn new(coeff: i128, exp: i16) -> Self {
        // TODO(eric): check `exp`.

        let sign = (coeff < 0) as c_int;
        let bcd = {
            let mut bcd = [0u8; 34];
            let mut bin = coeff.unsigned_abs();
            for c in &mut bcd {
                *c = (bin % 10) as u8;
                bin /= 10;
            }
            bcd
        };
        let mut d = decQuad { bytes: [0u8; 16] };
        unsafe { decQuadFromBCD(&mut d, exp as i32, bcd.as_ptr().cast(), sign) };
        Self(d)
    }

    pub fn from_u32(coeff: u32) -> Self {
        let mut d = decQuad { bytes: [0u8; 16] };
        unsafe { decQuadFromUInt32(&mut d, coeff) };
        Self(d)
    }

    pub fn signbit(self) -> bool {
        unsafe { decQuadIsSigned(&self.0) != 0 }
    }

    pub fn unbiased_exp(self) -> i16 {
        unsafe { decQuadGetExponent(&self.0) as i16 }
    }

    pub fn show(self) {
        unsafe { decQuadShow(&self.0, "\0".as_ptr().cast()) };
    }

    pub const fn to_ne_bytes(self) -> [u8; 16] {
        self.0.bytes
    }
}

impl PartialEq<Quad> for Dpd128 {
    fn eq(&self, other: &Quad) -> bool {
        self.to_ne_bytes() == other.to_ne_bytes()
    }
}

impl PartialEq<Dpd128> for Quad {
    fn eq(&self, other: &Dpd128) -> bool {
        self.to_ne_bytes() == other.to_ne_bytes()
    }
}

impl PartialEq<Quad> for Bid128 {
    fn eq(&self, other: &Quad) -> bool {
        self.to_dpd128() == *other
    }
}

impl PartialEq<Bid128> for Quad {
    fn eq(&self, other: &Bid128) -> bool {
        other.to_dpd128() == *self
    }
}
