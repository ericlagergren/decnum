#![cfg(test)]

use std::{
    ffi::{c_char, c_int, CStr, CString},
    fmt,
    ops::Add,
};

use decnumber_sys::*;

use crate::{
    bid::{Bid128, Bid64},
    dpd::Dpd128,
};

fn ctx64() -> decContext {
    let mut ctx = decContext {
        digits: 0,
        emax: 0,
        emin: 0,
        round: 0,
        traps: 0,
        status: 0,
        clamp: 0,
    };
    unsafe { decContextDefault(&mut ctx, DEC_INIT_DECIMAL64) };
    ctx
}

fn ctx128() -> decContext {
    let mut ctx = decContext {
        digits: 0,
        emax: 0,
        emin: 0,
        round: 0,
        traps: 0,
        status: 0,
        clamp: 0,
    };
    unsafe { decContextDefault(&mut ctx, DEC_INIT_DECIMAL128) };
    ctx
}

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
        let mut d = Self::default();
        unsafe { decQuadFromBCD(&mut d.0, exp as i32, bcd.as_ptr().cast(), sign) };
        d
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

    pub fn set_exponent(self, exp: i16) -> Self {
        let mut ctx = ctx128();
        let mut new = self.clone();
        unsafe { decQuadSetExponent(&mut new.0, &mut ctx, exp as i32) };
        new
    }

    pub fn parse(s: &str) -> Self {
        let s = CString::new(s).unwrap();
        let mut d = Self::default();
        let mut ctx = ctx128();
        unsafe { decQuadFromString(&mut d.0, s.as_ptr(), &mut ctx) };
        d
    }
}

impl Default for Quad {
    fn default() -> Self {
        Self(decQuad { bytes: [0u8; 16] })
    }
}

impl fmt::Display for Quad {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u8; 48];
        let ptr = unsafe { decQuadToString(&self.0, &mut buf[0] as *mut u8 as *mut c_char) };
        let s = unsafe { CStr::from_ptr(ptr) };
        s.to_string_lossy().fmt(f)
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
        self.to_dpd() == *other
    }
}

impl PartialEq<Bid128> for Quad {
    fn eq(&self, other: &Bid128) -> bool {
        other.to_dpd() == *self
    }
}

impl Add for Quad {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut sum = Self::default();
        let mut ctx = ctx128();
        ctx.round = DEC_ROUND_DOWN;
        unsafe { decQuadAdd(&mut sum.0, &self.0, &rhs.0, &mut ctx) };
        sum
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Double(decDouble);

impl Double {
    pub fn new(coeff: i64, exp: i16) -> Self {
        // TODO(eric): check `exp`.

        let sign = (coeff < 0) as c_int;
        let bcd = {
            let mut bcd = [0u8; 16];
            let mut bin = coeff.unsigned_abs();
            for c in &mut bcd {
                *c = (bin % 10) as u8;
                bin /= 10;
            }
            bcd
        };
        let mut d = decDouble { bytes: [0u8; 8] };
        unsafe { decDoubleFromBCD(&mut d, exp as i32, bcd.as_ptr().cast(), sign) };
        Self(d)
    }

    pub fn from_u32(coeff: u32) -> Self {
        let mut d = decDouble { bytes: [0u8; 8] };
        unsafe { decDoubleFromUInt32(&mut d, coeff) };
        Self(d)
    }

    pub fn signbit(self) -> bool {
        unsafe { decDoubleIsSigned(&self.0) != 0 }
    }

    pub fn unbiased_exp(self) -> i16 {
        unsafe { decDoubleGetExponent(&self.0) as i16 }
    }

    pub fn show(self) {
        unsafe { decDoubleShow(&self.0, "\0".as_ptr().cast()) };
    }

    pub const fn to_ne_bytes(self) -> [u8; 8] {
        self.0.bytes
    }

    pub fn parse(s: &str) -> Self {
        let s = CString::new(s).unwrap();
        let mut d = decDouble { bytes: [0u8; 8] };
        let mut ctx = ctx64();
        unsafe { decDoubleFromString(&mut d, s.as_ptr(), &mut ctx) };
        Self(d)
    }
}

impl fmt::Display for Double {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u8; 48];
        let ptr = unsafe { decDoubleToString(&self.0, &mut buf[0] as *mut u8 as *mut c_char) };
        let s = unsafe { CStr::from_ptr(ptr) };
        s.to_string_lossy().fmt(f)
    }
}

impl PartialEq<Double> for Bid64 {
    fn eq(&self, _other: &Double) -> bool {
        true // TODO
    }
}

impl PartialEq<Double> for Quad {
    fn eq(&self, _other: &Double) -> bool {
        true // TODO
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_wat() {
//         let lhs = Quad::parse("1E+2");
//         let rhs = Quad::parse("-1E-6143");
//         let sum = lhs + rhs;
//         println!("{lhs} + {rhs} = {sum}");
//         assert!(false);
//     }
// }
