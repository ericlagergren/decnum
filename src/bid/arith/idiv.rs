//! Implement division via recpirocal via "Improved division by
//! invariant integers" by N. Möller and T. Granlund.
//!
//! <https://gmplib.org/~tege/division-paper.pdf>

use crate::util::{unlikely, unpredictable};

// TODO(eric): The API `fn quorem(self, u: T)` requires the
// compiler to perform a bunch of moves to swap `self` and `u`.
// We should benchmark to see if it matters and, if so, update
// the API.

/// A 32-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor32 {
    pub d: u64, // divisor
    pub v: u64, // reciprocal
    pub s: u32, // shift
}

impl Divisor32 {
    pub const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    pub const fn new(d: u32) -> Self {
        assert!(d != 0);

        let Divisor64 { d, v, s } = Divisor64::new(d as u64);
        Self { d, v, s }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    #[allow(dead_code)]
    pub const fn quorem(self, u: u32) -> (u32, u32) {
        let (q, r) = div2x1(0, u as u64, self.d as u64, self.v as u64, self.s);
        (q as u32, r as u32)
    }
}

/// A 64-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor64 {
    pub d: u64, // divisor
    pub v: u64, // reciprocal
    pub s: u32, // shift
}

impl Divisor64 {
    pub const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    pub const fn new(mut d: u64) -> Self {
        assert!(d != 0);

        let s = d.leading_zeros();
        d <<= s;
        let x = pack64(!d, u64::MAX);
        let v = (x / (d as u128)) as u64;
        Self { d, v, s }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    #[allow(dead_code)]
    pub const fn quorem(self, u: u64) -> (u64, u64) {
        div2x1(0, u, self.d, self.v, self.s)
    }
}

/// A 128-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor128 {
    pub d: u128, // divisor
    pub v: u64,  // reciprocal
    pub s: u32,  // shift
}

impl Divisor128 {
    pub const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    pub const fn new(d: u128) -> Self {
        assert!(d != 0);

        let mut d1 = (d >> 64) as u64;
        let mut d0 = d as u64;

        if d1 == 0 {
            let Divisor64 { d, v, s } = Divisor64::new(d0);
            return Self { d: d as u128, v, s };
        }

        let s = d1.leading_zeros();
        if s != 0 {
            d1 = (d1 << s) | (d0 >> (64 - s));
            d0 <<= s;
        }

        let mut v = Divisor64::new(d1).v;
        let mut p = d1.wrapping_mul(v).wrapping_add(d0);
        if p < d0 {
            v -= 1;
            if p >= d1 {
                v -= 1;
                p -= d1;
            }
            p = p.wrapping_sub(d1);
        }
        let (t1, t0) = umul64(v, d0);
        p = p.wrapping_add(t1);
        if p < t1 {
            v -= 1;
            if pack64(p, t0) >= pack64(d1, d0) {
                v -= 1;
            }
        }
        let d = pack64(d1, d0);
        Self { d, v, s }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    #[inline(always)]
    #[allow(dead_code)]
    pub const fn quorem(self, u: u128) -> (u128, u128) {
        let u1 = (u >> 64) as u64;
        let u0 = u as u64;

        let d1 = (self.d >> 64) as u64;
        let d0 = self.d as u64;

        if d1 == 0 {
            let (q1, r) = div2x1(0, u1, d0, self.v, self.s);
            let (q0, r) = div2x1(r, u0, d0, self.v, self.s);
            let q = pack64(q1, q0);
            (q, r as u128)
        } else {
            let (q, r) = div3x2(0, u1, u0, d1, d0, self.v, self.s);
            (q as u128, r)
        }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    //#[inline(always)]
    #[no_mangle]
    pub const fn quorem3(self, _u1: u128, _u0: u128) -> (u128, u128) {
        // NB: `d` must be normalized.
        #[inline(always)]
        #[allow(dead_code)]
        const fn div2x1(mut u1: u64, mut u0: u64, d: u64, v: u64, s: u32) -> (u64, u64) {
            if s != 0 {
                u1 = (u1 << s) | (u0 >> (64 - s));
                u0 <<= s;
            }

            debug_assert!(d >= 1 << (64 - 1));
            debug_assert!(u1 < d);

            let (q1, q0) = umul64(v, u1);
            let (mut q1, q0) = uadd64(q1, q0, u1, u0);
            q1 = q1.wrapping_add(1);
            let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
            if unpredictable!(r > q0) {
                q1 = q1.wrapping_sub(1);
                r = r.wrapping_add(d);
            }
            if unlikely!(r >= d) {
                q1 += 1;
                r -= d;
            }
            (q1, r >> s)
        }

        todo!()

        // let u1 = (u >> 64) as u64;
        // let u0 = u as u64;

        // if self.d1 == 0 {
        //     let (_, r) = div2x1(0, u2, self.d0, self.v, self.s);
        //     let (q1, r) = div2x1(r, u1, self.d0, self.v, self.s);
        //     let (q0, r) = div2x1(r, u0, self.d0, self.v, self.s);
        //     let q = pack64(q1, q0);
        //     (q, r as u128)
        // } else {
        //     let d = ((self.d1 as u128) << 64) | (self.d0 as u128);
        //     let (q, r) = div4x2(u1, u0, d, self.v, self.s);
        //     (q as u128, r)
        // }
    }
}

// NB: `d` must be normalized.
#[inline(always)]
pub(super) const fn div2x1(mut u1: u64, mut u0: u64, d: u64, v: u64, s: u32) -> (u64, u64) {
    if s != 0 {
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
    }

    debug_assert!(d >= 1 << (64 - 1));
    debug_assert!(u1 < d);

    let (q1, q0) = umul64(v, u1);
    let (mut q1, q0) = uadd64(q1, q0, u1, u0);
    q1 = q1.wrapping_add(1);
    let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
    if unpredictable!(r > q0) {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if unlikely!(r >= d) {
        q1 += 1;
        r -= d;
    }
    (q1, r >> s)
}

// NB: `d1`, `d0` must be normalized.
#[inline(always)]
pub(super) const fn div3x2(
    mut u2: u64,
    mut u1: u64,
    mut u0: u64,
    d1: u64,
    d0: u64,
    v: u64,
    s: u32,
) -> (u64, u128) {
    if s != 0 {
        u2 = (u2 << s) | (u1 >> (64 - s));
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
    };

    debug_assert!(pack64(d1, d0) >= 1 << (128 - 1));
    debug_assert!(pack64(u2, u1) < pack64(d1, d0));

    let d = pack64(d1, d0);
    let (q1, q0) = umul64(v, u2);
    let (mut q1, q0) = uadd64(q1, q0, u2, u1);
    let r1 = u1.wrapping_sub(q1.wrapping_mul(d1));
    let t = {
        let (t1, t0) = umul64(d0, q1);
        pack64(t1, t0)
    };
    let mut r = pack64(r1, u0).wrapping_sub(t).wrapping_sub(d);
    q1 = q1.wrapping_add(1);
    if unpredictable!((r >> 64) as u64 >= q0) {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if unlikely!(r >= d) {
        q1 = q1.wrapping_add(1);
        r = r.wrapping_sub(d);
    }
    (q1, r >> s)
}

// NB: `d` must be normalized.
#[inline(always)]
#[allow(dead_code)]
pub(super) const fn div4x2(mut u1: u128, mut u0: u128, d: u128, v: u128, s: u32) -> (u128, u128) {
    if s != 0 {
        u1 = (u1 << s) | (u0 >> (128 - s));
        u0 <<= s;
    }

    debug_assert!(d >= 1 << (128 - 1));
    debug_assert!(u1 < d);

    let (q1, q0) = umul128(v, u1);
    let (mut q1, q0) = uadd128(q1, q0, u1, u0);
    q1 = q1.wrapping_add(1);
    let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
    if unpredictable!(r > q0) {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if unlikely!(r >= d) {
        q1 += 1;
        r -= d;
    }
    (q1, r >> s)
}

/// Returns `x*y = (hi, lo)`.
const fn umul64(x: u64, y: u64) -> (u64, u64) {
    // SAFETY: The result is contained in the larger
    // type.
    let wide = unsafe { (x as u128).unchecked_mul(y as u128) };
    let hi = (wide >> 64) as u64;
    let lo = wide as u64;
    (hi, lo)
}

// Returns `x*y = (hi, lo)`.
const fn umul128(x: u128, y: u128) -> (u128, u128) {
    let x1 = (x >> 64) as u64;
    let x0 = x as u64;
    let y1 = (y >> 64) as u64;
    let y0 = y as u64;

    /// Returns `lhs * rhs + carry`.
    const fn carrying_mul(lhs: u64, rhs: u64, carry: u64) -> (u64, u64) {
        // SAFETY: The result is contained in the larger type.
        let wide = unsafe {
            (lhs as u128)
                .unchecked_mul(rhs as u128)
                .unchecked_add(carry as u128)
        };
        (wide as u64, (wide >> 64) as u64)
    }

    let (p1, p2) = carrying_mul(x0, y0, 0);
    let (p2, p31) = carrying_mul(x0, y1, p2);
    let (p2, p32) = carrying_mul(x1, y0, p2);
    let (p3, p4o) = p31.overflowing_add(p32);
    let (p3, p4) = carrying_mul(x1, y1, p3);
    let p4 = p4.wrapping_add(p4o as u64);

    let hi = p3 as u128 | (p4 as u128) << 64; // hi
    let lo = p1 as u128 | (p2 as u128) << 64; // lo
    (hi, lo)
}

/// Returns `x+y = (hi, lo)`, wrapping on overflow.
const fn uadd64(x1: u64, x0: u64, y1: u64, y0: u64) -> (u64, u64) {
    let (z0, c) = x0.overflowing_add(y0);
    let z1 = x1.wrapping_add(y1).wrapping_add(c as u64);
    (z1, z0)
}

/// Returns `x+y = (hi, lo)`, wrapping on overflow.
const fn uadd128(x1: u128, x0: u128, y1: u128, y0: u128) -> (u128, u128) {
    let (z0, c) = x0.overflowing_add(y0);
    let z1 = x1.wrapping_add(y1).wrapping_add(c as u128);
    (z1, z0)
}

const fn pack64(hi: u64, lo: u64) -> u128 {
    ((hi as u128) << 64) | (lo as u128)
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    macro_rules! non_zero_word {
        () => {
            loop {
                let x = random();
                if x != 0 {
                    break x;
                }
            }
        };
    }

    macro_rules! rand_word {
        () => {{
            let zero = thread_rng().gen_range(0..3) == 0;
            if zero {
                0
            } else {
                random()
            }
        }};
    }

    #[test]
    fn test_divisor32() {
        const fn golden(u: u32, v: u32) -> (u32, u32) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        for i in 0..100_000 {
            let u = non_zero_word!();
            let v = non_zero_word!();
            let got = Divisor32::new(v).quorem(u);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }

    #[test]
    fn test_divisor64() {
        const fn golden(u: u64, v: u64) -> (u64, u64) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        for i in 0..100_000 {
            let u = non_zero_word!();
            let v = non_zero_word!();
            let got = Divisor64::new(v).quorem(u);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }

    #[test]
    fn test_divisor128() {
        const fn golden(u: u128, v: u128) -> (u128, u128) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        for i in 0..100_000 {
            let u1 = rand_word!();
            let u0 = rand_word!();
            let v1 = rand_word!();
            let mut v0 = rand_word!();
            if v1 == 0 && v0 == 0 {
                v0 |= 1;
            }

            let u = pack64(u1, u0);
            let mut v = pack64(v1, v0);

            let got = Divisor128::new(v).quorem(u);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");

            // let u2 = rand_word!();
            // if v == 1 {
            //     v0 += 1;
            //     v += 1;
            // }

            // let got = Divisor128::new(v).quorem2(u2, u);
            // #[allow(non_camel_case_types)]
            // type u256 = ruint::Uint<256, 4>;
            // let u = u256::from_limbs([u0, u1, u2, 0]);
            // let v = u256::from_limbs([v0, v1, 0, 0]);
            // let want: (u128, u128) = (
            //     (u / v).try_into().unwrap(), // q
            //     (u % v).try_into().unwrap(), // r
            // );
            // assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }
}
