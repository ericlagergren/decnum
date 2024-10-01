use crate::util::{unlikely, unpredictable};

// TODO(eric): The API `fn quorem(self, u: T)` requires the
// compiler to perform a bunch of moves to swap `self` and `u`.
// We should benchmark to see if it matters and, if so, update
// the API.

/// A 32-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor32 {
    d: u64, // divisor
    v: u64, // reciprocal
    s: u32, // shift
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
    pub const fn quorem(self, u: u32) -> (u32, u32) {
        let (q, r) = div2x1(0, u as u64, self.d as u64, self.v as u64, self.s);
        (q as u32, r as u32)
    }
}

/// A 64-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor64 {
    d: u64, // divisor
    v: u64, // reciprocal
    s: u32, // shift
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
    pub const fn quorem(self, u: u64) -> (u64, u64) {
        div2x1(0, u, self.d, self.v, self.s)
    }
}

/// A 128-bit divisor.
#[derive(Copy, Clone, Debug)]
pub struct Divisor128 {
    d1: u64, // divisor high
    d0: u64, // divisor low
    v: u64,  // reciprocal
    s: u32,  // shift
}

impl Divisor128 {
    pub const fn uninit() -> Self {
        Self {
            d1: 0,
            d0: 0,
            v: 0,
            s: 0,
        }
    }

    pub const fn new(d: u128) -> Self {
        assert!(d != 0);

        let mut d1 = (d >> 64) as u64;
        let mut d0 = d as u64;

        if d1 == 0 {
            let Divisor64 { d, v, s } = Divisor64::new(d0);
            return Self { d1: 0, d0: d, v, s };
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
        let (t1, t0) = umul(v, d0);
        p = p.wrapping_add(t1);
        if p < t1 {
            v -= 1;
            if pack64(p, t0) >= pack64(d1, d0) {
                v -= 1;
            }
        }
        Self { d1, d0, v, s }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    #[inline(always)]
    pub const fn quorem(self, u: u128) -> (u128, u128) {
        let u1 = (u >> 64) as u64;
        let u0 = u as u64;

        if self.d1 == 0 {
            let (q1, r) = div2x1(0, u1, self.d0, self.v, self.s);
            let (q0, r) = div2x1(r, u0, self.d0, self.v, self.s);
            let q = pack64(q1, q0);
            (q, r as u128)
        } else {
            let (q, r) = div3x2(0, u1, u0, self.d1, self.d0, self.v, self.s);
            (q as u128, r)
        }
    }
}

// NB: `d` must be normalized.
#[inline(always)]
const fn div2x1(mut u1: u64, mut u0: u64, d: u64, v: u64, s: u32) -> (u64, u64) {
    if s != 0 {
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
    }

    debug_assert!(d >= 1 << (64 - 1));
    debug_assert!(u1 < d);

    let (q1, q0) = umul(v, u1);
    let (mut q1, q0) = uadd(q1, q0, u1, u0);
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
const fn div3x2(
    mut u2: u64,
    mut u1: u64,
    mut u0: u64,
    d1: u64,
    d0: u64,
    v: u64,
    s: u32,
) -> (u64, u128) {
    if s != 0 {
        u2 = u1 >> (64 - s);
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
    };

    let d = pack64(d1, d0);
    let (q1, q0) = umul(v, u2);
    let (mut q1, q0) = uadd(q1, q0, u2, u1);
    let r1 = u1.wrapping_sub(q1.wrapping_mul(d1));
    let t = {
        let (t1, t0) = umul(d0, q1);
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

/// Returns `x*y = (hi, lo)`.
const fn umul(x: u64, y: u64) -> (u64, u64) {
    // SAFETY: The result is contained in the larger
    // type.
    let wide = unsafe { (x as u128).unchecked_mul(y as u128) };
    let hi = (wide >> 64) as u64;
    let lo = wide as u64;
    (hi, lo)
}

/// Returns `x+y = (hi, lo)`
const fn uadd(x1: u64, x0: u64, y1: u64, y0: u64) -> (u64, u64) {
    let x = ((x1 as u128) << 64) | (x0 as u128);
    let y = ((y1 as u128) << 64) | (y0 as u128);
    let sum = x + y;
    let hi = (sum >> 64) as u64;
    let lo = sum as u64;
    (hi, lo)
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
            let v0 = rand_word!();

            let u = pack64(u1, u0);
            let mut v = pack64(v1, v0);
            if v == 0 {
                v = 1;
            }

            let got = Divisor128::new(v).quorem(u);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }
}
