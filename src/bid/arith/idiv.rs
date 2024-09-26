use crate::util::{unlikely, unpredictable};

#[derive(Copy, Clone, Debug)]
pub struct Reciprocals128 {
    d1: u64,
    d0: u64,
    v: u64,
}

impl Reciprocals128 {
    const fn zero() -> Self {
        Self { d1: 0, d0: 0, v: 0 }
    }

    const fn new(d1: u64, d0: u64) -> Self {
        let v = if d1 == 0 {
            Divisor64::new(d1).v
        } else {
            Divisor128::new(d1, d0).v
        };
        Self { d1, d0, v }
    }

    const fn quorem(self, u: u128) -> (u128, u128) {
        let Self { d1, d0, v } = self;
        if self.d1 == 0 {
            let (q, r) = Divisor64 { d: d0, v }.quorem(u);
            (q, r as u128)
        } else {
            Divisor128 { d1, d0, v }.quorem(u)
        }
    }
}

/// A 64-bit divisor.
#[derive(Copy, Clone, Debug)]
struct Divisor64 {
    d: u64, // divisor
    v: u64, // reciprocal
}

impl Divisor64 {
    pub const fn new(d: u64) -> Self {
        let u = d << d.leading_zeros();
        let x = pack(!u, u64::MAX);
        let v = (x / (u as u128)) as u64;
        Self { d, v }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    pub const fn quorem(self, u: u128) -> (u128, u64) {
        let u1 = (u >> 64) as u64;
        let u0 = u as u64;
        self.div128x64(u1, u0)
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = (u1, u0) / self
    /// r = (u1, u0) % self
    /// ```
    #[no_mangle]
    pub const fn div128x64(self, u1: u64, u0: u64) -> (u128, u64) {
        if u1 == 0 {
            let (q, r) = self.div2x1(0, u0);
            return (q as u128, r);
        }
        let (q1, r) = self.div2x1(0, u1);
        let (q0, r) = self.div2x1(r, u0);
        (pack(q1, q0), r)
    }

    /// Computes the quotient and remainder `(q, r)` such that
    ///
    /// ```text
    /// q = (u1, u0) / self
    /// r = (u1, u0) / self
    /// ```
    const fn div2x1(self, mut u1: u64, mut u0: u64) -> (u64, u64) {
        let Self { mut d, v } = self;

        let s = d.leading_zeros();
        if s != 0 {
            u1 = (u1 << s) | (u0 >> (64 - s));
            u0 <<= s;
            d <<= s;
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
}

/// A 128-bit divisor.
#[derive(Copy, Clone, Debug)]
struct Divisor128 {
    d1: u64, // divisor high
    d0: u64, // divisor low
    v: u64,  // reciprocal
}

impl Divisor128 {
    pub const fn new(mut d1: u64, mut d0: u64) -> Self {
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
            if pack(p, t0) >= pack(d1, d0) {
                v -= 1;
            }
        }
        Self { d1, d0, v }
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = u / self
    /// r = u % self
    /// ```
    pub const fn quorem(self, u: u128) -> (u128, u128) {
        let u1 = (u >> 64) as u64;
        let u0 = u as u64;
        self.div128x128(u1, u0)
    }

    /// Compute the quotient and remainder `(q, r)` where
    ///
    /// ```text
    /// q = (u1, u0) / v
    /// r = (u1, u0) % v
    /// ```
    #[no_mangle]
    pub const fn div128x128(self, mut u1: u64, mut u0: u64) -> (u128, u128) {
        let Self { mut d1, mut d0, v } = self;

        // if u1 == 0 {
        //     if d1 == 0 {
        //         // (0, u0) / (0, d0)
        //         let (q, r) = div2x1(0, u0, d0, rec);
        //         return (q as u128, r as u128);
        //     }
        //     // (0, u0) / (d1, d0)
        //     return (0, u0 as u128);
        // }
        // debug_assert!(u1 != 0);

        // if d1 == 0 {
        //     // (u1, u0) / (0, d0)
        //     let (q, r) = div128x64(u1, u0, d0, rec);
        //     return (q, r as u128);
        // }
        // debug_assert!(d1 != 0);

        // debug_assert!(d1 != 0);
        // debug_assert!(d0 != 0);
        // debug_assert!(u1 != 0);
        // debug_assert!(u0 != 0);

        let (q, r) = self.div3x2(0, u1, u0);
        (q as u128, r)
    }

    /// Computes the quotient and remainder `(q, r)` such that
    ///
    /// ```text
    /// q = (u2, u1, u0) / (d1, d0)
    /// r = (u2, u1, u0) / (d1, d0)
    /// ```
    const fn div3x2(self, mut u2: u64, mut u1: u64, mut u0: u64) -> (u64, u128) {
        let Self { mut d1, mut d0, v } = self;

        let s = d1.leading_zeros();
        if s != 0 {
            d1 = (d1 << s) | (d0 >> (64 - s));
            d0 <<= s;

            u2 = u1 >> (64 - s);
            u1 = (u1 << s) | (u0 >> (64 - s));
            u0 <<= s;
        };

        let d = pack(d1, d0);
        let (q1, q0) = umul(v, u2);
        let (mut q1, q0) = uadd(q1, q0, u2, u1);
        let r1 = u1.wrapping_sub(q1.wrapping_mul(d1));
        let t = {
            let (t1, t0) = umul(d0, q1);
            pack(t1, t0)
        };
        let mut r = pack(r1, u0).wrapping_sub(t).wrapping_sub(d);
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

const fn pack(hi: u64, lo: u64) -> u128 {
    ((hi as u128) << 64) | (lo as u128)
}

#[cfg(test)]
mod tests {
    use rand::{distributions::Standard, prelude::*};

    use super::*;

    fn rand_word<T>() -> T
    where
        T: Default,
        Standard: Distribution<T>,
    {
        let zero = thread_rng().gen_range(0..3) == 0;
        if zero {
            T::default()
        } else {
            random()
        }
    }

    #[test]
    fn test_div128x64() {
        const fn golden(u: u128, v: u64) -> (u128, u64) {
            let q = u / (v as u128);
            let r = u % (v as u128);
            (q, r as u64)
        }
        for i in 0..100_000 {
            let u1 = rand_word();
            let u0 = rand_word();
            let v = loop {
                let v = random();
                if v != 0 {
                    break v;
                }
            };
            let u = pack(u1, u0);
            let got = Divisor64::new(v).div128x64(u1, u0);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }

    #[test]
    fn test_div128x128() {
        const fn golden(u: u128, v: u128) -> (u128, u128) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        for i in 0..100_000 {
            let u1 = rand_word();
            let u0 = rand_word();
            let v1 = rand_word();
            let v0 = loop {
                let v0 = rand_word();
                if v0 != 0 || v1 != 0 {
                    break v0;
                }
            };

            let u = pack(u1, u0);
            let v = pack(v1, v0);

            let got = Divisor128::new(v1, v0).div128x128(u1, u0);
            let want = golden(u, v);
            assert_eq!(got, want, "#{i}: {u}/{v}");
        }
    }
}
