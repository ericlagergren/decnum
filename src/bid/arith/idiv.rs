/// Compute the quotient and remainder `(q, r)` where
///
/// ```text
/// q = (u1, u0) / v
/// r = (u1, u0) % v
/// ```
#[no_mangle]
pub const fn div128x64(u1: u64, u0: u64, v: u64, rec: u64) -> (u128, u64) {
    if u1 == 0 {
        let (q, r) = div2x1(0, u0, v, rec);
        return (q as u128, r);
    }
    let (q1, r) = div2x1(0, u1, v, rec);
    let (q0, r) = div2x1(r, u0, v, rec);
    let q = ((q1 as u128) << 64) | (q0 as u128);
    (q, r)
}

/// Compute the quotient and remainder `(q, r)` where
///
/// ```text
/// q = (u1, u0) / v
/// r = (u1, u0) % v
/// ```
#[no_mangle]
pub const fn div128x128(
    mut u1: u64,
    mut u0: u64,
    mut v1: u64,
    mut v0: u64,
    rec: u64,
) -> (u128, u128) {
    if false {
        if u1 == 0 {
            if v1 == 0 {
                // (0, u0) / (0, v0)
                let (q, r) = div2x1(0, u0, v0, rec);
                return (q as u128, r as u128);
            }
            // (0, u0) / (v1, v0)
            return (0, u0 as u128);
        }
        debug_assert!(u1 != 0);

        if v1 == 0 {
            // (u1, u0) / (0, v0)
            let (q, r) = div128x64(u1, u0, v0, rec);
            return (q, r as u128);
        }
        debug_assert!(v1 != 0);
    }

    debug_assert!(v1 != 0);
    debug_assert!(v0 != 0);
    debug_assert!(u1 != 0);
    debug_assert!(u0 != 0);

    let mut u2 = 0;

    let s = v1.leading_zeros();
    if s != 0 {
        v1 = (v1 << s) | (v0 >> (64 - s));
        v0 <<= s;

        u2 = u1 >> (64 - s);
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
    };

    let (q, r) = div3x2(u2, u1, u0, v1, v0, rec);
    (q as u128, r >> s)
}

const fn div2x1(mut u1: u64, mut u0: u64, mut d: u64, rec: u64) -> (u64, u64) {
    let s = d.leading_zeros();
    if s != 0 {
        u1 = (u1 << s) | (u0 >> (64 - s));
        u0 <<= s;
        d <<= s;
    }

    debug_assert!(d >= 1 << (64 - 1));
    debug_assert!(u1 < d);

    let (q1, q0) = umul(rec, u1);
    let (mut q1, q0) = uadd(q1, q0, u1, u0);
    q1 = q1.wrapping_add(1);
    let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
    if r > q0 {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if r >= d {
        q1 += 1;
        r -= d;
    }
    (q1, r >> s)
}

/// Computes a reciprocal for [`div128x64`].
pub const fn reciprocal2x1(d1: u64) -> u64 {
    let u = d1 << d1.leading_zeros();
    let x1 = !u;
    let x0 = u64::MAX;
    let x = ((x1 as u128) << 64) | (x0 as u128);
    (x / (u as u128)) as u64
}

const fn div3x2(u2: u64, u1: u64, u0: u64, d1: u64, d0: u64, v: u64) -> (u64, u128) {
    let d = pack(d1, d0);
    let (q1, q0) = umul(v, u2);
    let (mut q1, q0) = uadd(q1, q0, u1, u0);
    let r1 = u1.wrapping_sub(q1.wrapping_mul(d1));
    let t = {
        let (t1, t0) = umul(d0, q1);
        pack(t1, t0)
    };
    let mut r = pack(r1, u0).wrapping_sub(t).wrapping_sub(d);
    q1 = q1.wrapping_add(1);
    if (r >> 64) as u64 >= q0 {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if r >= d {
        q1 = q1.wrapping_add(1);
        r = r.wrapping_sub(d);
    }
    (q1, r)
}

/// Computes a reciprocal for [`div128x128`].
pub const fn reciprocal3x2(mut d1: u64, mut d0: u64) -> u64 {
    let s = d1.leading_zeros();
    if s != 0 {
        d1 = (d1 << s) | (d0 >> (64 - s));
        d0 <<= s;
    }
    let mut v = reciprocal2x1(d1);
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
    v
}

const fn umul(x: u64, y: u64) -> (u64, u64) {
    // SAFETY: The result is contained in the larger
    // type.
    let wide = unsafe { (x as u128).unchecked_mul(y as u128) };
    let hi = (wide >> 64) as u64;
    let lo = wide as u64;
    (hi, lo)
}

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
    use rand::prelude::*;

    use super::*;

    #[test]
    fn test_div128x128() {
        const fn golden(u: u128, v: u128) -> (u128, u128) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        for _ in 0..100_000 {
            let u = random();
            let v = loop {
                let v = random();
                if v != 0 {
                    break v;
                }
            };

            let u1 = (u >> 64) as u64;
            let u0 = u as u64;

            let v1 = (v >> 64) as u64;
            let v0 = v as u64;

            if u1 == 0 || u0 == 0 || v1 == 0 || v0 == 0 {
                continue;
            }

            let rec = reciprocal3x2(v1, v0);
            let got = div128x128(u1, u0, v1, v0, rec);
            let want = golden(u, v);
            assert_eq!(got, want, "{u}/{v}");
        }
    }

    #[test]
    fn test_div128x64() {
        const fn golden(u: u128, v: u64) -> (u128, u64) {
            let q = u / (v as u128);
            let r = u % (v as u128);
            (q, r as u64)
        }
        for _ in 0..100_000 {
            let u1 = random();
            let u0 = random();
            let v: u64 = loop {
                let v = random();
                if v != 0 {
                    break v;
                }
            };

            let u = ((u1 as u128) << 64) | (u0 as u128);
            let rec = reciprocal2x1(v);
            let got = div128x64(u1, u0, v, rec);
            let want = golden(u, v);
            assert_eq!(got, want, "{u}/{v}");
        }
    }

    #[test]
    fn test_div128x64_u1_zero() {
        const fn golden(u: u64, v: u64) -> (u128, u64) {
            let q = u / v;
            let r = u % v;
            (q as u128, r)
        }
        for _ in 0..100_000 {
            let u = random();
            let v: u64 = loop {
                let v = random();
                if v != 0 {
                    break v;
                }
            };

            let rec = reciprocal2x1(v);
            let got = div128x64(0, u, v, rec);
            let want = golden(u, v);
            assert_eq!(got, want, "{u}/{v}");
        }
    }
}
