//! Implement division via recpirocal via "Improved division by
//! invariant integers" by N. Möller and T. Granlund.
//!
//! <https://gmplib.org/~tege/division-paper.pdf>

use crate::util::{unlikely, unpredictable};

pub(super) const fn recip2x1(mut d: u64) -> (u64, u64, u32) {
    assert!(d != 0);

    let s = d.leading_zeros();
    d <<= s;
    let x = pack64(!d, u64::MAX);
    let v = (x / (d as u128)) as u64;
    (d, v, s)
}

pub(super) const fn recip3x2(d: u128) -> (u128, u64, u32) {
    assert!(d != 0);

    let mut d1 = (d >> 64) as u64;
    let mut d0 = d as u64;

    let s = d1.leading_zeros();
    if s != 0 {
        d1 = (d1 << s) | (d0 >> (64 - s));
        d0 <<= s;
    }

    let mut v = recip2x1(d1).1;
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
    (d, v, s)
}

pub(super) const fn recip4x2(mut d: u128) -> (u128, u128, u32) {
    assert!(d != 0);

    /// Returns `(q, r)` such that
    ///
    /// ```text
    /// q = (u1, u0) / v
    /// r = (u1, u0) % v
    /// ```
    const fn div4x2(u1: u128, u0: u128, mut v: u128) -> (u128, u128) {
        assert!(v != 0);
        assert!(v > u1);

        if u1 == 0 {
            return (u0 / v, u0 % v);
        }

        let s = v.leading_zeros();
        v <<= s;
        let vn1 = v >> 64;
        let vn0 = v as u64 as u128;

        let un32 = if s != 0 {
            (u1 << s) | (u0 >> (128 - s))
        } else {
            u1
        };
        let un10 = u0 << s;
        let un1 = un10 >> 64;
        let un0 = un10 as u64 as u128;

        let mut q1 = un32 / vn1;
        let mut rhat = un32 % vn1;

        const TWO64: u128 = 1 << 64;

        while q1 >= TWO64 || q1.wrapping_mul(vn0) > TWO64.wrapping_mul(rhat).wrapping_add(un1) {
            q1 = q1.wrapping_sub(1);
            rhat = rhat.wrapping_add(vn1);
            if rhat >= TWO64 {
                break;
            }
        }

        let un21 = un32
            .wrapping_mul(TWO64)
            .wrapping_add(un1)
            .wrapping_sub(q1.wrapping_mul(v));
        let mut q0 = un21 / vn1;
        let mut rhat = un21.wrapping_sub(q0.wrapping_mul(vn1));

        while q0 >= TWO64 || q0.wrapping_mul(vn0) > TWO64.wrapping_mul(rhat).wrapping_add(un0) {
            q0 = q0.wrapping_sub(1);
            rhat = rhat.wrapping_add(vn1);
            if rhat >= TWO64 {
                break;
            }
        }

        let q = q1.wrapping_mul(TWO64).wrapping_add(q0);
        let r = un21
            .wrapping_mul(TWO64)
            .wrapping_add(un0)
            .wrapping_sub(q0.wrapping_mul(v));
        (q, r >> s)
    }

    let s = d.leading_zeros();
    d <<= s;
    let v = div4x2(!d, u128::MAX, d).0;
    (d, v, s)
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
