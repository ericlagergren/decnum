use super::idiv::{self, div2x1, div3x2, div4x2};

super::impl_basic!(u128, u256);

/// Like [`digits`], but for a double-width word.
#[no_mangle]
pub fn digits2(mut x1: u128, mut x0: u128) -> u32 {
    // Ensure that `x` is non-zero so that `digits(0) == 1`.
    //
    // This cannot cause an incorrect result because:
    //
    // - `x0|1` sets the lowest bit, so it cannot increase the
    //   bit length for a non-zero `x`.
    // - `x >= p` remains correct because the largest integer
    //   less than `p` is 999...999, which is odd, meaning `x0|1`
    //   is a no-op.
    x0 |= 1;

    const MAX: u32 = (NUM_POW10 - 1) as u32;

    let bits = if x1 != 0 {
        u128::BITS + bitlen(x1)
    } else {
        bitlen(x0)
    };
    // r is in [0, 78]
    let r = ((bits + 1) * 1233) / 4096;
    let mut n = r;
    if n >= MAX * 2 {
        crate::debug!("(1) n = {n} ({x1}, {x0})");
        const Y0: u128 = 0xba477cdae68ef33ba09aa98000000000;
        const Y1: u128 = 0xdd15fe86affad91249ef0eb713f39ebb;
        (x1, x0) = sub2x2(x1, x0, Y1, Y0);
        debug_assert!(x1 == 0);
        n -= MAX;
    }
    if n > MAX {
        crate::debug!("(2) n = {n} ({x1}, {x0})");
        (x1, x0) = sub2x1(x1, x0, 99999999999999999990000000000000000000);
        n -= MAX;
    }
    crate::debug!("(3) n = {n} ({x1}, {x0}) {}", pow10(n));
    let gt = x1 != 0 || x0 >= pow10(n);
    r + gt as u32
}

fn sub2x1(mut x1: u128, x0: u128, y: u128) -> (u128, u128) {
    let (x0, b) = x0.overflowing_sub(y);
    x1 -= b as u128;
    (x1, x0)
}

fn sub2x2(mut x1: u128, x0: u128, y1: u128, y0: u128) -> (u128, u128) {
    println!("x = ({x1}, {x0})");
    println!("y = ({y1}, {y0})");
    let (x0, b) = x0.overflowing_sub(y0);
    x1 -= y1;
    x1 -= b as u128;
    (x1, x0)
}

const fn quorem_pow10(u: u128, n: u32) -> (u128, u128) {
    debug_assert!(n > 0);
    debug_assert!(n < NUM_POW10 as u32);

    const RECIP10: [Divisor; NUM_POW10] = {
        let mut table = [Divisor::uninit(); NUM_POW10];
        let mut i = 0;
        while i < table.len() {
            table[i] = Divisor::new(pow10(i as u32));
            i += 1;
        }
        table
    };

    // Implement division via recpirocal via "Improved
    // division by invariant integers" by N. Möller
    // and T. Granlund.
    //
    // https://gmplib.org/~tege/division-paper.pdf
    #[allow(
        clippy::indexing_slicing,
        reason = "Calling code always checks that `n` is in range"
    )]
    let Divisor { d, v, s } = RECIP10[n as usize];

    let u1 = (u >> 64) as u64;
    let u0 = u as u64;

    let d1 = (d >> 64) as u64;
    let d0 = d as u64;
    if d1 == 0 {
        let (q1, r) = div2x1(0, u1, d0, v, s);
        let (q0, r) = div2x1(r, u0, d0, v, s);
        let q = ((q1 as u128) << 64) | (q0 as u128);
        (q, r as u128)
    } else {
        let (q, r) = div3x2(0, u1, u0, d1, d0, v, s);
        (q as u128, r)
    }
}

#[derive(Copy, Clone, Debug)]
struct Divisor {
    d: u128, // divisor
    v: u64,  // reciprocal
    s: u32,  // shift
}

impl Divisor {
    const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    const fn new(d: u128) -> Self {
        let d1 = (d >> 64) as u64;
        let d0 = d as u64;
        let (d, v, s) = if d1 == 0 {
            let (d, v, s) = idiv::recip2x1(d0);
            (d as u128, v, s)
        } else {
            idiv::recip3x2(d)
        };
        Self { d, v, s }
    }
}

const fn wide_quorem_pow10(u1: u128, u0: u128, n: u32) -> (u128, u128) {
    const RECIP10: [WideDivisor; NUM_POW10] = {
        let mut table = [WideDivisor::uninit(); NUM_POW10];
        let mut i = 0;
        while i < table.len() {
            table[i] = WideDivisor::new(pow10(i as u32));
            i += 1;
        }
        table
    };

    // Implement division via recpirocal via "Improved
    // division by invariant integers" by N. Möller
    // and T. Granlund.
    //
    // https://gmplib.org/~tege/division-paper.pdf
    #[allow(
        clippy::indexing_slicing,
        reason = "Calling code always checks that `n` is in range"
    )]
    let WideDivisor { d, v, s } = RECIP10[n as usize];

    let d1 = (d >> 64) as u64;
    let d0 = d as u64;
    if d1 == 0 {
        let u3 = (u1 >> 64) as u64;
        let u2 = u1 as u64;
        let u1 = (u0 >> 64) as u64;
        let u0 = u0 as u64;

        let v = v as u64;

        let (q3, r) = div2x1(0, u3, d0, v, s);
        let (q2, r) = div2x1(r, u2, d0, v, s);
        let (q1, r) = div2x1(r, u1, d0, v, s);
        let (q0, r) = div2x1(r, u0, d0, v, s);

        debug_assert!(q3 == 0);
        debug_assert!(q2 == 0);

        let q = ((q1 as u128) << 64) | (q0 as u128);
        (q, r as u128)
    } else {
        div4x2(u1, u0, d, v as u128, s)
    }
}

#[derive(Copy, Clone, Debug)]
struct WideDivisor {
    d: u128, // divisor
    v: u128, // reciprocal
    s: u32,  // shift
}

impl WideDivisor {
    const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    const fn new(d: u128) -> Self {
        let d1 = (d >> 64) as u64;
        let d0 = d as u64;
        let (d, v, s) = if d1 == 0 {
            let (d, v, s) = idiv::recip2x1(d0);
            (d as u128, v as u128, s)
        } else {
            idiv::recip4x2(d)
        };
        Self { d, v, s }
    }
}

// Returns `(lo, hi)`
pub(super) const fn widening_mul(x: u128, y: u128) -> (u128, u128) {
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
    (lo, hi)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bid::arith::u256;

    super::super::impl_tests!(u128, u256);

    #[test]
    fn test_digits2() {
        let mut x = u256::new(1);
        let mut want = 1;
        loop {
            let got = digits2(x.hi, x.lo);
            assert_eq!(got, want, "#{x:?}");
            x = x.const_mul64(10);
            want += 1;
            println!();
        }
    }
}
