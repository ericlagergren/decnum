use super::idiv::{self, div2x1, div3x2, div4x2};

super::impl_basic!(u128);

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
const fn widening_mul(x: u128, y: u128) -> (u128, u128) {
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
