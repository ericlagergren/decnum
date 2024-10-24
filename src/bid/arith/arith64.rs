use super::idiv::{self, div2x1};
use crate::util::assume;

super::impl_basic!(u64);

pub(super) const fn quorem_pow10(u: u64, n: u32) -> (u64, u64) {
    debug_assert!(n > 0);
    debug_assert!(n < NUM_POW10 as u32);

    let d = pow10(n);

    // Amazingly, Apple Silicon's integer division units are
    // better than reciprocals for word-sized operands.
    if cfg!(all(target_vendor = "apple", target_arch = "aarch64")) {
        return (u / d, u % d);
    }

    // Implement division via recpirocal via "Division by
    // Invariant Integers using Multiplication" by T.
    // Granlund and P. Montgomery.
    //
    // https://gmplib.org/~tege/divcnst-pldi94.pdf
    let q = {
        const RECIP10: [(u32, u32, u64); NUM_POW10] = [
            (0, 0, 0),                     // 10^0
            (0, 3, 14757395258967641293),  // 10^1
            (2, 2, 2951479051793528259),   // 10^2
            (3, 4, 2361183241434822607),   // 10^3
            (0, 11, 3777893186295716171),  // 10^4
            (5, 7, 755578637259143235),    // 10^5
            (0, 18, 4835703278458516699),  // 10^6
            (0, 23, 15474250491067253437), // 10^7
            (0, 26, 12379400392853802749), // 10^8
            (9, 11, 19342813113834067),    // 10^9
            (0, 33, 15845632502852867519), // 10^10
            (0, 36, 12676506002282294015), // 10^11
            (0, 37, 2535301200456458803),  // 10^12
            (0, 41, 4056481920730334085),  // 10^13
            (0, 42, 811296384146066817),   // 10^14
            (15, 20, 633825300114115),     // 10^15
            (0, 51, 4153837486827862103),  // 10^16
            (17, 22, 101412048018259),     // 10^17
            (18, 24, 81129638414607),      // 10^18
            (0, 62, 8507059173023461587),  // 10^19
        ];

        #[allow(
            clippy::indexing_slicing,
            reason = "Calling code always checks that `n` is in range"
        )]
        let (pre, post, m) = RECIP10[n as usize];
        umulh(m, u >> pre) >> post
    };

    // Assert invariants to help the compiler.
    // SAFETY: `q = u / (10^n)`.
    unsafe { assume(q <= u) }

    let r = u - q * d;

    // Assert some invariants to help the compiler.
    // SAFETY: `r = u % (10^n)`.
    unsafe {
        // NB: `r < d` must come first, otherwise the compiler
        // doesn't always use it.
        assume(r < d);
        assume(r == (u % d));
    }

    (q, r)
}

pub(super) const fn wide_quorem_pow10(u1: u64, u0: u64, n: u32) -> (u64, u64) {
    const RECIP10: [Divisor; NUM_POW10] = {
        let mut table = [Divisor::uninit(); NUM_POW10];
        let mut i = 0;
        while i < table.len() {
            table[i] = Divisor::new(pow10(i as u32));
            i += 1;
        }
        table
    };

    #[allow(
        clippy::indexing_slicing,
        reason = "Calling code always checks that `n` is in range"
    )]
    let Divisor { d, v, s } = RECIP10[n as usize];
    div2x1(u1, u0, d, v, s)
}

#[derive(Copy, Clone, Debug)]
struct Divisor {
    d: u64, // divisor
    v: u64, // reciprocal
    s: u32, // shift
}

impl Divisor {
    const fn uninit() -> Self {
        Self { d: 0, v: 0, s: 0 }
    }

    const fn new(d: u64) -> Self {
        let (d, v, s) = idiv::recip2x1(d);
        Self { d, v, s }
    }
}

const fn umulh(lhs: u64, rhs: u64) -> u64 {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u128).unchecked_mul(rhs as u128) };
    (wide >> 64) as u64
}

const fn widening_mul(lhs: u64, rhs: u64) -> (u64, u64) {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u128).unchecked_mul(rhs as u128) };
    (wide as u64, (wide >> 64) as u64)
}
