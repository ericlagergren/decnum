use core::cmp::Ordering;

use super::uint256::u256;
use crate::util::assume;

/// Shift `x` to the left by `n` digits.
pub(super) const fn shl(x: u128, n: u32) -> u256 {
    debug_assert!(n <= 34);

    widening_mul(x, 10u128.pow(n))
}

/// Shift `x` to the right by `n` digits.
pub(super) const fn shr(mut x: u128, n: u32) -> u128 {
    debug_assert!(n <= 34);

    let mut i = 0;
    while i < n / 3 {
        x = quorem1e3(x).0;
        i += 1;
    }
    if n % 3 > 0 {
        x /= 10u128.pow(n % 3);
    }
    x
}

/// Compares `lhs` and `rhs`.
pub(super) const fn const_cmp(lhs: u128, rhs: u128) -> Ordering {
    match lhs.checked_sub(rhs) {
        Some(0) => Ordering::Equal,
        Some(_) => Ordering::Greater,
        None => Ordering::Less,
    }
}

/// Reports whether `(lhs * 10^shift) == rhs`.
pub(super) const fn const_cmp_shifted(lhs: u128, rhs: u128, shift: u32) -> Ordering {
    shl(lhs, shift).const_cmp128(rhs as u128)
}

/// Reports whether `(lhs * 10^shift) == rhs`.
pub(super) const fn const_eq_shifted(lhs: u128, rhs: u128, shift: u32) -> bool {
    shl(lhs, shift).const_eq128(rhs)
}

/// Returns the number of decimal digits in `x`.
///
/// The result will be in [0, 39].
pub(super) const fn digits(mut x: u128) -> u32 {
    // Ensure that `x` is non-zero so that `digits(0) == 1`.
    //
    // This cannot cause an incorrect result because:
    //
    // - `x|1` sets the lowest bit, so it cannot increase the bit
    // length for a non-zero `x`.
    // - `x >= p` remains correct because the largest integer
    // less than `p` is 999...999, which is odd, meaning `x|1` is
    // a no-op.
    x |= 1;

    let r = ((bitlen(x) + 1) * 1233) / 4096;
    let p = POW10[r as usize];
    r + (x >= p) as u32
}

/// Returns the minimum number of bits required to represent `x`.
///
/// It returns 0 for `x == 0`.
pub(super) const fn bitlen(x: u128) -> u32 {
    u128::BITS - x.leading_zeros()
}

/// All 128-bit powers of 10.
const POW10: [u128; 39] = {
    let mut tab = [0u128; 39];
    let mut i = 0;
    while i < tab.len() {
        tab[i] = 10u128.pow(i as u32);
        i += 1;
    }
    tab
};

/// Returns (q, r) such that
///
/// ```text
/// q = n / 1000
/// r = n % 1000
/// ```
const fn quorem1e3(n: u128) -> (u128, u16) {
    #![allow(non_upper_case_globals)]

    const d: u128 = 1000;

    let q = {
        // Implement division via recpirocal via "Division by
        // Invariant Integers using Multiplication" by T.
        // Granlund and P. Montgomery.
        //
        // https://gmplib.org/~tege/divcnst-pldi94.pdf

        // l = ceil( log2(d) )
        //   = ceil( 9.965... )
        //   = 10
        // m' = floor( 2^N * (2^l - d)/d ) + 1
        //    = floor( (2^128) * (2^10 - 1000)/1000 ) + 1
        //    = floor( (2^128) * 3/125 ) + 1
        const REC: u128 = 8166776806102523123120990578362437075;

        // t1 = muluh(m', n)
        let t1 = muluh(REC, n);

        // sh1 = min(l, 1)
        // sh2 = max(l-1, 0)
        //
        // Since d > 1, l >= 1, therefore sh1 = 1 and sh2 = l-1.
        //
        // q = SRL(t1 + SRL(n−t1, 1), l−1)
        // q = SRL(t1 + SRL(n−t1, 1), 10-1)
        //   = SRL(t1 + SRL(n−t1, 1), 9)
        (t1 + ((n - t1) >> 1)) >> 9
    };
    // Assert some invariants to help the compiler.
    // SAFETY: `q = n/1000`.
    unsafe {
        assume(q <= n);
        assume(q == n / d);
        assume(q * d <= n);
    }

    let r = n - q * d;

    // Assert some invariants to help the compiler.
    // SAFETY: `r = n % 1000`.
    unsafe {
        // NB: `r < d` must come first, otherwise the compiler
        // doesn't use it in `from_u113`.
        assume(r < d);
        assume(r == (n % d));
    }

    (q, r as u16)
}

const fn muluh(x: u128, y: u128) -> u128 {
    const MASK: u128 = (1 << 64) - 1;
    let x0 = x & MASK;
    let x1 = x >> 64;
    let y0 = y & MASK;
    let y1 = y >> 64;
    let w0 = x0 * y0;
    let t = x1 * y0 + (w0 >> 64);
    let w1 = (t & MASK) + x0 * y1;
    let w2 = t >> 64;
    x1 * y1 + w2 + (w1 >> 64)
}

const fn widening_mul(x: u128, y: u128) -> u256 {
    const MASK: u128 = (1 << 64) - 1;
    let x0 = x & MASK;
    let x1 = x >> 64;
    let y0 = y & MASK;
    let y1 = y >> 64;
    let w0 = x0 * y0;
    let t = x1 * y0 + (w0 >> 64);
    let w1 = (t & MASK) + x0 * y1;
    let w2 = t >> 64;
    let hi = x1 * y1 + w2 + (w1 >> 64);
    let lo = x.wrapping_mul(y);
    u256::from_parts(hi, lo)
}

#[cfg(test)]
mod tests {
    use super::*;

    impl PartialEq<u128> for u256 {
        fn eq(&self, other: &u128) -> bool {
            self.const_eq128(*other)
        }
    }
    impl PartialEq<u256> for u128 {
        fn eq(&self, other: &u256) -> bool {
            other.const_eq128(*self)
        }
    }

    #[test]
    fn test_shl() {
        for n in 0..=34u32 {
            let x = 1;
            let got = shl(x, n);
            let want = x * 10u128.pow(n);
            assert_eq!(got, want, "{n}");
        }
    }

    #[test]
    fn test_shr() {
        for n in 0..=34u32 {
            let x = 10u128.pow(34) - 1;
            let got = shr(x, n);
            let want = x / 10u128.pow(n);
            assert_eq!(got, want, "{n}");
        }
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn test_digits() {
        let mut buf = itoa::Buffer::new();
        for x in 0..u32::MAX {
            let got = digits(x as u128);
            let want = buf.format(x).len() as u32;
            assert_eq!(got, want, "{x}");
        }
    }
}
