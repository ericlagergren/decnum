use core::cmp::Ordering;

/// Shift `x` to the left by `n` digits.
pub(super) const fn shl(x: u64, n: u32) -> u128 {
    debug_assert!(n <= 16);

    x as u128 * 10u64.pow(n) as u128
}

/// Shift `x` to the right by `n` digits.
pub(super) const fn shr(mut x: u64, n: u32) -> u64 {
    debug_assert!(n <= 16);

    let mut i = 0;
    while i < n / 3 {
        x /= 1000;
        i += 1;
    }
    if n % 3 > 0 {
        x /= 10u64.pow(n % 3);
    }
    x
}

/// Compares `lhs` and `rhs`.
pub(super) const fn const_cmp(lhs: u64, rhs: u64) -> Ordering {
    match lhs.checked_sub(rhs) {
        Some(0) => Ordering::Equal,
        Some(_) => Ordering::Greater,
        None => Ordering::Less,
    }
}

/// Reports whether `(lhs * 10^shift) == rhs`.
pub(super) const fn const_cmp_shifted(lhs: u64, rhs: u64, shift: u32) -> Ordering {
    match shl(lhs, shift).checked_sub(rhs as u128) {
        Some(0) => Ordering::Equal,
        Some(_) => Ordering::Greater,
        None => Ordering::Less,
    }
}

/// Reports whether `(lhs * 10^shift) == rhs`.
pub(super) const fn const_eq_shifted(lhs: u64, rhs: u64, shift: u32) -> bool {
    shl(lhs, shift) == rhs as u128
}

/// Returns the number of decimal digits in `x`.
///
/// The result will be in [0, 39].
pub(super) const fn digits(mut x: u64) -> u32 {
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
pub(super) const fn bitlen(x: u64) -> u32 {
    u64::BITS - x.leading_zeros()
}

/// All 128-bit powers of 10.
const POW10: [u64; 20] = {
    let mut tab = [0u64; 20];
    let mut i = 0;
    while i < tab.len() {
        tab[i] = 10u64.pow(i as u32);
        i += 1;
    }
    tab
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shl() {
        for n in 0..=34u32 {
            let x = 1;
            let got = shl(x, n);
            let want = (x as u128) * 10u128.pow(n);
            assert_eq!(got, want, "{n}");
        }
    }

    #[test]
    fn test_shr() {
        for n in 0..=34u32 {
            let x = 10u64.pow(34) - 1;
            let got = shr(x, n);
            let want = x / 10u64.pow(n);
            assert_eq!(got, want, "{n}");
        }
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn test_digits() {
        let mut buf = itoa::Buffer::new();
        for x in 0..u32::MAX {
            let got = digits(x as u64);
            let want = buf.format(x).len() as u32;
            assert_eq!(got, want, "{x}");
        }
    }
}
