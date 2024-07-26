use core::hint;

/// Hints to the compiler that `b` is always true.
///
/// # Safety
///
/// `b` must never be false.
pub(super) const unsafe fn assume(b: bool) {
    debug_assert!(b);

    if !b {
        // SAFETY: See the function's safety docs.
        unsafe { hint::unreachable_unchecked() }
    }
}

/// Converts `n` to a base-10 string.
///
/// `n` must be in [0,9999].
pub(super) fn itoa4(n: u16) -> u32 {
    println!("n={n}");
    debug_assert!(n < 10_000);

    const MASK: u32 = 0x30303030;

    let mut n = n as u32;
    let mut v = 0;
    let mut i = 0;
    while i < 4 {
        v |= (n % 10) << (24 - (i * 8));
        n /= 10;
        i += 1;
    }

    // Figure out how much we have to shift to get rid of
    // insignificant zeros. In other words, if v==0 then we shift
    // by 24, not 32.
    let ntz = (v.trailing_zeros() / 8) * 8;
    let mut s = ntz;
    s |= (ntz & 32) >> 1;
    s |= (ntz & 32) >> 2;
    s &= 31;

    v |= MASK;
    v >>= s;
    v
}

pub(super) const fn str_len(w: u32) -> usize {
    (((32 - w.leading_zeros()) + 7) / 8) as usize
}

#[cfg(test)]
mod tests {
    use core::str;

    use super::*;

    #[test]
    fn test_itoa4() {
        let mut buf = itoa::Buffer::new();
        for n in 0..=9999 {
            let w = itoa4(n);
            let i = ((32 - w.leading_zeros()) + 7) / 8;
            let got = w.to_le_bytes();
            let got = str::from_utf8(&got[..i as usize]).unwrap();
            let want = buf.format(n);
            assert_eq!(got, want, "#{n}");
        }
    }
}
