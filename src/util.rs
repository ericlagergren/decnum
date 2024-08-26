use core::{hint, mem::MaybeUninit};

macro_rules! const_assert {
    ($($tt:tt)*) => {
        const _: () = ::core::assert!($($tt)*);
    }
}
pub(crate) use const_assert;

/// Hints to the compiler that `b` is always true.
///
/// # Safety
///
/// `b` must never be false.
#[track_caller]
pub(super) const unsafe fn assume(b: bool) {
    debug_assert!(b);

    if !b {
        // SAFETY: See the function's safety docs.
        unsafe { hint::unreachable_unchecked() }
    }
}

/// Asserts that every byte in `s` is an ASCII digit.
#[track_caller]
pub(super) const fn debug_assert_all_digits(s: &[u8]) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut i = 0;
    while i < s.len() {
        debug_assert!(matches!(s[i], b'0'..=b'9'));
        i += 1;
    }
}

/// A string of length [1,4].
#[derive(Copy, Clone, Debug)]
pub(super) struct Str4(u32);

impl Str4 {
    /// Returns the number of significant digits.
    pub const fn digits(self) -> usize {
        (((32 - self.0.leading_zeros()) + 7) / 8) as usize
    }

    /// Converts the string to bytes.
    ///
    /// Only [`len`][Self::len] bytes are valid.
    pub const fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}

/// Converts the binary number `n` to a base-10 string.
///
/// `n` must be in [1,9999].
pub(super) const fn itoa4(n: u16) -> Str4 {
    debug_assert!(n > 0 && n < 10_000);

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
    Str4(v)
}

/// See [`MaybeUninit::copy_from_slice`].
pub(super) fn copy_from_slice(dst: &mut [MaybeUninit<u8>], src: &[u8]) {
    // SAFETY: &[T] and &[MaybeUninit<T>] have the same layout
    let uninit_src: &[MaybeUninit<u8>] =
        unsafe { &*(src as *const [u8] as *const [MaybeUninit<u8>]) };
    dst.copy_from_slice(uninit_src);
}

/// See [`MaybeUninit::slice_assume_init_ref`].
pub(super) const unsafe fn slice_assume_init_ref(slice: &[MaybeUninit<u8>]) -> &[u8] {
    // SAFETY: casting `slice` to a `*const [T]` is safe since
    // the caller guarantees that `slice` is initialized, and
    // `MaybeUninit` is guaranteed to have the same layout as
    // `T`. The pointer obtained is valid since it refers to
    // memory owned by `slice` which is a reference and thus
    // guaranteed to be valid for reads.
    unsafe { &*(slice as *const [MaybeUninit<u8>] as *const [u8]) }
}

#[inline(always)]
pub(super) fn copy(dst: &mut [MaybeUninit<u8>], src: &[u8]) -> usize {
    let n = src.len();
    // The caller must verify the length of `dst`
    #[allow(clippy::indexing_slicing)]
    copy_from_slice(&mut dst[..n], src);
    n
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
            let i = ((32 - w.0.leading_zeros()) + 7) / 8;
            let got = w.to_bytes();
            let got = str::from_utf8(&got[..i as usize]).unwrap();
            let want = buf.format(n);
            assert_eq!(got, want, "#{n}");
        }
    }
}
