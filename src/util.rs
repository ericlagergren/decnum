use core::{hint, mem::MaybeUninit};

macro_rules! const_assert {
    (
        #[$meta:meta]
        $($tt:tt)*
    ) => {
        #[$meta]
        const _: () = ::core::assert!($($tt)*);
    };
    ($($tt:tt)*) => {
        const _: () = ::core::assert!($($tt)*);
    };
}
pub(crate) use const_assert;

/// Hints to the compiler that `b` is always true.
///
/// # Safety
///
/// `b` must never be false.
#[track_caller]
pub(crate) const unsafe fn assume(b: bool) {
    debug_assert!(b);

    if !b {
        // SAFETY: See the function's safety docs.
        unsafe { hint::unreachable_unchecked() }
    }
}

/// Asserts that every byte in `s` is an ASCII digit.
#[track_caller]
#[allow(clippy::indexing_slicing)] // debug code
pub(crate) const fn debug_assert_all_digits(s: &[u8]) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut i = 0;
    while i < s.len() {
        debug_assert!(s[i].is_ascii_digit());
        i += 1;
    }
}

/// See [`MaybeUninit::copy_from_slice`].
#[inline(always)]
pub(crate) fn copy_from_slice<'a>(dst: &'a mut [MaybeUninit<u8>], src: &'a [u8]) -> &'a mut [u8] {
    // SAFETY: &[T] and &[MaybeUninit<T>] have the same layout
    let uninit_src: &[MaybeUninit<u8>] =
        unsafe { &*(src as *const [u8] as *const [MaybeUninit<u8>]) };
    dst.copy_from_slice(uninit_src);
    // SAFETY: Valid elements have just been copied into `dst`,
    // so it is initialized
    unsafe { slice_assume_init_mut(dst) }
}

/// See [`MaybeUninit::slice_assume_init_ref`].
#[inline(always)]
pub(crate) const unsafe fn slice_assume_init_ref(slice: &[MaybeUninit<u8>]) -> &[u8] {
    // SAFETY: casting `slice` to a `*const [T]` is safe since
    // the caller guarantees that `slice` is initialized, and
    // `MaybeUninit` is guaranteed to have the same layout as
    // `T`. The pointer obtained is valid since it refers to
    // memory owned by `slice` which is a reference and thus
    // guaranteed to be valid for reads.
    unsafe { &*(slice as *const [MaybeUninit<u8>] as *const [u8]) }
}

/// See [`MaybeUninit::slice_assume_init_mut`].
#[inline(always)]
pub(crate) unsafe fn slice_assume_init_mut(slice: &mut [MaybeUninit<u8>]) -> &mut [u8] {
    // SAFETY: similar to safety notes for `slice_get_ref`, but
    // we have a mutable reference which is also guaranteed to be
    // valid for writes.
    unsafe { &mut *(slice as *mut [MaybeUninit<u8>] as *mut [u8]) }
}

#[inline(always)]
pub(crate) fn copy(dst: &mut [MaybeUninit<u8>], src: &[u8]) -> usize {
    let n = src.len();
    // The caller must verify the length of `dst`.
    #[allow(clippy::indexing_slicing)]
    copy_from_slice(&mut dst[..n], src);
    n
}
