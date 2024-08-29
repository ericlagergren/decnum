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
pub(crate) const unsafe fn assume(b: bool) {
    debug_assert!(b);

    if !b {
        // SAFETY: See the function's safety docs.
        unsafe { hint::unreachable_unchecked() }
    }
}

/// Asserts that every byte in `s` is an ASCII digit.
#[track_caller]
pub(crate) const fn debug_assert_all_digits(s: &[u8]) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut i = 0;
    while i < s.len() {
        debug_assert!(matches!(s[i], b'0'..=b'9'));
        i += 1;
    }
}

/// See [`MaybeUninit::copy_from_slice`].
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

/// Transmutes `&mut [T; N]` to `&mut [T; M]`.
///
/// NB: This function is safe because `M <= N`.
pub(crate) fn sub_array<T, const N: usize, const M: usize>(src: &mut [T; N]) -> &mut [T; M] {
    const { assert!(M <= N) }
    // SAFETY: See the `const` block above, the references do not
    // outlive `src`, and the result is also an exclusive
    // reference.
    unsafe { &mut *(src.as_mut_ptr().cast::<[T; M]>()) }
}

/// Transmutes `&mut [T; N]` to `&mut [T; M]`.
///
/// NB: This function is safe because `M <= N`.
pub(crate) fn sub_array_at<T, const N: usize, const M: usize, const I: usize>(
    src: &mut [T; N],
) -> &mut [T; M] {
    const {
        assert!(M <= N);
        assert!(I <= M);
        assert!(N <= M - I);
    }
    // SAFETY: See the `const` block above, the references do not
    // outlive `src`, and the result is also an exclusive
    // reference.
    unsafe { &mut *(src.as_mut_ptr().add(I).cast::<[T; M]>()) }
}

pub(crate) fn split_array_mut<T, const N: usize, const L: usize, const R: usize>(
    src: &mut [T; N],
) -> (&mut [T; L], &mut [T; R]) {
    const {
        assert!(L <= N);
        assert!(R <= N);
        assert!(L + R <= N);
        assert!(usize::MAX - L >= N);
        assert!(usize::MAX - R >= N);
    }
    let lhs = unsafe { &mut *(src.as_mut_ptr().cast::<[T; L]>()) };
    let rhs = unsafe { &mut *(src.as_mut_ptr().add(L).cast::<[T; R]>()) };
    (lhs, rhs)
}
