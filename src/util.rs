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
