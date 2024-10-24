super::impl_basic!(u32);

const fn quorem_pow10(u: u32, n: u32) -> (u32, u32) {
    let (q, r) = super::arith64::quorem_pow10(u as u64, n);
    (q as u32, r as u32)
}

const fn wide_quorem_pow10(u1: u32, u0: u32, n: u32) -> (u32, u32) {
    let u = ((u1 as u64) << 32) | (u0 as u64);
    let (q, r) = super::arith64::quorem_pow10(u, n);
    (q as u32, r as u32)
}

const fn widening_mul(lhs: u32, rhs: u32) -> (u32, u32) {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u64).unchecked_mul(rhs as u64) };
    (wide as u32, (wide >> 32) as u32)
}
