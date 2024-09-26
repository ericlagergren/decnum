use super::idiv::Divisor32;

super::impl_basic!(u32, u16, 7);

#[no_mangle]
pub const fn shr32(x: u32, n: u32) -> (u32, u32) {
    unsafe { crate::util::assume(n <= 7) }
    shr(x, n)
}

const fn umulh(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u64).unchecked_mul(rhs as u64) };
    (wide >> 32) as u32
}

const fn widening_mul(lhs: u32, rhs: u32) -> (u32, u32) {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u64).unchecked_mul(rhs as u64) };
    (wide as u32, (wide >> 32) as u32)
}

const RECIP10: [(u32, u32, u32); NUM_POW10] = [
    (0, 0, 0),           // 10^0
    (0, 3, 3435973837),  // 10^1
    (0, 5, 1374389535),  // 10^2
    (0, 6, 274877907),   // 10^3
    (0, 13, 3518437209), // 10^4
    (5, 7, 175921861),   // 10^5
    (0, 18, 1125899907), // 10^6
    (0, 22, 1801439851), // 10^7
    (0, 25, 1441151881), // 10^8
    (9, 7, 281475),      // 10^9
];

const RECIP10_2: [Divisor32; NUM_POW10] = {
    let mut table = [Divisor32::uninit(); NUM_POW10];
    let mut i = 0;
    while i < table.len() {
        table[i] = Divisor32::new(pow10(i as u32));
        i += 1;
    }
    table
};
