use super::idiv::{div2x1, Divisor2x1};

super::impl_basic!(u32, u16);

type Divisor = Divisor2x1<u32, u64>;

const fn quorem(u: u32, d: Divisor) -> (u32, u32) {
    let Divisor { d, v, s } = d;
    let (q, r) = div2x1(0, u as u64, d as u64, v as u64, s);
    (q as u32, r as u32)
}

const fn wide_quorem(u1: u32, u0: u32, d: Divisor) -> (u32, u32) {
    let Divisor { d, v, s } = d;
    let u = ((u1 as u64) << 32) | (u0 as u64);
    let (q, r) = div2x1(0, u, d as u64, v as u64, s);
    (q as u32, r as u32)
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

const RECIP10_IMPROVED: [Divisor; NUM_POW10] = {
    let mut table = [Divisor::uninit(); NUM_POW10];
    let mut i = 0;
    while i < table.len() {
        table[i] = Divisor::new(pow10(i as u32));
        i += 1;
    }
    table
};
