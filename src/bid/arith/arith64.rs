use super::idiv::{div2x1, Divisor64};

super::impl_basic!(u64, u32);

const fn quorem(u: u64, d: Divisor64) -> (u64, u64) {
    let Divisor64 { d, v, s } = d;
    div2x1(0, u, d, v, s)
}

#[allow(dead_code)]
const fn wide_quorem(u1: u64, u0: u64, d: Divisor64) -> (u128, u128) {
    let Divisor64 { d, v, s } = d;
    let (q1, r) = div2x1(0, u1, d, v, s);
    let (q0, r) = div2x1(r, u0, d, v, s);
    let q = ((q1 as u128) << 64) | (q0 as u128);
    (q, r as u128)
}

const fn umulh(lhs: u64, rhs: u64) -> u64 {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u128).unchecked_mul(rhs as u128) };
    (wide >> 64) as u64
}

const fn widening_mul(lhs: u64, rhs: u64) -> (u64, u64) {
    // SAFETY: The product is contained in the larger type.
    let wide = unsafe { (lhs as u128).unchecked_mul(rhs as u128) };
    (wide as u64, (wide >> 64) as u64)
}

const RECIP10: [(u32, u32, u64); NUM_POW10] = [
    (0, 0, 0),                     // 10^0
    (0, 3, 14757395258967641293),  // 10^1
    (2, 2, 2951479051793528259),   // 10^2
    (3, 4, 2361183241434822607),   // 10^3
    (0, 11, 3777893186295716171),  // 10^4
    (5, 7, 755578637259143235),    // 10^5
    (0, 18, 4835703278458516699),  // 10^6
    (0, 23, 15474250491067253437), // 10^7
    (0, 26, 12379400392853802749), // 10^8
    (9, 11, 19342813113834067),    // 10^9
    (0, 33, 15845632502852867519), // 10^10
    (0, 36, 12676506002282294015), // 10^11
    (0, 37, 2535301200456458803),  // 10^12
    (0, 41, 4056481920730334085),  // 10^13
    (0, 42, 811296384146066817),   // 10^14
    (15, 20, 633825300114115),     // 10^15
    (0, 51, 4153837486827862103),  // 10^16
    (17, 22, 101412048018259),     // 10^17
    (18, 24, 81129638414607),      // 10^18
    (0, 62, 8507059173023461587),  // 10^19
];

const RECIP10_IMPROVED: [Divisor64; NUM_POW10] = {
    let mut table = [Divisor64::uninit(); NUM_POW10];
    let mut i = 0;
    while i < table.len() {
        table[i] = Divisor64::new(pow10(i as u32));
        i += 1;
    }
    table
};
