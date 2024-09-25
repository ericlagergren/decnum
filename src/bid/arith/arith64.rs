super::impl_basic!(u64, u32, 16);

const fn widening_mul(lhs: u64, rhs: u64) -> (u64, u64) {
    // SAFETY: The result is contained in the larger type.
    let wide = unsafe { (lhs as u128).unchecked_mul(rhs as u128) };
    (wide as u64, (wide >> 64) as u64)
}

const RECIP10: [(u32, u32, u64); NUM_POW10 + 1] = [
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
    (0, 66, 13611294676837538539), // 10^20
];

// TODO
const fn _div2_by_1_reciprocal(d: u64) -> u64 {
    const fn umul(x: u64, y: u64) -> (u64, u64) {
        // SAFETY: The result is contained in the larger
        // type.
        let wide = unsafe { (x as u128).unchecked_mul(y as u128) };
        let hi = (wide >> <u64>::BITS) as u64;
        let lo = wide as u64;
        (hi, lo)
    }

    let d = d << d.leading_zeros();
    let d0 = d & 1;
    let d9 = d >> 55;
    let d40 = (d >> 24) + 1;
    let d63 = (d >> 1) + d0;
    let v0 = ((1 << 19) - 3 * (1 << 8)) / d9;
    let v1 = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1;
    let v2 = (v1 << 13) + ((v1 * ((1 << 60) - v1 * d40)) >> 47);

    // Checks that the expression for `e` can be simplified in the way we did below.
    debug_assert!(umul(v2, d63).0 == (1 << 32) - 1);
    let e = <u64>::MAX - v2.wrapping_mul(d63) + 1 + (v2 >> 1) * d0;

    let hi = umul(v2, e).0;
    let v3 = (v2 << 31).wrapping_add(hi >> 1);

    // The paper has `(v3 + 1) * d / 2^64` (there's
    // another 2^64, but it's accounted for later).
    // If `v3 == 2^64-1` this should give `d`, but we
    // can't achieve this in our wrapping arithmetic.
    // Hence the `ct_select()`.
    let x = v3.wrapping_add(1);
    let hi = umul(x, d).0;
    let hi = if x != 0 { d } else { hi };

    v3.wrapping_sub(hi).wrapping_sub(d)
}
