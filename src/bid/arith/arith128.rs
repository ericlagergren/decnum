use super::idiv::{div2x1, div3x2, div4x1, div4x2, Divisor2x1, Divisor3x2};

super::impl_basic!(u128, u64);

const fn quorem(u: u128, d: Divisor128) -> (u128, u128) {
    let Divisor128 { d, v, s } = d;

    let u1 = (u >> 64) as u64;
    let u0 = u as u64;

    let d1 = (d >> 64) as u64;
    let d0 = d as u64;
    if d1 == 0 {
        let (q1, r) = div2x1(0, u1, d0, v, s);
        let (q0, r) = div2x1(r, u0, d0, v, s);
        let q = ((q1 as u128) << 64) | (q0 as u128);
        (q, r as u128)
    } else {
        let (q, r) = div3x2(0, u1, u0, d1, d0, v, s);
        (q as u128, r)
    }
}

const fn wide_quorem(u1: u128, u0: u128, d: Divisor128) -> (u128, u128) {
    let Divisor128 { d, v, s } = d;

    let d1 = (d >> 64) as u64;
    let d0 = d as u64;
    if d1 == 0 {
        let u3 = (u1 >> 64) as u64;
        let u2 = u1 as u64;
        let u1 = (u0 >> 64) as u64;
        let u0 = u0 as u64;

        let (q3, r) = div2x1(0, u3, d0, v, s);
        let (q2, r) = div2x1(r, u2, d0, v, s);
        let (q1, r) = div2x1(r, u1, d0, v, s);
        let (q0, r) = div2x1(r, u0, d0, v, s);

        debug_assert!(q3 == 0);
        debug_assert!(q2 == 0);

        let q = ((q1 as u128) << 64) | (q0 as u128);
        (q, r as u128)
    } else {
        div4x2(u1, u0, d, v as u128, s)
    }
}

fn wide_quorem2(u1: u128, u0: u128, d: Divisor128) -> (u128, u128) {
    let Divisor128 { d, v, s } = d;

    let d1 = (d >> 64) as u64;
    let d0 = d as u64;
    println!("d1={d1} d0={d0}");
    if d1 == 0 {
        let u3 = (u1 >> 64) as u64;
        let u2 = u1 as u64;
        let u1 = (u0 >> 64) as u64;
        let u0 = u0 as u64;

        let (q3, r) = div2x1(0, u3, d0, v, s);
        let (q2, r) = div2x1(r, u2, d0, v, s);
        let (q1, r) = div2x1(r, u1, d0, v, s);
        let (q0, r) = div2x1(r, u0, d0, v, s);

        debug_assert!(q3 == 0);
        debug_assert!(q2 == 0);

        let q = ((q1 as u128) << 64) | (q0 as u128);
        (q, r as u128)
    } else {
        div4x2(u1, u0, d, v as u128, s)
    }
}

const fn umulh(x: u128, y: u128) -> u128 {
    widening_mul(x, y).1
}

// Returns `(lo, hi)`
const fn widening_mul(x: u128, y: u128) -> (u128, u128) {
    let x1 = (x >> 64) as u64;
    let x0 = x as u64;
    let y1 = (y >> 64) as u64;
    let y0 = y as u64;

    /// Returns `lhs * rhs + carry`.
    const fn carrying_mul(lhs: u64, rhs: u64, carry: u64) -> (u64, u64) {
        // SAFETY: The result is contained in the larger type.
        let wide = unsafe {
            (lhs as u128)
                .unchecked_mul(rhs as u128)
                .unchecked_add(carry as u128)
        };
        (wide as u64, (wide >> 64) as u64)
    }

    let (p1, p2) = carrying_mul(x0, y0, 0);
    let (p2, p31) = carrying_mul(x0, y1, p2);
    let (p2, p32) = carrying_mul(x1, y0, p2);
    let (p3, p4o) = p31.overflowing_add(p32);
    let (p3, p4) = carrying_mul(x1, y1, p3);
    let p4 = p4.wrapping_add(p4o as u64);

    let hi = p3 as u128 | (p4 as u128) << 64; // hi
    let lo = p1 as u128 | (p2 as u128) << 64; // lo
    (lo, hi)
}

const RECIP10: [(u32, u32, u128); NUM_POW10] = [
    (0, 0, 0),                                         // 10^0
    (0, 3, 272225893536750770770699685945414569165),   // 10^1
    (0, 4, 54445178707350154154139937189082913833),    // 10^2
    (3, 4, 43556142965880123323311949751266331067),    // 10^3
    (0, 13, 278759314981632789269196478408104518825),  // 10^4
    (0, 14, 55751862996326557853839295681620903765),   // 10^5
    (0, 15, 11150372599265311570767859136324180753),   // 10^6
    (0, 23, 285449538541191976211657193889899027277),  // 10^7
    (8, 11, 1784059615882449851322857461811868921),    // 10^8
    (0, 29, 182687704666362864775460604089535377457),  // 10^9
    (0, 31, 73075081866545145910184241635814150983),   // 10^10
    (0, 36, 233840261972944466912589573234605283145),  // 10^11
    (0, 37, 46768052394588893382517914646921056629),   // 10^12
    (0, 42, 149657767662684458824057326870147381213),  // 10^13
    (0, 46, 239452428260295134118491722992235809941),  // 10^14
    (15, 20, 11692013098647223345629478661730265),     // 10^15
    (0, 51, 76624777043294442917917351357515459181),   // 10^16
    (0, 56, 245199286538542217337335524344049469379),  // 10^17
    (18, 23, 748288838313422294120286634350737),       // 10^18
    (0, 62, 156927543384667019095894735580191660403),  // 10^19
    (20, 24, 59863107065073783529622930748059),        // 10^20
    (21, 28, 191561942608236107294793378393789),       // 10^21
    (0, 73, 321387608851798055108392418468232520505),  // 10^22
    (0, 74, 64277521770359611021678483693646504101),   // 10^23
    (0, 79, 205688069665150755269371147819668813123),  // 10^24
    (0, 83, 329100911464241208430993836511470100997),  // 10^25
    (0, 85, 131640364585696483372397534604588040399),  // 10^26
    (0, 88, 105312291668557186697918027683670432319),  // 10^27
    (0, 93, 336999333339382997433337688587745383421),  // 10^28
    (0, 96, 269599466671506397946670150870196306737),  // 10^29
    (30, 39, 200867255532373784442745261543),          // 10^30
    (31, 41, 160693804425899027554196209235),          // 10^31
    (32, 41, 32138760885179805510839241847),           // 10^32
    (0, 109, 220855883097298041197912187592864814479), // 10^33
    (0, 112, 176684706477838432958329750074291851583), // 10^34
    (0, 116, 282695530364541492733327600118866962533), // 10^35
    (0, 118, 113078212145816597093331040047546785013), // 10^36
    (0, 122, 180925139433306555349329664076074856021), // 10^37
    (0, 125, 144740111546645244279463731260859884817), // 10^38
];

const RECIP10_IMPROVED: [Divisor128; NUM_POW10] = {
    let mut table = [Divisor128::uninit(); NUM_POW10];
    let mut i = 0;
    while i < table.len() {
        table[i] = Divisor128::new(pow10(i as u32));
        i += 1;
    }
    table
};

#[cfg(test)]
mod tests2 {
    use super::*;

    #[test]
    fn test_idk() {
        const RND: u128 = ((27105 as u128) << 64) | (1001882102603448320 as u128);
        let mut x = 10u128.pow(34) - 1;
        x += RND;
        const REC: u128 = ((10889035741470030 as u128) << 64) | (15326071253540576846 as u128);
        println!("x = {x}");
        println!("rec = {REC}");
        let (lo, hi) = widening_mul(x, REC);
        println!("lo = {lo} ({}, {})", (lo >> 64) as u64, lo as u64);
        println!("hi = {hi} ({}, {})", (hi >> 64) as u64, hi as u64);

        let q = hi >> 69;
        println!("q = {q}");
        let r = (((((hi >> 64) as u64) << (128 - 69)) as u128) << 64) | ((hi as u64) as u128);
        println!("r = {r}");

        const IDK: u128 = ((8646911284551352320 as u128) << 64) | (18446744073709551615 as u128);
        println!("? = {IDK}");

        println!("q = {}", x / 10u128.pow(24));
        println!("r = {}", x % 10u128.pow(24));
    }

    #[test]
    fn test_wide_quorem() {
        const DIGITS: u32 = 34;
        const MAX: u128 = u128::pow(10, DIGITS) - 1;
        for s in 0..=DIGITS {
            let (u0, mut u1) = widening_mul(MAX, u128::pow(10, s));
            let (u0, carry) = u0.overflowing_add(MAX);
            if carry {
                u1 += 1;
            }
            let (u0, carry) = u0.overflowing_add(super::super::util::point5(s));
            if carry {
                u1 += 1;
            }
            let v = u128::pow(10, s);
            let d = Divisor128::new(v);
            let got = wide_quorem2(u1, u0, d);

            #[allow(non_camel_case_types)]
            type u256 = ruint::Uint<256, 4>;
            let u = u256::from_limbs([u0 as u64, (u0 >> 64) as u64, u1 as u64, (u1 >> 64) as u64]);
            let v = u256::from_limbs([v as u64, (v >> 64) as u64, 0, 0]);
            let want: (u128, u128) = (
                (u / v).try_into().unwrap(), // q
                (u % v).try_into().unwrap(), // r
            );
            assert_eq!(got, want, "#{s}: {u} / {v}");
        }
    }
}
