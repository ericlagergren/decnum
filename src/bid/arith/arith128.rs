use super::idiv::Divisor128;

super::impl_basic!(u128, u64, 34);

#[no_mangle]
pub const fn shr128(x: u128, n: u32) -> (u128, u128) {
    unsafe { crate::util::assume(n <= 34) }
    // if n == 0 {
    //     return (x, 0);
    // }
    // let d = RECIP10_2[n as usize];
    // Divisor128::quorem2(x, d)
    shr(x, n)
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

const RECIP10_2: [Divisor128; NUM_POW10] = {
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
}
