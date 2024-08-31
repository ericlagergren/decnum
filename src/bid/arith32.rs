/// Returns the number of decimal digits in `x`.
///
/// The result will be in [0, 10].
pub(super) const fn digits(x: u32) -> u32 {
    const TABLE: [u64; 32] = {
        let mut table = [0u64; 32];
        let mut i = 0;
        while i < table.len() {
            let smallest = if i == 0 { 0 } else { (1u64 << i).ilog10() + 1 };
            let mut x = if i < 30 {
                (1u64 << 32) - 10u64.pow(smallest)
            } else {
                0
            };
            x += (smallest as u64) << 32;
            table[i] = x;
            i += 1;
        }
        table[0] += 1; // shrug
        table
    };
    // #[rustfmt::skip]
    // const TABLE: [u64;32] = [
    //   4294967296,  8589934582,  8589934582,  8589934582,  12884901788,
    //   12884901788, 12884901788, 17179868184, 17179868184, 17179868184,
    //   21474826480, 21474826480, 21474826480, 21474826480, 25769703776,
    //   25769703776, 25769703776, 30063771072, 30063771072, 30063771072,
    //   34349738368, 34349738368, 34349738368, 34349738368, 38554705664,
    //   38554705664, 38554705664, 41949672960, 41949672960, 41949672960,
    //   42949672960, 42949672960
    // ];
    const fn bitlen(x: u32) -> u32 {
        31 - x.leading_zeros()
    }
    (((x as u64) + TABLE[bitlen(x | 1) as usize]) >> 32) as u32
}

/// Returns the minimum number of bits required to represent `x`.
///
/// It returns 0 for `x == 0`.
pub(super) const fn bitlen(x: u32) -> u32 {
    31 - x.leading_zeros()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_digits() {
        for x in 0..=u32::MAX {
            let got = digits(x);
            let want = super::super::arith64::digits(x as u64);
            assert_eq!(got, want, "#{x}");
        }
    }
}
