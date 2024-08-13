//! Densely Packed Decimal conversion routines.

use core::hint;

use super::{
    bcd::{self, Pattern, Str3},
    tables::{BCD_TO_DPD, BIN_TO_DPD, DPD_TO_BCD, DPD_TO_STR},
    util::assume,
};

/// Reports whether the 10-bit DPD is valid.
pub const fn is_valid(dpd: u16) -> bool {
    if dpd > 1 << 10 {
        return false;
    }
    !matches!(
        dpd,
        0x16e
            | 0x16f
            | 0x17e
            | 0x17f
            | 0x1ee
            | 0x1ef
            | 0x1fe
            | 0x1ff
            | 0x26e
            | 0x26f
            | 0x27e
            | 0x27f
            | 0x2ee
            | 0x2ef
            | 0x2fe
            | 0x2ff
            | 0x36e
            | 0x36f
            | 0x37e
            | 0x37f
            | 0x3ee
            | 0x3ef
            | 0x3fe
            | 0x3ff,
    )
}

/// Classifies a 10-bit DPD for unpacking into a 12-bit BCD.
pub const fn classify(dpd: u16) -> Pattern {
    use Pattern::*;

    // Match bit `v`.
    if dpd & 0x8 == 0 {
        return AllSmall;
    }

    // Match bits `vwx`.
    match dpd & 0xe {
        0x8 => return RightLarge,
        0xa => return MiddleLarge,
        0xc => return LeftLarge,
        _ => {}
    }

    // Match bits `st`.
    match dpd & 0x60 {
        0x00 => RightSmall,
        0x20 => MiddleSmall,
        0x40 => LeftSmall,
        0x60 => AllLarge,
        // SAFETY: Given the bits we've set, these are the only
        // possible results.
        _ => unsafe { hint::unreachable_unchecked() },
    }
}

/// Packs a 12-bit BCD into a 10-bit DPD.
///
/// # Panics
///
/// This function might panic if `dpd-tables` is enabled and
/// `bcd` is greater than 0x999.
pub const fn pack(bcd: u16) -> u16 {
    if cfg!(feature = "dpd-tables") {
        #[allow(clippy::indexing_slicing)]
        BCD_TO_DPD[bcd as usize]
    } else {
        pack_via_bits(bcd)
    }
}

/// Pack a 12-bit BCD into a 10-bit DPD using bit twiddling.
pub(super) const fn pack_via_bits(mut bcd: u16) -> u16 {
    // BCDs only use the lower 12 bits.
    bcd &= 0x0fff;

    // Shift the low byte left by one, then shift the whole thing
    // right by one.
    //
    // 0000 abcd efgh ijkm
    // 0000 abcd fghi klm0
    // 0000 0abc dfgh iklm
    let mut dpd = ((bcd & 0xff00) | ((bcd << 1) & 0x00ff)) >> 1;

    if bcd & 0x880 == 0 {
        // 0000 0bcd 0fgh ijkm
        return dpd;
    }

    let (hi, lo) = {
        // Ideally, we'd use `pext` for x86. Rough benchmarks
        // show it to be maybe 1 ns/op faster. But `core::arch`
        // intrinsics are not `const` and LLVM currently does not
        // recognize bit extraction.
        // https://github.com/llvm/llvm-project/issues/72088
        let mut idx = if cfg!(target_arch = "aarch64") {
            // This is marginally faster since the compiler
            // rewrites it as
            //    lsr
            //    bfixl
            //    lsr
            //    and
            //    bfi
            let mut idx = 0;
            idx |= (bcd & 0x800) >> 8;
            idx |= (bcd & 0x80) >> 5;
            idx |= (bcd & 0x8) >> 2;
            idx
        } else {
            let mut idx = bcd;
            // 0000 a000 e000 i000
            idx &= 0x888;
            // 0ae0 aei0 ei00 i000
            idx = idx.wrapping_mul(0x49);
            // 0000 0000 0ae0 aei0
            idx >>= 8;
            // 0000 0000 0000 aei0
            idx &= 0xe;
            idx
        };
        idx /= 2;

        if cfg!(target_arch = "aarch64") {
            // Using two 64-bit constants is significantly faster
            // than one 128-bit constant.
            const LO: u64 = 0x0081088100110000;
            const HI: u64 = 0x6e0e2e0c4e0a0000;

            idx *= 8;
            let lo = (LO >> idx) & 0xff;
            let hi = (HI >> idx) & 0xff;
            (hi as u16, lo as u16)
        } else {
            const LOOKUP: [u16; 8] = [
                0x0000, 0x0000, 0x0a11, 0x4e00, 0x0c81, 0x2e08, 0x0e81, 0x6e00,
            ];
            // `idx` is in [0, 7], so the compiler elides the
            // bounds checks.
            let v = LOOKUP[idx as usize];
            (v >> 8, v & 0x00ff)
        }
    };

    // 0000 0000 0fg0 0kl0
    let v = (dpd & 0x66).wrapping_mul(lo);
    dpd &= 0x397;
    dpd ^= v;
    dpd = (dpd & 0xff00) | (hi | (dpd & 0x00ff));
    dpd &= 0x3ff;

    dpd
}

/// Pack a 12-bit BCD into a 10-bit DPD using bit twiddling.
pub(super) const fn pack_via_bits_obvious(mut bcd: u16) -> u16 {
    // (abcd)(efgh)(ijkm) becomes (pqr)(stu)(v)(wxy)

    // | aei | pqr stu v wxy   comments
    // | --- | ------------- | ----------------------|
    // | 000 | bcd fgh 0 jkm | All digits are small  |
    // | 001 | bcd fgh 1 00m | Right digit is large  |
    // | 010 | bcd jkh 1 01m | Middle digit is large |
    // | 100 | jkd fgh 1 10m | Left digit is large   |
    // | 110 | jkd 00h 1 11m | Right digit is small  |
    // | 101 | fgd 01h 1 11m | Middle digit is small |
    // | 011 | bcd 10h 1 11m | Left digit is small   |
    // | 111 | 00d 11h 1 11m | All digits are large  |

    // BCDs only use the lower 12 bits.
    bcd &= 0x0fff;

    use Pattern::*;
    match bcd::classify(bcd) {
        AllSmall => {
            // .... abcd efgh ijkm
            // .... ..bc dfgh 0jkm
            ((bcd & 0x700) >> 1) | (bcd & 0x77)
        }
        RightLarge => {
            // .... abcd efgh ijkm
            // .... ..bc dfgh 100m
            ((bcd & 0x700) >> 1) | 0x8 | (bcd & 0x71)
        }
        MiddleLarge => {
            // .... abcd efgh ijkm
            // .... ..bc djkh 101m
            ((bcd & 0x700) >> 1) | ((bcd & 0x6) << 4) | 0xa | (bcd & 0x11)
        }
        LeftLarge => {
            // .... abcd efgh ijkm
            // .... ..jk dfgh 110m
            ((bcd & 0x6) << 7) | ((bcd & 0x100) >> 1) | (bcd & 0x71) | 0xc
        }
        RightSmall => {
            // .... abcd efgh ijkm
            // .... ..jk d00h 111m
            ((bcd & 0x6) << 7) | ((bcd & 0x100) >> 1) | (bcd & 0x11) | 0xe
        }
        MiddleSmall => {
            // .... abcd efgh ijkm
            // .... ..fg d01h 111m
            ((bcd & 0x60) << 3) | ((bcd & 0x100) >> 1) | (bcd & 0x11) | 0x2e
        }
        LeftSmall => {
            // .... abcd efgh ijkm
            // .... ..bc d10h 111m
            ((bcd & 0x700) >> 1) | (bcd & 0x11) | 0x4e
        }
        AllLarge => {
            // .... abcd efgh ijkm
            // .... ..00 d11h 111m
            ((bcd & 0x100) >> 1) | (bcd & 0x11) | 0x6e
        }
    }
}

/// Unpacks a 10-bit DPD into a 12-bit BCD.
///
/// # Panics
///
/// This function might panic if `dpd-tables` is enabled and
/// `dpd` is greater than 1023.
pub const fn unpack(dpd: u16) -> u16 {
    if cfg!(feature = "dpd-tables") {
        #[allow(clippy::indexing_slicing)]
        DPD_TO_BCD[dpd as usize]
    } else {
        unpack_via_bits(dpd)
    }
}

/// Unpacks a 10-bit DPD into a 12-bit BCD using bit twiddling.
pub(super) const fn unpack_via_bits(mut dpd: u16) -> u16 {
    // (pqr)(stu)(v)(wxy) becomes (abcd)(efgh)(ijkm)

    // DPDs only use the lower 10 bits.
    dpd &= 0x3ff;

    // | vwxst | abcd efgh ikjm |
    // | ----- | -------------- |
    // | 0.... | 0pqr 0stu 0wxy |
    // | 100.. | 0pqr 0stu 100y |
    // | 101.. | 0pqr 100u 0sty |
    // | 110.. | 100r 0stu 0pqy |
    // | 11100 | 100r 100u 0pqy |
    // | 11101 | 100r 0pqu 100y |
    // | 11110 | 0pqr 100u 100y |
    // | 11111 | 100r 100u 100y |

    use Pattern::*;
    match classify(dpd) {
        AllSmall => {
            // .... ..pq rstu vwxy
            // .... 0pqr 0stu 0wxy
            ((dpd & 0x380) << 1) | (dpd & 0x077)
        }
        RightLarge => {
            // .... ..pq rstu vwxy
            // .... 0pqr 0stu 100y
            ((dpd & 0x380) << 1) | (dpd & 0x71) | 0x8
        }
        MiddleLarge => {
            // .... ..pq rstu vwxy
            // .... 0pqr 100u 0sty
            ((dpd & 0x380) << 1) | ((dpd & 0x60) >> 4) | 0x80 | (dpd & 0x11)
        }
        LeftLarge => {
            // .... ..pq rstu vwxy
            // .... 100r 0stu 0pqy
            ((dpd & 0x80) << 1) | (dpd & 0x71) | ((dpd & 0x300) >> 7) | 0x800
        }
        RightSmall => {
            // .... ..pq rstu vwxy
            // .... 100r 100u 0pqy
            ((dpd & 0x80) << 1) | ((dpd & 0x300) >> 7) | (dpd & 0x11) | 0x880
        }
        MiddleSmall => {
            // .... ..pq rstu vwxy
            // .... 100r 0pqu 100y
            ((dpd & 0x80) << 1) | ((dpd & 0x300) >> 3) | (dpd & 0x11) | 0x808
        }
        LeftSmall => {
            // .... ..pq rstu vwxy
            // .... 0pqr 100u 100y
            ((dpd & 0x380) << 1) | (dpd & 0x11) | 0x88
        }
        AllLarge => {
            // .... ..pq rstu vwxy
            // .... 100r 100u 100y
            ((dpd & 0x80) << 1) | (dpd & 0x11) | 0x888
        }
    }
}

impl Str3 {
    /// Unpacks the 10-bit DPD into a three-byte string.
    ///
    /// The high octet contains the number of significant digits
    /// in the DPD.
    ///
    /// # Panics
    ///
    /// This function might panic if `dpd-tables` is enabled and
    /// `dpd` is greater than 1023.
    pub const fn from_dpd(dpd: u16) -> Self {
        if cfg!(feature = "dpd-tables") {
            #[allow(clippy::indexing_slicing)]
            DPD_TO_STR[dpd as usize]
        } else {
            unpack_to_str_via_bits(dpd)
        }
    }

    /// Packs the three-byte string into a 10-bit DPD.
    pub const fn to_dpd(self) -> u16 {
        pack(self.to_bcd())
    }
}

pub(super) const fn unpack_to_str_via_bits(dpd: u16) -> Str3 {
    Str3::from_bcd(unpack(dpd))
}

/// Packs a 32-bit binary number into a 40-bit DPD.
///
/// The most significant 10 bits will always be in [0,4].
pub const fn pack_bin_u32(mut bin: u32) -> u64 {
    let mut dpd = 0;
    let mut i = 0;
    while i < 3 {
        let d = (bin % 1000) as u16;
        dpd |= (bin_to_dpd(d) as u64) << (i * 10);
        bin /= 1000;
        i += 1;
    }
    dpd |= (bin_to_dpd((bin % 10) as u16) as u64) << (i * 10);
    dpd
}

/// Packs a 113-bit binary number into a 120-bit DPD.
///
/// The most significant 10 bits will always be either `0` or
/// `9`.
///
/// `bin` must be in the range `[0, (10^34)-1]`
pub const fn pack_bin_u113(mut bin: u128) -> u128 {
    const MASK: u128 = !(((1 << 15) - 1) << 113);
    bin &= MASK;

    let mut dpd = 0;
    let mut i = 0;
    while i < 11 {
        let (q, r) = quorem1e3(bin);
        dpd |= (bin_to_dpd(r) as u128) << (i * 10);
        i += 1;
        bin = q;
    }
    dpd |= (bin_to_dpd((bin % 10) as u16) as u128) << (i * 10);
    dpd
}

/// Returns (q, r) such that
///
/// ```text
/// q = n / 1000
/// r = n % 1000
/// ```
const fn quorem1e3(n: u128) -> (u128, u16) {
    #![allow(non_upper_case_globals)]

    const d: u128 = 1000;

    let q = {
        // Implement division via recpirocal via "Division by
        // Invariant Integers using Multiplication" by T.
        // Granlund and P. Montgomery.
        //
        // https://gmplib.org/~tege/divcnst-pldi94.pdf

        // l = ceil( log2(d) )
        //   = ceil( 9.965... )
        //   = 10
        // m' = floor( 2^N * (2^l - d)/d ) + 1
        //    = floor( (2^128) * (2^10 - 1000)/1000 ) + 1
        //    = floor( (2^128) * 3/125 ) + 1
        const REC: u128 = 8166776806102523123120990578362437075;

        // t1 = muluh(m', n)
        let t1 = muluh(REC, n);

        // sh1 = min(l, 1)
        // sh2 = max(l-1, 0)
        //
        // Since d > 1, l >= 1, therefore sh1 = 1 and sh2 = l-1.
        //
        // q = SRL(t1 + SRL(n−t1, 1), l−1)
        // q = SRL(t1 + SRL(n−t1, 1), 10-1)
        //   = SRL(t1 + SRL(n−t1, 1), 9)
        (t1 + ((n - t1) >> 1)) >> 9
    };
    // Assert some invariants to help the compiler.
    // SAFETY: `q = n/1000`.
    unsafe {
        assume(q <= n);
        assume(q == n / d);
        assume(q * d <= n);
    }

    let r = n - q * d;

    // Assert some invariants to help the compiler.
    // SAFETY: `r = n % 1000`.
    unsafe {
        // NB: `r < d` must come first, otherwise the compiler
        // doesn't use it in `from_u113`.
        assume(r < d);
        assume(r == (n % d));
    }

    (q, r as u16)
}

const fn muluh(x: u128, y: u128) -> u128 {
    const MASK: u128 = (1 << 64) - 1;
    let x0 = x & MASK;
    let x1 = x >> 64;
    let y0 = y & MASK;
    let y1 = y >> 64;
    let w0 = x0 * y0;
    let t = x1 * y0 + (w0 >> 64);
    let w1 = (t & MASK) + x0 * y1;
    let w2 = t >> 64;
    x1 * y1 + w2 + (w1 >> 64)
}

/// Converts a binary number in [0,999] to a 10-bit DPD.
///
/// # Panics
///
/// This function might panic if `dpd-tables` is enabled and
/// `bin` is greater than 999.
const fn bin_to_dpd(bin: u16) -> u16 {
    if cfg!(feature = "dpd-tables") {
        #[allow(clippy::indexing_slicing)]
        BIN_TO_DPD[bin as usize]
    } else {
        pack(bcd::from_bin(bin))
    }
}

/// Returns the number of significant digits in the 10-bit DPD.
pub(super) const fn sig_digits(dpd: u16) -> u32 {
    let bcd = unpack(dpd);
    let nlz = bcd.leading_zeros();
    let mut sd = ((16 - nlz) + 3) / 4;
    sd |= (bcd == 0) as u32;
    sd
}

#[cfg(test)]
mod tests {
    use core::{fmt, iter};

    use super::*;
    use crate::bcd;

    macro_rules! bit {
        ($x:ident, $idx:literal) => {{
            (($x >> $idx) & 1) == 1
        }};
    }

    // From https://speleotrove.com/decimal/DPDecimal.html
    const fn dpd2bcd(arg: u16) -> u16 {
        let p = bit!(arg, 9);
        let q = bit!(arg, 8);
        let r = bit!(arg, 7);
        let s = bit!(arg, 6);
        let t = bit!(arg, 5);
        let u = bit!(arg, 4);
        let v = bit!(arg, 3);
        let w = bit!(arg, 2);
        let x = bit!(arg, 1);
        let y = bit!(arg, 0);

        let a = (v & w) & (!s | t | !x);
        let b = p & (!v | !w | (s & !t & x));
        let c = q & (!v | !w | (s & !t & x));
        let d = r;
        let e = v & ((!w & x) | (!t & x) | (s & x));
        let f = (s & (!v | !x)) | (p & !s & t & v & w & x);
        let g = (t & (!v | !x)) | (q & !s & t & w);
        let h = u;
        let i = v & ((!w & !x) | (w & x & (s | t)));
        let j = (!v & w) | (s & v & !w & x) | (p & w & (!x | (!s & !t)));
        let k = (!v & x) | (t & !w & x) | (q & v & w & (!x | (!s & !t)));
        let m = y;

        (m as u16)
            | ((k as u16) << 1)
            | ((j as u16) << 2)
            | ((i as u16) << 3)
            | ((h as u16) << 4)
            | ((g as u16) << 5)
            | ((f as u16) << 6)
            | ((e as u16) << 7)
            | ((d as u16) << 8)
            | ((c as u16) << 9)
            | ((b as u16) << 10)
            | ((a as u16) << 11)
    }

    // From https://speleotrove.com/decimal/DPDecimal.html
    const fn bcd2dpd(arg: u16) -> u16 {
        let a = bit!(arg, 11);
        let b = bit!(arg, 10);
        let c = bit!(arg, 9);
        let d = bit!(arg, 8);
        let e = bit!(arg, 7);
        let f = bit!(arg, 6);
        let g = bit!(arg, 5);
        let h = bit!(arg, 4);
        let i = bit!(arg, 3);
        let j = bit!(arg, 2);
        let k = bit!(arg, 1);
        let m = bit!(arg, 0);

        let p = b | (a & j) | (a & f & i);
        let q = c | (a & k) | (a & g & i);
        let r = d;
        let s = (f & (!a | !i)) | (!a & e & j) | (e & i);
        let t = g | (!a & e & k) | (a & i);
        let u = h;
        let v = a | e | i;
        let w = a | (e & i) | (!e & j);
        let x = e | (a & i) | (!a & k);
        let y = m;

        (y as u16)
            | ((x as u16) << 1)
            | ((w as u16) << 2)
            | ((v as u16) << 3)
            | ((u as u16) << 4)
            | ((t as u16) << 5)
            | ((s as u16) << 6)
            | ((r as u16) << 7)
            | ((q as u16) << 8)
            | ((p as u16) << 9)
    }

    const fn bin2dpd(bin: u16) -> u16 {
        assert!(bin <= 999);
        bcd2dpd(bcd::from_bin(bin))
    }

    struct Dpd(u16);
    impl fmt::Display for Dpd {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let pqr = (self.0 >> 7) & 0x7;
            let stu = (self.0 >> 4) & 0x7;
            let v = (self.0 >> 3) & 0x1;
            let wxy = self.0 & 0x7;
            write!(f, "({pqr:03b})({stu:03b})({v:01b})({wxy:03b})")
        }
    }

    struct Bcd(u16);
    impl fmt::Display for Bcd {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let abcd = (self.0 >> 8) & 0xf;
            let efgh = (self.0 >> 4) & 0xf;
            let ijkm = self.0 & 0xf;
            write!(f, "({abcd:04b})({efgh:04b})({ijkm:04b})")
        }
    }

    #[derive(Copy, Clone, Debug)]
    struct Tuple {
        bin: u16,
        bcd: u16,
        dpd: u16,
    }

    /// Returns an iterator over all the bin <-> BCD <-> DPD
    /// mappings.
    fn all() -> impl Iterator<Item = Tuple> {
        let mut idx = 0;
        iter::from_fn(move || {
            if idx > 999 {
                None
            } else {
                let bin = idx;
                let bcd = bcd::from_bin(bin);
                let dpd = bcd2dpd(bcd);
                assert_eq!(bcd, dpd2bcd(dpd), "#{bin}");
                idx += 1;
                Some(Tuple { bin, dpd, bcd })
            }
        })
        .fuse()
    }

    #[test]
    fn test_pack_unpack() {
        use Pattern::*;
        let tests = [
            (5, 0b000_000_0_101, AllSmall),
            (9, 0b000_000_1_001, RightLarge),
            (55, 0b000_101_0_101, AllSmall),
            (79, 0b000_111_1_001, RightLarge),
            (80, 0b000_000_1_010, MiddleLarge),
            (99, 0b000_101_1_111, LeftSmall),
            (555, 0b101_101_0_101, AllSmall),
            (999, 0b001_111_1_111, AllLarge),
        ];
        for (i, (bin, dpd, pattern)) in tests.into_iter().enumerate() {
            let bcd = bcd::from_bin(bin);

            // Check the BCD/DPD classification.
            assert_eq!(bcd::classify(bcd), pattern, "#{i}");
            assert_eq!(classify(dpd), pattern, "#{i}");

            let got = pack(bcd);
            assert_eq!(got, dpd, "#{i} ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = pack_via_bits(bcd);
            assert_eq!(got, dpd, "#{i} ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = unpack(got);
            assert_eq!(got, bcd, "#{i} ({bin}): {} != {}", Bcd(got), Bcd(bcd));
        }
    }

    #[test]
    fn test_pack_bin_u32() {
        // TODO(eric): test the rest of the digits.
        for bin in 0..=999 {
            let got = pack_bin_u32(bin);
            let want = bin2dpd(bin as u16) as u64;
            assert_eq!(got, want, "#{bin}");
        }

        // Test `u32::MAX`.
        let want = {
            // pack(0x4_294_967_295)
            let mut dpd = 0;
            dpd |= pack(0x295) as u64;
            dpd |= (pack(0x967) as u64) << 10;
            dpd |= (pack(0x294) as u64) << 20;
            dpd |= (pack(0x004) as u64) << 30;
            dpd
        };
        let got = pack_bin_u32(u32::MAX);
        assert_eq!(got, want);
    }

    #[test]
    fn test_pack_bin_u113() {
        // TODO(eric): test (some of) the rest of the digits.
        for bin in 0..=999 {
            let got = pack_bin_u113(bin);
            let want = bin2dpd(bin as u16) as u128;
            assert_eq!(got, want, "#{bin}");
        }

        let want = {
            // pack(0x9_999_999_999_999_999_999_999_999_999_999_999)
            let mut dpd = 0;
            for i in 0..11 {
                dpd |= (pack(0x999) as u128) << (i * 10);
            }
            dpd | (pack(0x9) as u128) << 110
        };
        let got = pack_bin_u113(10u128.pow(34) - 1);
        assert_eq!(got, want);
    }

    #[test]
    fn test_pack_unpack_exhaustive() {
        for (i, Tuple { bin, dpd, bcd }) in all().enumerate() {
            assert_eq!(bcd::classify(bcd), classify(dpd), "#{i}");

            assert_eq!(bcd::from_bin(bin), bcd, "#{i}");

            let got = pack(bcd);
            assert_eq!(got, dpd, "#{i}: ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = unpack(got);
            assert_eq!(got, bcd, "#{i}): ({bin}): {} != {}", Bcd(got), Bcd(bcd));
        }
    }

    #[test]
    fn test_div1000() {
        let mut n = u128::MAX;
        let mut i = 0;
        loop {
            let want = {
                let q = n / 1000;
                let r = (n % 1000) as u16;
                (q, r)
            };
            let got = quorem1e3(n);
            assert_eq!(got, want, "#{i}: {n} / 1000");
            if want == (0, 0) {
                break;
            }
            n = want.0;
            i += 1;
        }
    }
}
