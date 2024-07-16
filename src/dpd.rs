//! Densely Packed Decimal conversion routines.

use core::{fmt, hint};

/// A BCD's bit pattern.
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    /// All digits are small.
    AllSmall = 0x000,
    /// The right digit is large.
    RightLarge = 0x008,
    /// The middle digit is large.
    MiddleLarge = 0x080,
    /// The left digit is large.
    LeftLarge = 0x800,
    /// The right digit is small.
    RightSmall = 0x880,
    /// The middle digit is small.
    MiddleSmall = 0x808,
    /// The left digit is small.
    LeftSmall = 0x088,
    /// All digits are large.
    AllLarge = 0x888,
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Pattern::*;
        match self {
            AllSmall => write!(f, "AllSmall"),
            RightLarge => write!(f, "RightLarge"),
            MiddleLarge => write!(f, "MiddleLarge"),
            LeftLarge => write!(f, "LeftLarge"),
            RightSmall => write!(f, "RightSmall"),
            MiddleSmall => write!(f, "MiddleSmall"),
            LeftSmall => write!(f, "LeftSmall"),
            AllLarge => write!(f, "AllLarge"),
        }
    }
}

/// Classifies a BCD for packing into a DPD.
pub const fn classify_bcd(bcd: u16) -> Pattern {
    use Pattern::*;
    match bcd & 0x888 {
        0x000 => AllSmall,
        0x008 => RightLarge,
        0x080 => MiddleLarge,
        0x800 => LeftLarge,
        0x880 => RightSmall,
        0x808 => MiddleSmall,
        0x088 => LeftSmall,
        0x888 => AllLarge,
        // SAFETY: Given the bits we've set, these are the only
        // possible results.
        _ => unsafe { hint::unreachable_unchecked() },
    }
}

/// Classifies a DPD for unpacking into a BCD.
pub const fn classify_dpd(dpd: u16) -> Pattern {
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

/// Packs a three-digit BCD into a DPD.
pub const fn pack(mut bcd: u16) -> u16 {
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
    match classify_bcd(bcd) {
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

/// Packs a BCD into a DPD.
pub const fn pack_u32(bcd: u32) -> u32 {
    // [0000 .... ....] [.... .... ....] [.... .... ....]
    //        d0               d1               d2
    let d0 = pack((bcd & 0xfff) as u16) as u32;
    let d1 = pack(((bcd >> 12) & 0xfff) as u16) as u32;
    let d2 = pack(((bcd >> 24) & 0xfff) as u16) as u32;
    (d2 << 20) | (d1 << 10) | d0
}

/// Packs a BCD into a DPD.
pub const fn pack_u64(bcd: u64) -> u64 {
    // [0000 .... ....] [.... .... ....] [.... .... ....]
    //        hi              mid               lo
    let d0 = pack((bcd & 0xfff) as u16) as u64;
    let d1 = pack(((bcd >> 12) & 0xfff) as u16) as u64;
    let d2 = pack(((bcd >> 24) & 0xfff) as u16) as u64;
    let d3 = pack(((bcd >> 36) & 0xfff) as u16) as u64;
    let d4 = pack(((bcd >> 48) & 0xfff) as u16) as u64;
    (d4 << 40) | (d3 << 30) | (d2 << 20) | (d1 << 10) | d0
}

/// Unpacks a DPD into a three-digit BCD.
pub const fn unpack(mut dpd: u16) -> u16 {
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
    match classify_dpd(dpd) {
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

    /*
    /* dpd2bcd -- Expand Densely Packed Decimal to BCD
       argument is a string of 10 characters, each 0 or 1; all 1024
                possibilities are accepted (non-canonicals -> various)
                (for example, 0110101101)
       result   is a string of 12 characters, each 0 or 1
                (for the example, 100100100011 -- 923)
       */
    dpd2bcd: procedure
      -- assign each bit to a variable, named as in the description
      parse arg p +1 q +1 r +1 s +1 t +1 u +1 v +1 w +1 x +1 y +1
      -- derive the result bits, using boolean expressions only
      a= (v & w) & (\s | t | \x)
      b=p & (\v | \w | (s & \t & x))
      c=q & (\v | \w | (s & \t & x))
      d=r
      e=v & ((\w & x) | (\t & x) | (s & x))
      f=(s & (\v | \x)) | (p & \s & t & v & w & x)
      g=(t & (\v | \x)) | (q & \s & t & w)
      h=u
      i=v & ((\w & \x) | (w & x & (s | t)))
      j=(\v & w) | (s & v & \w & x) | (p & w & (\x | (\s & \t)))
      k=(\v & x) | (t & \w & x) | (q & v & w & (\x | (\s & \t)))
      m=y
      -- concatenate the bits and return
      return a||b||c||d||e||f||g||h||i||j||k||m
    */
    pub const fn dpd2bcd(arg: u16) -> u16 {
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

    /*
    /* bcd2dpd -- Compress BCD to Densely Packed Decimal
       argument is a string of 12 characters, each 0 or 1, being 3 digits
                of 4 bits, each being a valid BCD digit (0000-1001)
                (for example, 923 is 100100100011)
       result   is a string of 10 characters, each 0 or 1
                (for the example, this would be 0110101101)
       */
    bcd2dpd: procedure
      -- assign each bit to a variable, named as in the description
      parse arg a +1 b +1 c +1 d +1 e +1 f +1 g +1 h +1 i +1 j +1 k +1 m +1

      -- derive the result bits, using boolean expressions only
      -- [the operators are: '&'=AND, '|'=OR, '\'=NOT.]
      p=b | (a & j) | (a & f & i)
      q=c | (a & k) | (a & g & i)
      r=d
      s=(f & (\a | \i)) | (\a & e & j) | (e & i)
      t=g  | (\a & e &k) | (a & i)
      u=h
      v=a | e | i
      w=a | (e & i) | (\e & j)
      x=e | (a & i) | (\a & k)
      y=m
      -- concatenate the bits and return
      return p||q||r||s||t||u||v||w||x||y
    */
    pub const fn bcd2dpd(arg: u16) -> u16 {
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
            assert_eq!(classify_bcd(bcd), pattern, "#{i}");
            assert_eq!(classify_dpd(dpd), pattern, "#{i}");

            let got = pack(bcd);
            assert_eq!(got, dpd, "#{i} ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = unpack(got);
            assert_eq!(got, bcd, "#{i} ({bin}): {} != {}", Bcd(got), Bcd(bcd));
        }
    }

    #[test]
    fn test_pack_unpack_exhaustive() {
        for (i, Tuple { bin, dpd, bcd }) in all().enumerate() {
            assert_eq!(classify_bcd(bcd), classify_dpd(dpd), "#{i}");

            assert_eq!(bcd::from_bin(bin), bcd, "#{i}");

            let got = pack(bcd);
            assert_eq!(got, dpd, "#{i}: ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = unpack(got);
            assert_eq!(got, bcd, "#{i}): ({bin}): {} != {}", Bcd(got), Bcd(bcd));
        }
    }

    // #[test]
    // fn test_pack_u32() {
    //     for bin in 0..999_999 {
    //         let bcd = bcd::from_u32(bin);
    //         assert_eq!(bcd::to_u32(bcd), bin, "{bin}");
    //         let lhs = bcd2dpd((bcd >> 16) as u16);
    //         let rhs = bcd2dpd(bcd as u16);

    //         let got = pack_u32(bcd);
    //         let want = ((lhs as u32) << 10) | (rhs as u32);
    //         assert_eq!(got, want, "{bin}");
    //     }
    // }

    // TODO
    // #[test]
    // fn test_pack_u64() {
    //     for bin in 0..999_999_999 {
    //         let bcd = bcd::from_u64(bin);
    //         assert_eq!(bcd::to_u64(bcd), bin, "{bin}");
    //         let lhs = bcd2dpd((bcd >> 16) as u16);
    //         let rhs = bcd2dpd(bcd as u16);
    //
    //         let got = pack_u64(bcd);
    //         let want = ((lhs as u32) << 10) | (rhs as u32);
    //         assert_eq!(got, want, "{bin}");
    //     }
    // }
}
