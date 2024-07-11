#![allow(dead_code)]

use core::hint;

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
pub fn classify_dpd(dpd: u16) -> Pattern {
    use Pattern::*;

    // .... ..pq rstu vwxy
    // .... .... ...v wxst

    println!(
        "dpd: ({:03b})({:03b})({:01b})({:03b})",
        (dpd >> 7) & 0x7,
        (dpd >> 4) & 0x7,
        (dpd >> 3) & 0x1,
        dpd & 0x7,
    );

    // Match `v`.
    if dpd & 0x8 == 0 {
        return AllSmall;
    }

    println!("vwx = {:#x}", dpd & 0xe);

    // Match bits `vwx`.
    match dpd & 0xe {
        0x8 => return RightLarge,
        0xa => return MiddleLarge,
        0xc => return LeftLarge,
        _ => {}
    }

    println!("st = {:#x}", dpd & 0x60);

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

/// Packs a BCD into a DPD.
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
            ((bcd & 0x700) >> 1) | ((bcd & 0x6) << 4) | 0xa | (bcd & 0x1)
        }
        LeftLarge => {
            // .... abcd efgh ijkm
            // .... ..jk dfgh 110m
            ((bcd & 0x6) << 6) | ((bcd >> 1) & 0x80) | 0xc | (bcd & 0x1)
        }
        RightSmall => {
            // .... abcd efgh ijkm
            // .... ..jk d00h 111m
            ((bcd & 0x6) << 6) | ((bcd >> 1) & 0x80) | (bcd & 0x11) | 0xe
        }
        MiddleSmall => {
            // .... abcd efgh ijkm
            // .... ..fg d01h 111m
            ((bcd & 0x60) << 3) | ((bcd >> 1) & 0x80) | (bcd & 0x11) | 0x2e
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

/// Unpacks a DPD into a BCD.
pub fn unpack(mut dpd: u16) -> u16 {
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
            ((dpd & 0x380) << 1) | (dpd & 0x777)
        }
        RightLarge => {
            // .... ..pq rstu vwxy
            // .... 0pqr 0stu 100y
            ((dpd & 0x380) << 1) | (dpd & 0x71) | 0x8
        }
        MiddleLarge => {
            // .... ..pq rstu vwxy
            // .... 0pqr 100u 0sty
            ((dpd & 0x380) << 1) | ((dpd & 0x60) >> 4) | (dpd & 1) | 0x10
        }
        LeftLarge => {
            // .... ..pq rstu vwxy
            // .... 100r 0stu 0pqy
            ((dpd & 0x80) << 1) | (dpd & 0x71) | ((dpd & 0x300) >> 7) | 0x800
        }
        RightSmall => {
            // .... ..pq rstu vwxy
            // .... 100r 100u 0pqy
            todo!()
        }
        MiddleSmall => {
            // .... ..pq rstu vwxy
            // .... 100r 0pqu 100y
            todo!()
        }
        LeftSmall => {
            // .... ..pq rstu vwxy
            // .... 0pqr 100u 100y
            todo!()
        }
        AllLarge => {
            // .... ..pq rstu vwxy
            // .... 100r 100u 100y
            todo!()
        }
    }
}

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
pub fn dpd2bcd(arg: u16) -> u16 {
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

    print!("{:1b}{:1b}{:1b} ", p as u8, q as u8, r as u8);
    print!("{:1b}{:1b}{:1b} ", s as u8, t as u8, u as u8);
    print!("{:1b}{:1b}{:1b}{:1b} ", v as u8, w as u8, x as u8, y as u8);
    println!("// input");
    println!("pqr stu vwxy");

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

    println!("1001 1001 1001 // want");
    print!("{:1b}{:1b}{:1b}{:1b} ", a as u8, b as u8, c as u8, d as u8);
    print!("{:1b}{:1b}{:1b}{:1b} ", e as u8, f as u8, g as u8, h as u8);
    print!("{:1b}{:1b}{:1b}{:1b} ", i as u8, j as u8, k as u8, m as u8);
    println!("// got");
    println!("abcd efgh ijkm");

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

#[cfg(test)]
mod tests {
    use core::fmt;

    use super::*;
    use crate::bcd;

    #[test]
    fn test_dpd2bcd() {
        let input = 0b001_111_1111;
        let want = 0b1001_1001_1001; // 0x999
        let got = dpd2bcd(input);
        assert_eq!(got, want);
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
            let bcd = bcd::from_u16(bin);

            // Check the BCD/DPD classification.
            assert_eq!(classify_bcd(bcd), pattern, "#{i}");
            assert_eq!(classify_dpd(dpd), pattern, "#{i}");

            let got = pack(bcd);
            assert_eq!(got, dpd, "#{i} ({bin}): {} != {}", Dpd(got), Dpd(dpd));

            let got = unpack(got);
            assert_eq!(got, bcd, "#{i} ({bin}): {} != {}", Bcd(got), Bcd(bcd));
            println!();
        }
    }
}
