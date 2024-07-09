#![allow(dead_code)]

pub fn decode(c: u16) -> u16 {
    let x = ((c / 16) % 8) as u16;
    let y = (c / 128) as u16;
    let p = ((c / 2) % 8) as u16;
    let d = if p < 6 {
        y
    } else if p == 6 {
        8 + (y % 2)
    } else if p == 7 && (x < 4 || x > 5) {
        8 + (y % 2)
    } else if p == 7 && (x == 4 || x == 5) {
        y
    } else {
        unreachable!()
    };
    println!("x={x} y={y} p={p} d={d}");
    d
}

macro_rules! bit {
    ($x:ident, $idx:literal) => {{
        (($x >> $idx) & 1) == 1
    }};
}

/*
pub fn bin2bcd(mut x: u16) -> u16 {
    const DIGITS: usize = 4;
    const MASK: u16 = 1 << (16 - 1);

    let mut bcd = [0u8; DIGITS];
    let mut carry = [0u8; DIGITS];
    let mut flag = false;
    for _ in 0..16 {
        let mask = (x & MASK) != 0;
        flag = flag || mask;
        if flag {
            let mut k = DIGITS - 1;
            if bcd[k] > 4 {
                bcd[k] += 3;
            }
            carry[k] = (bcd[k] >> 3) & 0xF;
            bcd[k] = ((bcd[k] << 1) & 0xF) | (mask as u8);
            while k > 0 {
                k -= 1;
                if bcd[k] > 4 {
                    bcd[k] += 3;
                }
                carry[k] = (bcd[k] >> 3) & 0xF;
                bcd[k] = ((bcd[k] << 1) | carry[k + 1]) & 0xF;
            }
        }
        x <<= 1;
    }

    ((bcd[0] as u16) << 12) | ((bcd[1] as u16) << 8) | ((bcd[2] as u16) << 4) | (bcd[3] as u16)
}
*/

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
pub fn bcd2dpd(arg: u16) -> u16 {
    let a = bit!(arg, 0);
    let b = bit!(arg, 1);
    let c = bit!(arg, 2);
    let d = bit!(arg, 3);
    let e = bit!(arg, 4);
    let f = bit!(arg, 5);
    let g = bit!(arg, 6);
    let h = bit!(arg, 7);
    let i = bit!(arg, 8);
    let j = bit!(arg, 9);
    let k = bit!(arg, 10);
    let m = bit!(arg, 11);

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

    println!("001 111 1111 // want");
    print!("{:1b}{:1b}{:1b} ", p as u8, q as u8, r as u8);
    print!("{:1b}{:1b}{:1b} ", s as u8, t as u8, u as u8);
    print!("{:1b}{:1b}{:1b}{:1b} ", v as u8, w as u8, x as u8, y as u8);
    println!("// got");
    println!("pqr stu vwxy");

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
    use super::*;

    #[test]
    fn test_bcd2dpd() {
        let input = 0b1001_1001_1001; // 0x999
        let want = 0b001_111_1111;
        let got = bcd2dpd(input);
        assert_eq!(got, want);
    }

    #[test]
    fn test_dpd2bcd() {
        let input = 0b001_111_1111;
        let want = 0b1001_1001_1001; // 0x999
        let got = dpd2bcd(input);
        assert_eq!(got, want);
    }

    #[test]
    fn test_decode() {
        let tests = [
            (5, 0b000_000_0101),
            (9, 0b000_000_1001),
            (55, 0b000_101_0101),
            (79, 0b000_111_1001),
            (80, 0b000_000_1010),
            (99, 0b000_101_1111),
            (555, 0b101_101_0101),
            (999, 0b001_111_1111),
        ];
        for (i, (want, input)) in tests.into_iter().enumerate() {
            let got = decode(input);
            assert_eq!(got, want, "#{i}");
        }
    }
}
