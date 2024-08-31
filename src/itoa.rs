use core::{mem::MaybeUninit, str};

use super::util;

/// A string of length [1,4].
#[derive(Copy, Clone, Debug)]
pub(crate) struct Str4(u32);

impl Str4 {
    /// Returns the number of significant digits.
    pub const fn digits(self) -> usize {
        (((32 - self.0.leading_zeros()) + 7) / 8) as usize
    }

    /// Converts the string to bytes.
    ///
    /// Only [`len`][Self::len] bytes are valid.
    pub const fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}

/// Converts the binary number `n` to a base-10 string.
///
/// `n` must be in [1, 9999].
pub(crate) const fn itoa4(n: u16) -> Str4 {
    debug_assert!(n > 0 && n < 10_000);

    const MASK: u32 = 0x30303030;

    let mut n = n as u32;
    let mut v = 0;
    let mut i = 0;
    while i < 4 {
        v |= (n % 10) << (24 - (i * 8));
        n /= 10;
        i += 1;
    }

    // Figure out how much we have to shift to get rid of
    // insignificant zeros. In other words, if v == 0 we shift by
    // 24, not 32.
    let ntz = (v.trailing_zeros() / 8) * 8;
    let mut s = ntz;
    s |= (ntz & 32) >> 1;
    s |= (ntz & 32) >> 2;
    s &= 31;

    v |= MASK;
    v >>= s;
    Str4(v)
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct Buffer {
    buf: [MaybeUninit<u8>; 39],
}

impl Buffer {
    pub const fn new() -> Self {
        Self {
            buf: [MaybeUninit::<u8>::uninit(); 39],
        }
    }

    pub fn format<I: Integer>(&mut self, x: I) -> &str {
        x.write(unsafe {
            &mut *(&mut self.buf as *mut [MaybeUninit<u8>; 39] as *mut <I as Integer>::Buffer)
        })
    }
}

pub(crate) trait Integer {
    type Buffer: 'static;

    fn write(self, dst: &mut Self::Buffer) -> &str;
}

impl Integer for u128 {
    type Buffer = [MaybeUninit<u8>; 39];

    fn write(self, dst: &mut Self::Buffer) -> &str {
        let mut tmp = ::itoa::Buffer::new();
        let s = tmp.format(self).as_bytes();
        util::copy_from_slice(&mut dst[..s.len()], s);
        todo!()
    }
}

impl Integer for u64 {
    type Buffer = [MaybeUninit<u8>; 20];

    fn write(self, dst: &mut Self::Buffer) -> &str {
        let n = itoa64(dst, self);
        // SAFETY: TODO
        unsafe { str::from_utf8_unchecked(util::slice_assume_init_ref(&dst[..n])) }
    }
}

fn itoa64(dst: &mut [MaybeUninit<u8>; 20], x: u64) -> usize {
    let top = x / 100000000;
    let bottom = x % 100000000;
    let first = 0x3030303030303030 | encode_ten_thousands(top / 10000, top % 10000);
    let second = 0x3030303030303030 | encode_ten_thousands(bottom / 10000, bottom % 10000);
    util::copy_from_slice(&mut dst[..8], &first.to_le_bytes());
    util::copy_from_slice(&mut dst[8..16], &second.to_le_bytes());
    16
}

const fn encode_hundreds(hi: u32, lo: u32) -> u32 {
    // Pack into a 32-bit value.
    let merged = hi | (lo << 16);
    // 103/1024 ~= 1/10
    let mut tens = (merged * 103) / 1024;
    // Mask garbage bits between digits.
    // tens = [ hi/10 0 lo/10 0 ]
    tens &= (0xf << 16) | 0xf;
    // x mod 10 = x - 10 * (x / 10)
    // (merged - 10 * tens) = [ hi%10 0 lo%10 0 ]
    tens + ((merged - 10 * tens) << 8)
}

const fn encode_ten_thousands(hi: u64, lo: u64) -> u64 {
    let merged = hi | (lo << 32);
    // 10486 / 2^20 ~= 1/100
    let top = ((merged * 10486) >> 20) & ((0x7F << 32) | 0x7F);
    // Trailing two digits in the 1e4 chunks.
    let bot = merged - 100 * top;

    // We now have 4 radix-100 digits in little-endian order,
    // each in its own 16 bit area.
    let hundreds = (bot << 16) + top;

    // Divide and mod by 10 all 4 radix-100 digits in parallel.
    let mut tens = (hundreds * 103) >> 10;
    tens &= (0xF << 48) | (0xF << 32) | (0xF << 16) | 0xF;
    tens += (hundreds - 10 * tens) << 8;

    tens
}

fn terje(buf: &mut [u8; 10], x: u32) -> &str {
    const F1_10000: u32 = (1 << 28) / 10000;

    let lo = x % 100000;
    let hi = x / 100000;

    let mut tmplo = lo * (F1_10000 + 1) - (lo / 4);
    let mut tmphi = hi * (F1_10000 + 1) - (hi / 4);

    let mut mask = 0x0fffffff;
    let mut shift = 28;
    let mut i = 0;
    while i < 5 {
        buf[i + 0] = b'0' + (tmphi >> shift) as u8;
        buf[i + 5] = b'0' + (tmplo >> shift) as u8;
        tmphi = (tmphi & mask) * 5;
        tmplo = (tmplo & mask) * 5;
        mask >>= 1;
        shift -= 1;
        i += 1;
    }
    println!("{buf:?}");

    let mut p: &[u8] = &*buf;
    if let Some((chunk, rest)) = p.split_first_chunk() {
        if u64::from_le_bytes(*chunk) == 0x3030303030303030 {
            p = rest;
        }
    }
    if let Some((chunk, rest)) = p.split_first_chunk() {
        if u32::from_le_bytes(*chunk) == 0x30303030 {
            p = rest;
        }
    }
    if let Some((chunk, rest)) = p.split_first_chunk() {
        if u16::from_le_bytes(*chunk) == 0x3030 {
            p = rest;
        }
    }
    if let Some((chunk, rest)) = p.split_first_chunk() {
        if u8::from_le_bytes(*chunk) == 0x30 {
            p = rest;
        }
    }
    if p.is_empty() {
        p = &buf[0..1]
    }
    unsafe { str::from_utf8_unchecked(p) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integer() {
        let mut buf1 = [MaybeUninit::<u8>::uninit(); 20];
        let mut buf2 = itoa::Buffer::new();
        let mut buf3 = [0u8; 10];
        for x in 0..=u32::MAX {
            println!("terje = {}", terje(&mut buf3, x));
            let got = (x as u64).write(&mut buf1);
            let want = buf2.format(x);
            assert_eq!(got, want, "#{x}");
        }
    }
}
