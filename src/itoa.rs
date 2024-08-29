use core::{mem::MaybeUninit, ptr, slice, str};

use super::util::{self, assume};

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

const U128_MAX_LEN: usize = 39;
const U64_MAX_LEN: usize = 20;

const DEC_DIGITS_LUT: &[u8] = b"\
      0001020304050607080910111213141516171819\
      2021222324252627282930313233343536373839\
      4041424344454647484950515253545556575859\
      6061626364656667686970717273747576777879\
      8081828384858687888990919293949596979899";

pub(crate) trait Integer {
    type Buffer: 'static;

    fn write(self, dst: &mut Self::Buffer) -> usize;
}

impl Integer for u128 {
    type Buffer = [MaybeUninit<u8>; 39];

    fn write(self, buf: &mut Self::Buffer) -> usize {
        let is_nonnegative = self >= 0;
        let n = if is_nonnegative {
            self as u128
        } else {
            // Convert negative number to positive by summing 1 to its two's complement.
            (!(self as u128)).wrapping_add(1)
        };
        let mut curr = buf.len() as isize;
        let buf_ptr = buf.as_mut_ptr() as *mut u8;

        // Divide by 10^19 which is the highest power less than 2^64.
        let (n, rem) = quorem1e19(n);
        let buf1 = unsafe {
            buf_ptr.offset(curr - U64_MAX_LEN as isize) as *mut [MaybeUninit<u8>; U64_MAX_LEN]
        };
        curr -= rem.write(unsafe { &mut *buf1 }) as isize;

        if n != 0 {
            // Memset the base10 leading zeros of rem.
            let target = buf.len() as isize - 19;
            unsafe {
                ptr::write_bytes(buf_ptr.offset(target), b'0', (curr - target) as usize);
            }
            curr = target;

            // Divide by 10^19 again.
            let (n, rem) = quorem1e19(n);
            let buf2 = unsafe {
                buf_ptr.offset(curr - U64_MAX_LEN as isize) as *mut [MaybeUninit<u8>; U64_MAX_LEN]
            };
            curr -= rem.write(unsafe { &mut *buf2 }) as isize;

            if n != 0 {
                // Memset the leading zeros.
                let target = buf.len() as isize - 38;
                unsafe {
                    ptr::write_bytes(buf_ptr.offset(target), b'0', (curr - target) as usize);
                }
                curr = target;

                // There is at most one digit left
                // because u128::MAX / 10^19 / 10^19 is 3.
                curr -= 1;
                unsafe {
                    *buf_ptr.offset(curr) = (n as u8) + b'0';
                }
            }
        }

        if !is_nonnegative {
            curr -= 1;
            unsafe {
                *buf_ptr.offset(curr) = b'-';
            }
        }

        buf.len() - curr as usize
    }
}

impl Integer for u64 {
    type Buffer = [MaybeUninit<u8>; 20];

    fn write(self, dst: &mut Self::Buffer) -> usize {
        const fn pow(x: u32) -> u64 {
            10u64.pow(x)
        }

        let x = self;

        if x < pow(2) {
            return itoa_hundreds(util::sub_array(dst), x as u32);
        }

        if x < pow(4) {
            return itoa_ten_thousands(util::sub_array(dst), x as u32);
        }

        if x < pow(8) {
            let mut buf = encode_ten_thousands(x / pow(4), x % pow(4));
            let zeros = buf.trailing_zeros() & !0x7;
            buf += 0x3030303030303030; // BCD to ASCII.
            buf >>= zeros; // Drop unused zeros.
            util::copy_from_slice(&mut dst[..8], &buf.to_le_bytes());
            return (8 - zeros / 8) as usize;
        }

        if x < pow(10) {
            let out = itoa_hundreds(util::sub_array(dst), (x / pow(8)) as u32);
            util::copy_from_slice(&mut dst[..8], &out.to_le_bytes());
            return 8;
        }

        let buf = encode_ten_thousands(
            // TODO
            (x / pow(4)) - ((x / pow(8)) * pow(4)),
            x % pow(4),
        ) + 0x3030303030303030;

        if x < pow(16) {
            let hi_hi = (x / pow(8)) / pow(4);
            let hi_lo = (x / pow(8)) - hi_hi * 10u64.pow(4);
            let mut buf_hi = encode_ten_thousands(hi_hi, hi_lo);
            let zeros = buf_hi.trailing_zeros() & (!8u32 + 1);
            buf_hi |= 0x3030303030303030;
            buf_hi >>= zeros;
            let idx = (8 - zeros / 8) as usize;
            util::copy_from_slice(&mut dst[..8], &buf_hi.to_le_bytes());
            util::copy_from_slice(&mut dst[8 + idx..8 + idx + 8], &buf_hi.to_le_bytes());
            (idx + 8) as usize
        } else {
            let hi = x / pow(16);
            let mid = (x / pow(8)) - hi * pow(8);
            let mid_hi = mid / 10u64.pow(4);
            let mid_lo = mid - mid_hi * pow(4);
            let buf_mid = encode_ten_thousands(mid_hi, mid_lo) | 0x3030303030303030;
            itoa_ten_thousands(util::sub_array(dst), hi as u32);
            util::copy_from_slice(&mut dst[..8], &buf_mid.to_le_bytes());
            util::copy_from_slice(&mut dst[8..], &buf.to_le_bytes());
            16
        }
    }
}

fn itoa_hundreds(dst: &mut [MaybeUninit<u8>; 4], x: u32) -> usize {
    let small = ((x - 10) as i64) >> 8;
    let mut base = (b'0' as u32) | ((b'0' as u32) << 8);
    let hi = (x * 103) >> 10;
    let lo = x - 10 * hi;
    base += hi + (lo << 8);
    base >>= small & 8;
    util::copy_from_slice(dst, &base.to_le_bytes());
    (2 + small) as usize
}

fn itoa_ten_thousands(dst: &mut [MaybeUninit<u8>; 4], x: u32) -> usize {
    const POW: u32 = 10u32.pow(2);
    let mut buf = encode_hundreds(x / POW, x % POW);
    let zeros = buf.trailing_zeros() & !0x7;
    buf |= 0x30303030; // BCD -> ASCII
    buf >>= zeros;
    util::copy_from_slice(dst, &buf.to_le_bytes());
    (4 - zeros / 8) as usize
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

/// Returns (q, r) such that
///
/// ```text
/// q = n / 1e19
/// r = n % 1e19
/// ```
const fn quorem1e19(n: u128) -> (u128, u64) {
    #![allow(non_upper_case_globals)]

    const d: u128 = 10u128.pow(19);

    let q = {
        // Implement division via recpirocal via "Division by
        // Invariant Integers using Multiplication" by T.
        // Granlund and P. Montgomery.
        //
        // https://gmplib.org/~tege/divcnst-pldi94.pdf

        // l = ceil( log2(d) )
        //   = ceil( 63.116... )
        //   = 64
        // m' = floor( 2^N * (2^l - d)/d ) + 1
        //    = floor( (2^128) * (2^64  - 1e19)/1e19 ) + 1
        //    = floor( (2^128) * 0.84467... ) + 1
        const REC: u128 = 287427806617729612920204334888998430155;

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
    // SAFETY: `q = n/1e19`.
    unsafe {
        assume(q <= n);
        assume(q == n / d);
        assume(q * d <= n);
    }

    let r = n - q * d;

    // Assert some invariants to help the compiler.
    // SAFETY: `r = n%1e19`.
    unsafe {
        // NB: `r < d` must come first, otherwise the compiler
        // doesn't use it.
        assume(r < d);
        assume(r == (n % d));
    }

    (q, r as u64)
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

#[cfg(test)]
mod tests {
    use core::str;

    use super::*;

    #[test]
    fn test_itoa4() {
        let mut buf = ::itoa::Buffer::new();
        for n in 0..=9999 {
            let w = itoa4(n);
            let i = ((32 - w.0.leading_zeros()) + 7) / 8;
            let got = w.to_bytes();
            let got = str::from_utf8(&got[..i as usize]).unwrap();
            let want = buf.format(n);
            assert_eq!(got, want, "#{n}");
        }
    }
}
