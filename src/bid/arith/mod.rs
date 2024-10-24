#![cfg_attr(feature = "bench", allow(missing_docs))]

pub mod arith128;
pub mod arith32;
pub mod arith64;
pub mod idiv;
pub mod uint256;
mod util;

macro_rules! impl_basic {
    ($word:ty) => {
        /// Returns the minimum number of bits required to
        /// represent `x`.
        ///
        /// It returns 0 for `x == 0`.
        pub const fn bitlen(x: $word) -> u32 {
            <$word>::BITS - x.leading_zeros()
        }

        /// Compares `lhs` and `rhs`.
        pub const fn const_cmp(lhs: $word, rhs: $word) -> ::core::cmp::Ordering {
            use ::core::cmp::Ordering;
            match lhs.checked_sub(rhs) {
                Some(0) => Ordering::Equal,
                Some(_) => Ordering::Greater,
                None => Ordering::Less,
            }
        }

        /// Orders `(lhs * 10^shift)` and `rhs`.
        pub const fn const_cmp_shifted(
            lhs: $word,
            rhs: $word,
            shift: u32,
        ) -> ::core::cmp::Ordering {
            use ::core::cmp::Ordering;

            let (lo, hi) = shl(lhs, shift);
            if hi != 0 {
                return Ordering::Less;
            }
            match lo.checked_sub(rhs) {
                Some(0) => Ordering::Equal,
                Some(_) => Ordering::Greater,
                None => Ordering::Less,
            }
        }

        /// Reports whether `(lhs * 10^shift) == rhs`.
        pub const fn const_eq_shifted(lhs: $word, rhs: $word, shift: u32) -> bool {
            let (lo, hi) = shl(lhs, shift);
            hi == 0 && lo == rhs
        }

        /// Returns the number of decimal digits in `x`.
        ///
        /// The result will be in `ceil(log10(2^<$word>::BITS))`.
        pub const fn digits(mut x: $word) -> u32 {
            // Ensure that `x` is non-zero so that `digits(0) ==
            // 1`.
            //
            // This cannot cause an incorrect result because:
            //
            // - `x|1` sets the lowest bit, so it cannot increase
            //   the bit length for a non-zero `x`.
            // - `x >= p` remains correct because the largest
            //   integer less than `p` is 999...999, which is
            //   odd, meaning `x|1` is a no-op.
            x |= 1;

            let r = ((bitlen(x) + 1) * 1233) / 4096;
            // `r` is in [0, digits(<$word>::MAX)], so it cannot
            // panic.
            let p = pow10(r);
            r + (x >= p) as u32
        }

        /// Returns 10^n.
        pub const fn pow10(n: u32) -> $word {
            #[allow(
                clippy::indexing_slicing,
                reason = "This is a const initializer, so panicking is okay."
            )]
            const TABLE: [$word; NUM_POW10] = {
                let mut table = [0; NUM_POW10];
                let mut i = 0;
                while i < table.len() {
                    table[i] = <$word>::pow(10, i as u32);
                    i += 1;
                }
                table
            };

            #[allow(
                clippy::indexing_slicing,
                reason = "Calling code always checks that `n` is in range"
            )]
            let p = TABLE[n as usize]; // or (10 as $word).pow(n)

            // SAFETY: `p` is a power of 10, so it cannot be
            // zero. This line helps the compiler get rid of some
            // panics.
            unsafe { $crate::util::assume(p != 0) };

            p
        }

        /// Returns the number of bits in `10^n`.
        pub const fn pow10_bits(n: u32) -> u32 {
            #[allow(
                clippy::indexing_slicing,
                reason = "This is a const initializer, so panicking is okay."
            )]
            const TABLE: [u32; NUM_POW10] = {
                let mut table = [0; NUM_POW10];
                let mut i = 0;
                while i < table.len() {
                    table[i] = bitlen(pow10(i as u32));
                    i += 1;
                }
                table
            };

            #[allow(
                clippy::indexing_slicing,
                reason = "Calling code always checks that `n` is in range"
            )]
            let bits = TABLE[n as usize];
            bits
        }

        /// The maximum shift that does not overflow `$word`.
        #[allow(dead_code)]
        pub const MAX_SHIFT: u32 = (NUM_POW10 - 1) as u32;

        const NUM_POW10: usize = {
            let mut n = 0;
            while (10 as $word).checked_pow(n).is_some() {
                n += 1
            }
            n as usize
        };

        /// Returns `floor(5 * 10^n)`.
        pub const fn point5(n: u32) -> $word {
            $crate::bid::arith::util::point5(n) as $word
        }

        /// Returns `(lo, hi) = x * 10^n`.
        ///
        /// # Panics
        ///
        /// Panics if `n > MAX_SHIFT`.
        pub const fn shl(x: $word, n: u32) -> ($word, $word) {
            widening_mul(x, pow10(n))
        }

        /// Returns the quotient and remainder `(q, r)` such that
        ///
        /// ```text
        /// q = x / (10^n)
        /// r = x % (10^n)
        /// ```
        pub const fn shr(x: $word, n: u32) -> ($word, $word) {
            if n == 0 {
                // x / (10^0) = x/1 = x
                (x, 0)
            } else if n >= NUM_POW10 as u32 {
                // x / y for y > x = 0
                (0, 0)
            } else {
                quorem_pow10(x, n)
            }
        }

        /// Returns the quotient and remainder `(q, r)` such that
        ///
        /// ```text
        /// q = (lo, hi) / (10^n)
        /// r = (lo, hi) % (10^n)
        /// ```
        pub const fn shr2(lo: $word, hi: $word, n: u32) -> ($word, $word) {
            if hi == 0 {
                shr(lo, n)
            } else {
                wide_quorem_pow10(hi, lo, n)
            }
        }

        #[cfg(test)]
        mod tests {
            use core::cmp;

            use super::*;

            #[test]
            fn test_shl() {
                for n in 0..NUM_POW10 as u32 {
                    let x = 1;
                    let got = shl(x, n).0;
                    let want = x * <$word>::pow(10, n);
                    assert_eq!(got, want, "{n}");
                }
            }

            #[test]
            fn test_shr() {
                for n in 0..NUM_POW10 as u32 {
                    let x = <$word>::pow(10, NUM_POW10 as u32 - 1) - 1;
                    let got = shr(x, n);
                    let want = {
                        let q = x / (10 as $word).pow(n);
                        let r = x % (10 as $word).pow(n);
                        (q, r)
                    };
                    assert_eq!(got, want, "{n}");
                }
            }

            #[test]
            fn test_shr2() {
                const K: u32 = <$word>::BITS;
                const DIGITS: u32 = 9 * (K / 32) - 2;
                const MAX: $word = <$word>::pow(10, DIGITS) - 1;

                fn limbs(u1: $word, u0: $word) -> [u64; ruint::nlimbs(2 * K as usize)] {
                    let mut limbs = [0; ruint::nlimbs(2 * K as usize)];
                    let mut i = 0;
                    for mut u in [u0, u1] {
                        let n = cmp::max(<$word>::BITS / 64, 1);
                        for _ in 0..n {
                            limbs[i] = u as u64;
                            i += 1;
                            u = u.wrapping_shr(64);
                        }
                    }
                    limbs
                }

                for s in 0..NUM_POW10 as u32 {
                    let (u0, mut u1) = widening_mul(MAX, <$word>::pow(10, s));
                    let (u0, carry) = u0.overflowing_add(MAX);
                    if carry {
                        u1 += 1;
                    }
                    let (u0, carry) = u0.overflowing_add(super::super::util::point5(s) as $word);
                    if carry {
                        u1 += 1;
                    }
                    let v = <$word>::pow(10, s);
                    println!("v={v}");
                    let got = shr2(u0, u1, s);

                    #[allow(non_camel_case_types)]
                    type uint = ruint::Uint<{ 2 * K as usize }, { ruint::nlimbs(2 * K as usize) }>;
                    let u = uint::from_limbs(limbs(u1, u0));
                    let v = uint::from_limbs(limbs(0, v));
                    println!("u={u}");
                    println!("v={v}");
                    let want = (
                        (u / v).try_into().unwrap(), // q
                        (u % v).try_into().unwrap(), // r
                    );
                    assert_eq!(got, want, "#{s}: {u} / {v}");
                }
            }

            #[test]
            #[cfg(not(debug_assertions))]
            fn test_digits() {
                let mut buf = itoa::Buffer::new();
                for x in 0..u32::MAX {
                    let got = digits(x as $word);
                    let want = buf.format(x).len() as u32;
                    assert_eq!(got, want, "{x}");
                }
            }
        }
    };
}
pub(super) use impl_basic;
