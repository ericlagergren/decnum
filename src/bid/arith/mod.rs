#![cfg_attr(feature = "bench", allow(missing_docs))]

pub mod arith128;
pub mod arith32;
pub mod arith64;
pub mod idiv;
mod uint256;

#[cfg(test)]
pub use uint256::u256;

macro_rules! impl_basic {
    ($word:ty, $wide:ty) => {
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
            let p = TABLE[n as usize]; // or <$word>::pow(10, n)

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
            TABLE[n as usize]
        }

        const NUM_POW10: usize = {
            let mut n = 0;
            while <$word>::checked_pow(10, n).is_some() {
                n += 1;
            }
            n as usize
        };

        /// Returns `floor(0.5 * 10^n)`.
        pub const fn point5(n: u32) -> $word {
            #[allow(
                clippy::indexing_slicing,
                reason = "This is a const initializer, so panicking is okay."
            )]
            const TABLE: [$word; NUM_POW5] = {
                let mut table = [0; NUM_POW5];
                let mut i = 1;
                table[0] = 0;
                while i < table.len() {
                    table[i] = 5 * <$word>::pow(10, (i - 1) as u32);
                    i += 1;
                }
                table
            };

            #[allow(
                clippy::indexing_slicing,
                reason = "Calling code always checks that `n` is in range"
            )]
            TABLE[n as usize]
        }

        const NUM_POW5: usize = {
            // Start at 1 so that pow5(0) == 0.
            let mut n = 1;
            loop {
                let Some(p) = <$word>::checked_pow(10, (n - 1) as u32) else {
                    break;
                };
                if <$word>::checked_mul(5, p).is_none() {
                    break;
                }
                n += 1;
            }
            n
        };

        /// Returns `(lo, hi) = x * 10^n`.
        ///
        /// # Panics
        ///
        /// Panics if `10^n` overflows.
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
                // x/(10^0) = x/1 = x
                (x, 0)
            } else if n >= NUM_POW10 as u32 {
                // x/y for y > x = 0
                (0, 0)
            } else {
                quorem_pow10(x, n)
            }
        }

        /// Like [`shr`], but for a double-width word.
        pub const fn shr2(lo: $word, hi: $word, n: u32) -> ($word, $word) {
            if n == 0 && hi == 0 {
                // x/(10^0) = x/1 = x
                //
                // This also holds if `hi != 0`, but we only
                // return a single word.
                (lo, 0)
            } else if n >= NUM_POW10 as u32 {
                // x/y for y > x = 0
                (0, 0)
            } else {
                wide_quorem_pow10(hi, lo, n)
            }
        }
    };
}
pub(super) use impl_basic;

#[cfg(test)]
macro_rules! impl_tests {
    ($word:ty, $wide:ty) => {
        #[cfg(test)]
        mod tests {
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
                const BITS: usize = (K * 2) as usize;
                const NLIMBS: usize = ruint::nlimbs(BITS as usize);

                fn limbs(u1: $word, u0: $word) -> [u64; NLIMBS] {
                    let mut limbs = [0; NLIMBS];
                    match <$word>::BITS {
                        32 => {
                            limbs[0] = ((u1 as u64) << 32) | (u0 as u64);
                        }
                        64 => {
                            limbs[0] = u0 as u64;
                            limbs[1] = u1 as u64;
                        }
                        128 => {
                            limbs[0] = u0 as u64;
                            limbs[1] = (u0 >> 64) as u64;
                            limbs[2] = u1 as u64;
                            limbs[3] = (u1 >> 64) as u64;
                        }
                        bits => panic!("unknown bit size: {bits}"),
                    }
                    limbs
                }

                for s in 0..NUM_POW10 as u32 {
                    let (u0, mut u1) = widening_mul(MAX, <$word>::pow(10, s));
                    let (u0, carry) = u0.overflowing_add(MAX);
                    if carry {
                        u1 += 1;
                    }
                    let (u0, carry) = u0.overflowing_add(point5(s));
                    if carry {
                        u1 += 1;
                    }
                    let v = <$word>::pow(10, s);
                    println!("v={v}");
                    let got = shr2(u0, u1, s);

                    #[allow(non_camel_case_types)]
                    type uint = ruint::Uint<BITS, NLIMBS>;
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
#[cfg(test)]
pub(super) use impl_tests;
