#![cfg_attr(feature = "bench", allow(missing_docs))]

pub mod arith128;
pub mod arith32;
pub mod arith64;
pub mod idiv;
pub mod uint256;

macro_rules! impl_basic {
    ($full:ty, $half:ty, $max_shift:literal) => {
        /// Returns the minimum number of bits required to
        /// represent `x`.
        ///
        /// It returns 0 for `x == 0`.
        pub const fn bitlen(x: $full) -> u32 {
            <$full>::BITS - x.leading_zeros()
        }

        /// Compares `lhs` and `rhs`.
        pub const fn const_cmp(lhs: $full, rhs: $full) -> ::core::cmp::Ordering {
            use ::core::cmp::Ordering;
            match lhs.checked_sub(rhs) {
                Some(0) => Ordering::Equal,
                Some(_) => Ordering::Greater,
                None => Ordering::Less,
            }
        }

        /// Orders `(lhs * 10^shift)` and `rhs`.
        pub const fn const_cmp_shifted(
            lhs: $full,
            rhs: $full,
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
        pub const fn const_eq_shifted(lhs: $full, rhs: $full, shift: u32) -> bool {
            let (lo, hi) = shl(lhs, shift);
            hi == 0 && lo == rhs
        }

        /// Returns the number of decimal digits in `x`.
        ///
        /// The result will be in [0, $max_shift].
        pub const fn digits(mut x: $full) -> u32 {
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
            // `r` is in [0, digits(<$full>::MAX)], so it cannot
            // panic.
            let p = pow10(r);
            r + (x >= p) as u32
        }

        /// Returns 10^n.
        const fn pow10(n: u32) -> $full {
            /// All powers of 10.
            // This is a const initializer, so panicking is okay.
            #[allow(clippy::indexing_slicing)]
            const POW10: [$full; NUM_POW10] = {
                let mut tab = [0; NUM_POW10];
                let mut i = 0;
                while i < tab.len() {
                    tab[i] = (10 as $full).pow(i as u32);
                    i += 1;
                }
                tab
            };

            #[allow(
                clippy::indexing_slicing,
                reason = "Calling code always checks that `n` is in range"
            )]
            POW10[n as usize] // or (10 as $full).pow(n)
        }

        const NUM_POW10: usize = {
            let mut n = 0;
            while (10 as $full).checked_pow(n).is_some() {
                n += 1
            }
            n as usize
        };

        // const HALF_NUM_POW10: usize = {
        //     let mut n = 0;
        //     while (10 as $half).checked_pow(n).is_some() {
        //         n += 1
        //     }
        //     n as usize
        // };

        /// Returns `x * 10^n`.
        pub const fn shl(x: $full, n: u32) -> ($full, $full) {
            debug_assert!(n <= $max_shift);

            widening_mul(x, pow10(n))
        }

        /// Returns the quotient and remainder `(q, r)` such that
        ///
        /// ```text
        /// q = x / (10^n)
        /// r = x % (10^n)
        /// ```
        #[inline(always)]
        pub const fn shr(x: $full, n: u32) -> ($full, $full) {
            debug_assert!(n <= $max_shift);

            if n == 0 {
                // x / 10^0 = x/1 = x
                return (x, 0);
            }

            // Implement division via recpirocal via "Division by
            // Invariant Integers using Multiplication" by T.
            // Granlund and P. Montgomery.
            //
            // https://gmplib.org/~tege/divcnst-pldi94.pdf
            let q = {
                #[allow(
                    clippy::indexing_slicing,
                    reason = "Calling code always checks that `n` is in range"
                )]
                let (pre, post, m) = RECIP10[n as usize];
                widening_mul(m, x >> pre).1 >> post
            };

            let d = pow10(n);

            // Assert invariants to help the compiler.
            // SAFETY: `q = x / (10^n)`.
            unsafe { $crate::util::assume(q <= x) }

            let r = x - q * d;

            // Assert some invariants to help the compiler.
            // SAFETY: `r = n % (10^n)`.
            unsafe {
                // NB: `r < d` must come first, otherwise the compiler
                // doesn't use it.
                $crate::util::assume(r < d);
                $crate::util::assume(r == (x % d));
            }

            (q, r)
        }

        // const RECIP10_FAST: [$half; HALF_NUM_POW10] = {
        //     let mut table = [0; HALF_NUM_POW10];
        //     let mut i = 0;
        //     while i < table.len() {
        //         let d = <$half>::pow(10, i as u32);
        //         table[i] = reciprocal_2x1(d);
        //         i += 1;
        //     }
        //     table
        // };

        // const RECIP10_FASTISH: [$half; NUM_POW10] = {
        //     let mut table = [0; NUM_POW10];
        //     let mut i = 0;
        //     while i < table.len() {
        //         let d = <$full>::pow(10, i as u32);
        //         table[i] = reciprocal_3x2(d);
        //         i += 1;
        //     }
        //     table
        // };

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_shl() {
                for n in 0..=$max_shift {
                    let x = 1;
                    let got = shl(x, n).0;
                    let want = x * (10 as $full).pow(n);
                    assert_eq!(got, want, "{n}");
                }
            }

            #[test]
            fn test_shr() {
                for n in 0..=$max_shift {
                    let x = (10 as $full).pow($max_shift) - 1;
                    let got = shr(x, n);
                    let want = {
                        let q = x / (10 as $full).pow(n);
                        let r = x % (10 as $full).pow(n);
                        (q, r)
                    };
                    assert_eq!(got, want, "{n}");
                }
            }

            #[test]
            #[cfg(not(debug_assertions))]
            fn test_digits() {
                let mut buf = itoa::Buffer::new();
                for x in 0..u32::MAX {
                    let got = digits(x as $full);
                    let want = buf.format(x).len() as u32;
                    assert_eq!(got, want, "{x}");
                }
            }
        }
    };
}
pub(super) use impl_basic;
