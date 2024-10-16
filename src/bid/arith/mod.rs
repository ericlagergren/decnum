#![cfg_attr(feature = "bench", allow(missing_docs))]

pub mod arith128;
pub mod arith32;
pub mod arith64;
pub mod idiv;
pub mod uint256;
mod util;

// TODO(eric): get rid of `$half`?
// TODO(eric): get rid of `$max_shift`?
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
        /// The result will be in `ceil(log10(2^<$full>::BITS))`.
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
        pub const fn pow10(n: u32) -> $full {
            #[allow(
                clippy::indexing_slicing,
                reason = "This is a const initializer, so panicking is okay."
            )]
            const TABLE: [$full; NUM_POW10] = {
                let mut table = [0; NUM_POW10];
                let mut i = 0;
                while i < table.len() {
                    table[i] = <$full>::pow(10, i as u32);
                    i += 1;
                }
                table
            };

            #[allow(
                clippy::indexing_slicing,
                reason = "Calling code always checks that `n` is in range"
            )]
            let p = TABLE[n as usize]; // or (10 as $full).pow(n)

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

        /// The maximum shift that does not overflow `$full`.
        pub const MAX_SHIFT: u32 = (NUM_POW10 - 1) as u32;

        const NUM_POW10: usize = {
            let mut n = 0;
            while (10 as $full).checked_pow(n).is_some() {
                n += 1
            }
            n as usize
        };

        /// Returns `floor(5 * 10^n)`.
        pub const fn point5(n: u32) -> $full {
            $crate::bid::arith::util::point5(n) as $full
        }

        /// Returns `(lo, hi) = x * 10^n`.
        ///
        /// # Panics
        ///
        /// Panics if `n > MAX_SHIFT`.
        pub const fn shl(x: $full, n: u32) -> ($full, $full) {
            widening_mul(x, pow10(n))
        }

        /// Returns the quotient and remainder `(q, r)` such that
        ///
        /// ```text
        /// q = x / (10^n)
        /// r = x % (10^n)
        /// ```
        pub const fn shr(x: $full, n: u32) -> ($full, $full) {
            if n == 0 {
                // x / (10^0) = x/1 = x
                return (x, 0);
            }
            if n > NUM_POW10 as u32 {
                // x / y for y > x = 0
                return (0, 0);
            }

            // Amazingly, Apple Silicon's integer division units
            // are better than our reciprocals for word-sized
            // operands.
            if cfg!(all(target_vendor = "apple", target_arch = "aarch64")) && <$full>::BITS <= 64 {
                let d = pow10(n);
                return (x / d, x % d);
            }

            // Implement division via recpirocal via "Improved
            // division by invariant integers" by N. Möller
            // and T. Granlund.
            //
            // https://gmplib.org/~tege/division-paper.pdf
            //
            // NB: This is only faster when using 128x128
            // multiplication.
            if <$full>::BITS == 128 {
                #[allow(
                    clippy::indexing_slicing,
                    reason = "Calling code always checks that `n` is in range"
                )]
                let d = RECIP10_2[n as usize];
                return d.quorem(x);
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
                umulh(m, x >> pre) >> post
            };

            let d = pow10(n);

            // Assert invariants to help the compiler.
            // SAFETY: `q = x / (10^n)`.
            unsafe { $crate::util::assume(q <= x) }

            let r = x - q * d;

            // Assert some invariants to help the compiler.
            // SAFETY: `r = n % (10^n)`.
            unsafe {
                // NB: `r < d` must come first, otherwise the
                // compiler doesn't always use it.
                $crate::util::assume(r < d);
                $crate::util::assume(r == (x % d));
            }

            (q, r)
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_shl() {
                for n in 0..NUM_POW10 as u32 {
                    let x = 1;
                    let got = shl(x, n).0;
                    let want = x * <$full>::pow(10, n);
                    assert_eq!(got, want, "{n}");
                }
            }

            #[test]
            fn test_shr() {
                for n in 0..NUM_POW10 as u32 {
                    let x = <$full>::pow(10, NUM_POW10 as u32 - 1) - 1;
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
