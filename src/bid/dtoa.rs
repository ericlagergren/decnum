macro_rules! impl_dtoa {
    ($name:ident) => {
        impl $name {
            /// Converts the decimal to a string.
            #[allow(clippy::indexing_slicing)]
            pub fn format(self, dst: &mut $crate::conv::Buffer) -> &str {
                let dst = &mut dst.buf;

                if self.is_special() {
                    let start = usize::from(self.is_sign_positive());
                    return if self.is_infinite() {
                        &"-Infinity"[start..]
                    } else if self.is_qnan() {
                        &"-NaN"[start..]
                    } else {
                        &"-sNaN"[start..]
                    };
                }
                debug_assert!(self.is_finite());

                let exp = i32::from(self.unbiased_exp());

                let mut tmp = itoa::Buffer::new();
                let coeff = tmp.format(self.coeff()).as_bytes();
                // SAFETY: `coeff_to_str` writes [1, DIGITS] to
                // `tmp` returns a subslice of `tmp`, so the
                // length of `coeff` must be in [1, DIGITS].
                unsafe {
                    assume(!coeff.is_empty());
                    assume(coeff.len() <= Self::DIGITS as usize);
                }

                // `e` is the adjusted exponent.
                // `pre` is the number of digits before the '.'.
                let (e, pre) = {
                    let mut e = 0;
                    #[allow(clippy::cast_possible_wrap)]
                    let mut pre = (coeff.len() as i32) + exp;
                    if exp > 0 || pre < -5 {
                        // Exponential form
                        e = pre - 1;
                        pre = 1;
                    }
                    // SAFETY:
                    //
                    // Because `coeff.len()` is in [1, DIGITS]
                    // and `exp` is in [MIN_EXP, MAX_EXP], `pre`
                    // is initially in [1+MIN_EXP,
                    // DIGITS+MAX_EXP]. After adjustment into
                    // exponential form, `pre` is in [min(1, -5),
                    // DIGITS+MAX_EXP].
                    unsafe {
                        assume(pre >= -5);
                        assume(pre <= (Self::DIGITS + Self::MAX_EXP as u32) as i32);
                    }
                    (e, pre)
                };

                if pre > 0 {
                    // SAFETY: `pre` was in [min(1, -5),
                    // DIGITS+MAX_EXP].  This block is predicated
                    // on `pre > 0`, so `pre` is now in [1,
                    // DIGITS+MAX_EXP].
                    unsafe {
                        assume(pre <= (Self::DIGITS + Self::MAX_EXP as u32) as i32);
                    }

                    let pre = pre.unsigned_abs() as usize;

                    let mut i = 1;
                    dst[0].write(b'-');

                    if pre < coeff.len() {
                        let (pre, post) = coeff.split_at(pre);
                        $crate::util::copy_from_slice(&mut dst[i..i + pre.len()], pre);
                        dst[i + pre.len()].write(b'.');
                        $crate::util::copy_from_slice(
                            &mut dst[i + pre.len() + 1..i + pre.len() + 1 + post.len()],
                            post,
                        );
                        i += 1;
                    } else {
                        $crate::util::copy_from_slice(&mut dst[i..i + coeff.len()], coeff);
                    };
                    i += coeff.len();

                    //println!("e={e}");
                    if e != 0 {
                        dst[i].write(b'E');
                        i += 1;
                        if e < 0 {
                            dst[i].write(b'-');
                        } else {
                            dst[i].write(b'+');
                        };
                        i += 1;

                        //println!("i={i}");

                        // `e` is either 0 or `pre-1`. Since
                        // `pre` is in [1, DIGITS+MAX_EXP] and
                        // DIGITS+MAX_EXP <= u16::MAX, the cast
                        // cannot wrap.
                        const_assert!(($name::DIGITS + $name::MAX_EXP as u32) < u16::MAX as u32);
                        let s = $crate::util::itoa4(e.unsigned_abs() as u16);
                        $crate::util::copy_from_slice(&mut dst[i..i + 4], &s.to_bytes());
                        i += s.digits();
                    }

                    let start = usize::from(self.is_sign_positive());
                    //println!("start={start} i={i} len={}", dst.len());
                    // SAFETY: `buf` only ever contains UTF-8.
                    return unsafe {
                        str::from_utf8_unchecked($crate::util::slice_assume_init_ref(
                            &dst[start..i],
                        ))
                    };
                }

                // SAFETY: TODO
                unsafe {
                    assume(pre >= -5);
                    assume(pre <= 0);
                }

                // -5 => 7
                // -4 => 6
                // -3 => 5
                // -2 => 4
                // -1 => 3
                //  0 => 2
                let pre = 2 + pre.unsigned_abs() as usize;
                // SAFETY: `pre` was in [-5, 0]. After negation and
                // adding 2, `pre` is now in [2, 7].
                unsafe {
                    assume(pre >= 2);
                    assume(pre <= 7);
                }
                const_assert!(1 + 7 + $name::DIGITS as usize <= $crate::conv::Buffer::len());

                $crate::util::copy(dst, b"-0.00000");
                let mut i = 1 + pre;
                // SAFETY: `pre` was in [-5, 0]. After negation
                // and adding 2, `pre` is now in [2, 7]. `coeff`
                // is in [1, DIGITS], so `i+pre+coeff.len()` is
                // in [1+2+DIGITS, 1+7+DIGITS].
                let (_, rest) = dst.split_at_mut(i);
                $crate::util::copy_from_slice(&mut rest[..coeff.len()], coeff);
                i += coeff.len();

                let start = usize::from(self.is_sign_positive());
                // SAFETY: `buf` only ever contains UTF-8.
                return unsafe {
                    str::from_utf8_unchecked($crate::util::slice_assume_init_ref(&dst[start..i]))
                };
            }
        }

        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::Default);
                write!(f, "{str}")
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let sign = self.signbit() as u8;
                if self.is_nan() {
                    if self.is_snan() {
                        write!(f, "[{sign},sNaN]")
                    } else {
                        write!(f, "[{sign},qNaN]")
                    }
                } else if self.is_infinite() {
                    write!(f, "[{sign},inf]")
                } else {
                    write!(
                        f,
                        "[{sign},{},{},form={}]",
                        self.coeff(),
                        self.unbiased_exp(),
                        (self.is_form2() as u8) + 1,
                    )
                }
            }
        }

        impl ::core::fmt::Binary for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::Binary::fmt(&self.to_bits(), f)
            }
        }

        impl ::core::fmt::LowerExp for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::LowerExp);
                ::core::write!(f, "{str}")
            }
        }

        impl ::core::fmt::UpperExp for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> ::core::fmt::Result {
                let mut buf = $crate::conv::Buffer::new();
                let str = buf.format(*self, $crate::conv::Fmt::UpperExp);
                ::core::write!(f, "{str}")
            }
        }
    };
}
pub(crate) use impl_dtoa;
