macro_rules! impl_dtoa {
    ($name:ident, $arith:ident) => {
        impl $name {
            /// Converts the decimal to a string.
            #[allow(clippy::indexing_slicing)]
            pub(crate) fn format(self, dst: &mut $crate::conv::Buffer) -> &str {
                let dst = &mut dst.buf;

                let start = usize::from(self.is_sign_positive());
                if self.is_special() {
                    if self.is_infinite() {
                        // `start` is either 0 or 1, so this
                        // cannot panic.
                        #[allow(clippy::string_slice)]
                        return &"-Infinity"[start..];
                    }
                    println!("payload = {}", self.payload());
                    if self.payload() == 0 {
                        // `start` is either 0 or 1, so this
                        // cannot panic.
                        #[allow(clippy::string_slice)]
                        return if self.is_snan() {
                            &"-sNaN"[start..]
                        } else {
                            &"-NaN"[start..]
                        };
                    }
                }
                debug_assert!(self.is_finite() || (self.is_nan() && self.payload() != 0));

                let mut tmp = ::itoa::Buffer::new();
                let coeff = {
                    let x = if self.is_finite() {
                        self.coeff()
                    } else {
                        self.payload()
                    };
                    debug_assert!($arith::digits(x) <= Self::DIGITS);

                    let coeff = tmp.format(x).as_bytes();
                    // Teach the compiler about the length of
                    // `coeff` to elimite bounds checks.
                    match coeff.split_at_checked(Self::DIGITS as usize) {
                        Some((s, rest)) => {
                            // `self.coeff()` is at most `DIGITS`
                            // long and `self.payload()` is
                            // smaller, so `rest` should always
                            // be empty.
                            debug_assert!(rest.is_empty());
                            s
                        }
                        None => coeff,
                    }
                };
                debug_assert!(!coeff.is_empty());
                debug_assert!(coeff.len() <= Self::DIGITS as usize);

                if self.is_nan() {
                    let mut i = if self.is_snan() {
                        $crate::util::copy(dst, b"-sNaN")
                    } else {
                        $crate::util::copy(dst, b"-NaN")
                    };
                    i += $crate::util::copy(&mut dst[i..], coeff);

                    // SAFETY: We wrote to `dst[..i+coeff.len()]`
                    let buf = unsafe { $crate::util::slice_assume_init_ref(&dst[start..i]) };
                    // SAFETY: We only write UTF-8 to `dst`.
                    return unsafe { str::from_utf8_unchecked(buf) };
                }
                debug_assert!(self.is_finite());

                // exp is in [ETINY, EMAX].
                let exp = i32::from(self.unbiased_exp());

                // `e` is the adjusted exponent in [0, pre-1].
                // NB: `e` is either 0 or `pre-1`.
                //
                // `pre` is the number of digits before the
                // decimal point in [-5, DIGITS+EMAX].
                let (e, pre) = {
                    let mut e = 0;
                    #[allow(clippy::cast_possible_wrap)]
                    let mut pre = (coeff.len() as i32) + exp;
                    if exp > 0 || pre < -5 {
                        // Exponential form.
                        e = pre - 1;
                        pre = 1;
                    }
                    // `coeff.len()` = [1, DIGITS]
                    // `exp` = [ETINY, EMAX]
                    // `pre` = `coeff.len() + exp`
                    //       = [1, DIGITS] + [ETINY, EMAX]
                    //       = [1+ETINY, DIGITS+EMAX]
                    //
                    // If `pre` is converted to exponential form,
                    // `pre` = 1. Therefore:
                    //
                    // `pre` = [min(1, -5), DIGITS+EMAX]
                    //       = [-5, DIGITS+EMAX]
                    debug_assert!(pre >= -5);
                    debug_assert!(pre <= (Self::DIGITS + Self::EMAX as u32) as i32);
                    (e, pre)
                };

                if pre > 0 {
                    // Before this block
                    //
                    // `pre` = [-5, DIGITS+EMAX]
                    //
                    // This block is predicated on `pre > 0`,
                    // meaning
                    //
                    // `pre` = [1, DIGITS+EMAX]
                    debug_assert!(pre <= (Self::DIGITS + Self::EMAX as u32) as i32);

                    let pre = pre.unsigned_abs() as usize;

                    let mut i = 1;
                    dst[0].write(b'-');

                    if pre < coeff.len() {
                        let (pre, post) = coeff.split_at(pre);
                        // Write `pre` before the dot.
                        $crate::util::copy_from_slice(&mut dst[i..i + pre.len()], pre);
                        // Dot!
                        dst[i + pre.len()].write(b'.');
                        // Write `post` after the dot.
                        $crate::util::copy_from_slice(
                            &mut dst[i + pre.len() + 1..i + pre.len() + 1 + post.len()],
                            post,
                        );
                        i += 1; // dot
                    } else {
                        $crate::util::copy_from_slice(&mut dst[i..i + coeff.len()], coeff);
                    };
                    i += coeff.len();

                    if e != 0 {
                        dst[i].write(b'E');
                        i += 1;
                        if e < 0 {
                            dst[i].write(b'-');
                        } else {
                            dst[i].write(b'+');
                        };
                        i += 1;

                        // `e` is either 0 or `pre-1`. Since
                        // `pre` = [1, DIGITS+EMAX] and
                        // `DIGITS+EMAX <= u16::MAX`, the cast
                        // cannot wrap.
                        const_assert!(($name::DIGITS + $name::EMAX as u32) < u16::MAX as u32);
                        let s = $crate::itoa::itoa4(e.unsigned_abs() as u16);
                        $crate::util::copy_from_slice(&mut dst[i..i + 4], &s.to_bytes());
                        i += s.digits();
                    }

                    let start = usize::from(self.is_sign_positive());
                    // SAFETY: We wrote to `dst[..i]`.
                    let buf = unsafe { $crate::util::slice_assume_init_ref(&dst[start..i]) };
                    // SAFETY: We only write UTF-8 to `dst`.
                    return unsafe { str::from_utf8_unchecked(buf) };
                }
                debug_assert!(pre <= 0);

                let pre = {
                    // `pre` = [-5, DIGITS+EMAX]
                    //
                    // The previous block is predicated on `pre
                    // > 0`, meaning at this point `pre <= 0`.
                    // Therefore, `pre` must be in [-5, 0].
                    debug_assert!(pre >= -5);
                    debug_assert!(pre <= 0);

                    // Rewrite `pre`:
                    // -5 => 7
                    // -4 => 6
                    // -3 => 5
                    // -2 => 4
                    // -1 => 3
                    //  0 => 2
                    let pre = 2 + pre.unsigned_abs() as usize;

                    // `pre` = 2 + abs([-5, 0])
                    //       = [2, 2] + abs([-5, 0])
                    //       = [2, 2] + [0, 5]
                    //       = [2, 7]
                    debug_assert!(pre <= 7);
                    debug_assert!(pre >= 2);

                    pre
                };

                const PREFIX: &[u8; 8] = b"-0.00000";
                const_assert!(PREFIX.len() + $name::DIGITS as usize <= $crate::conv::Buffer::len());
                $crate::util::copy(dst, PREFIX);

                // `pre` = [2, 7]
                // `i` = 1 + `pre`
                //     = 1 + [2, 7]
                //     = [3, 8]
                let mut i = 1 + pre;
                let (_, rest) = dst.split_at_mut(i);
                // Use `min(rest, coeff)` to avoid an unnecessary
                // bounds check.
                //
                // The compiler knows that
                //
                // - `i` = [3, 8]
                // - `dst.len()` = 48
                // - `coeff.len()` = [1, DIGITS]
                // - DIGITS < `dst.len()`
                //
                // but for some reason it doesn't know that
                // `rest.len()` = [40, 45]. All it knows is that
                // `rest.len() > 0`.
                let n = ::core::cmp::min(rest.len(), coeff.len());
                i += $crate::util::copy(&mut rest[..n], &coeff[..n]);

                let start = usize::from(self.is_sign_positive());
                // SAFETY: We wrote to `dst[..i]`.
                let buf = unsafe { $crate::util::slice_assume_init_ref(&dst[start..i]) };
                // SAFETY: We only write UTF-8 to `dst`.
                unsafe { str::from_utf8_unchecked(buf) }
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
                let sign = u8::from(self.signbit());
                if self.is_nan() {
                    write!(f, "[{sign},")?;
                    if self.is_snan() {
                        write!(f, "s")?;
                    } else {
                        write!(f, "q")?;
                    }
                    write!(f, "NaN")?;
                    if self.payload() != 0 {
                        write!(f, ",{}", self.payload())?;
                    }
                    write!(f, "]")
                } else if self.is_infinite() {
                    write!(f, "[{sign},inf]")
                } else {
                    write!(
                        f,
                        "[{sign},{},{},form={}]",
                        self.coeff(),
                        self.unbiased_exp(),
                        u8::from(self.is_form2()) + 1,
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
