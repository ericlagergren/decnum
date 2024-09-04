macro_rules! impl_atod {
    ($name:ident, $ucoeff:ty, $unbiased:ty, $arith:ident) => {
        impl $name {
            /// Parses a decimal from a string.
            pub fn parse(s: &str) -> Result<Self, ParseError> {
                let mut s = s.as_bytes();
                if s.is_empty() {
                    return Err(ParseError::empty());
                }

                let mut sign = false;
                if let Some((c @ (b'-' | b'+'), rest)) = s.split_first() {
                    sign = *c == b'-';
                    s = rest;
                }

                match s.first() {
                    Some(b'0'..=b'9') => {}
                    Some(b'i' | b'I' | b'n' | b'N' | b's' | b'S') => {
                        return Self::parse_special(sign, s)
                    }
                    Some(_) => return Err(ParseError::invalid("expected digit or special")),
                    None => return Err(ParseError::invalid("unexpected end of input")),
                }

                let (coeff, sd, s) = match Self::parse_coeff(s) {
                    Ok((c, e, r)) => (c, e, r),
                    Err(err) => return Err(err),
                };
                if cfg!(debug_assertions) {
                    println!("coeff = {coeff}");
                    println!("  dot = {sd:?}");
                    println!("    s = \"{}\"", str::from_utf8(s).unwrap());
                }
                let exp = match Self::parse_exp(s) {
                    // If the decimal-part included a decimal
                    // point the exponent is then reduced by the
                    // count of digits following the decimal
                    // point (which may be zero) and the decimal
                    // point is removed.
                    //
                    // https://speleotrove.com/decimal/daconvs.html#reftonum
                    Ok(exp) => exp - sd as $unbiased,
                    Err(err) => return Err(err),
                };
                if cfg!(debug_assertions) {
                    println!("  exp = {exp}");
                }

                if !Self::need_round(coeff, exp) {
                    Ok(Self::from_parts(sign, exp, coeff))
                } else {
                    Ok(Self::rounded2(sign, exp, coeff))
                }
            }

            /// Parses the coefficient.
            ///
            /// It returns the coefficient, number of digits
            /// after the decimal point, and unused remainder of
            /// the input.
            fn parse_coeff(s: &[u8]) -> Result<($ucoeff, usize, &[u8]), ParseError> {
                debug_assert!(!s.is_empty());

                if cfg!(debug_assertions) {
                    println!("parse_coeff = {}", str::from_utf8(s).unwrap());
                }

                /// Parses digits from `s` and adds them to `x`,
                /// stopping at the first non-digit.
                ///
                /// It returns the parsed digits, the unparsed
                /// digits, and the updated `x` in that order.
                const fn parse_digits(s: &[u8], mut x: $ucoeff) -> (&[u8], &[u8], $ucoeff) {
                    let mut lhs: &[u8] = &[];
                    let mut rhs: &[u8] = s;
                    let mut tmp = s;
                    let mut i = 0;
                    while let Some((c @ (b'0'..=b'9'), rest)) = tmp.split_first() {
                        // It's okay if `x` overflows. The caller
                        // is responsible for checking.
                        let d = (*c - b'0') as $ucoeff;
                        x = x * 10 + d;
                        (lhs, rhs) = s.split_at(i + 1);
                        i += 1;
                        tmp = rest;
                    }
                    (lhs, rhs, x)
                }

                let (pre, rest, coeff) = parse_digits(s, 0);
                let (post, rest, coeff): (&[u8], &[u8], $ucoeff) =
                    if let Some((&b'.', rest)) = rest.split_first() {
                        parse_digits(rest, coeff)
                    } else {
                        (&[], rest, coeff)
                    };

                // `rest` should not start with a digit.
                debug_assert!(!matches!(rest.first(), Some(&(b'0'..=b'9'))));

                if cfg!(debug_assertions) {
                    println!(" pre = {pre:?} {}", str::from_utf8(pre).unwrap());
                    println!("post = {post:?} {}", str::from_utf8(post).unwrap());
                    println!("rest = {rest:?} {}", str::from_utf8(rest).unwrap());
                }

                // Number of significant digits. Make sure to
                // collect this before we start trimming zeros.
                let sd = post.len();

                let mut digits = pre.len() + post.len();
                if digits > Self::DIGITS as usize {
                    // Uncommon case: too many digits to know
                    // whether `coeff` overflowed. Maybe we have
                    // leading zeros?
                    let mut tmp = match s.split_at_checked(digits) {
                        Some((s, _)) => s,
                        // NB: This case is impossible since
                        //   s = pre || post || rest
                        //   s = pre || '.' || post || rest
                        // but the compiler doesn't understand
                        // this.
                        None => &[],
                    };
                    while let Some((b'0' | b'.', rest)) = tmp.split_first() {
                        digits -= 1;
                        tmp = rest;
                    }
                }

                // Common case fast path: we had a reasonable
                // number of digits and did not overflow `coeff`.
                // Limit to N-1 since (10^digits)-1 is probably
                // larger than $ucoeff::MAX.
                const MAX_DIGITS: u32 = $arith::digits(<$ucoeff>::MAX) - 1;
                if digits <= MAX_DIGITS as usize {
                    return Ok((coeff, sd, rest));
                }

                // Slow and (hopefully) uncommon path: we
                // overflowed `coeff`.
                let (coeff, dropped) = Self::parse_large_coeff(pre, post);
                Ok((coeff, sd + dropped, rest))
            }

            /// Parses a coefficient with too many digits.
            ///
            /// - `pre` is the coefficient before the dot.
            /// - `post` is the coefficient after the dot.
            ///
            /// The coefficient does not have any leading zeros.
            #[cold]
            fn parse_large_coeff<'a>(pre: &'a [u8], mut post: &'a [u8]) -> ($ucoeff, usize) {
                debug_assert!(pre.len() + post.len() > Self::DIGITS as usize);
                util::debug_assert_all_digits(pre);
                util::debug_assert_all_digits(post);

                // Partition (pre, post) so that `pre || post` is
                // at most N+1 digits. We only need one extra
                // digit to round.
                const MAX_DIGITS: usize = ($name::DIGITS + 1) as usize;

                let (mut pre, mut dropped) = match pre.split_at_checked(MAX_DIGITS) {
                    Some((pre, rest)) => (pre, rest.len()),
                    None => (pre, 0),
                };
                if pre.len() < MAX_DIGITS {
                    // Need some digits from `post`, too.
                    (post, dropped) = match post.split_at_checked(MAX_DIGITS - post.len()) {
                        Some((post, rest)) => (post, rest.len()),
                        None => (post, 0),
                    };
                }
                debug_assert!(pre.len() + post.len() == MAX_DIGITS);
                if cfg!(debug_assertions) {
                    println!("pre={} post={} dropped={dropped}", pre.len(), post.len());
                }

                let mut coeff = 0;
                while let Some((&c, rest)) = pre.split_first() {
                    let d = (c - b'0') as $ucoeff;
                    coeff = coeff * 10 + d;
                    pre = rest;
                }
                while let Some((&c, rest)) = post.split_first() {
                    let d = (c - b'0') as $ucoeff;
                    coeff = coeff * 10 + d;
                    post = rest;
                }
                (coeff, dropped)
            }

            const fn parse_exp(mut s: &[u8]) -> Result<$unbiased, ParseError> {
                if s.is_empty() {
                    return Ok(0);
                }

                if let Some((b'e' | b'E', rest)) = s.split_first() {
                    s = rest;
                } else {
                    return Err(ParseError::invalid("expected `e` or `E`"));
                }

                let mut sign = false;
                if let Some((c @ (b'-' | b'+'), rest)) = s.split_first() {
                    sign = *c == b'-';
                    s = rest;
                }

                let mut exp: $unbiased = 0;
                while let Some((&c, rest)) = s.split_first() {
                    let d = c.wrapping_sub(b'0');
                    if d >= 10 {
                        return Err(ParseError::invalid("expected digit"));
                    }
                    exp = match exp.checked_mul(10) {
                        Some(exp) => exp,
                        None => return Err(ParseError::invalid("exp overflow")),
                    };
                    exp = match exp.checked_add(d as $unbiased) {
                        Some(exp) => exp,
                        None => return Err(ParseError::invalid("exp overflow")),
                    };
                    s = rest;
                }
                if sign {
                    exp = -exp;
                }
                Ok(exp)
            }

            /// Parses a special from `s`.
            ///
            /// The sign has already been parsed.
            const fn parse_special(sign: bool, s: &[u8]) -> Result<Self, ParseError> {
                if s.len() > "snan".len() + Self::PAYLOAD_DIGITS as usize {
                    return Err(ParseError::invalid("unknown special"));
                }
                if conv::equal_fold_ascii(s, b"inf") || conv::equal_fold_ascii(s, b"infinity") {
                    return Ok(Self::inf(sign));
                }

                const fn atoi(mut s: &[u8]) -> Result<$ucoeff, ParseError> {
                    let mut n: $ucoeff = 0;
                    while let Some((&c, rest)) = s.split_first() {
                        let d = c.wrapping_sub(b'0');
                        if d >= 10 {
                            return Err(ParseError::invalid("expected digit"));
                        }
                        n = match n.checked_mul(10) {
                            Some(n) => n,
                            None => return Err(ParseError::invalid("payload overflow")),
                        };
                        n = match n.checked_add(d as $ucoeff) {
                            Some(n) => n,
                            None => return Err(ParseError::invalid("payload overflow")),
                        };
                        s = rest;
                    }
                    Ok(n)
                }

                if let Some((chunk, rest)) = s.split_first_chunk::<4>() {
                    if conv::equal_fold_ascii(chunk, b"snan") {
                        return match atoi(rest) {
                            Ok(payload) => Ok(Self::snan(sign, payload)),
                            Err(err) => Err(err),
                        };
                    }
                }

                if let Some((chunk, rest)) = s.split_first_chunk::<3>() {
                    if conv::equal_fold_ascii(chunk, b"nan") {
                        return match atoi(rest) {
                            Ok(payload) => Ok(Self::nan(sign, payload)),
                            Err(err) => Err(err),
                        };
                    }
                }

                Err(ParseError::invalid("unknown special"))
            }
        }

        impl ::core::str::FromStr for $name {
            type Err = $crate::conv::ParseError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $name::parse(s)
            }
        }
    };
}
pub(crate) use impl_atod;
