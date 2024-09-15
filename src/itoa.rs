/// A string of length [1, 4].
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
