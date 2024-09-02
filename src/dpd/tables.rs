use super::{
    bcd::{self, Str3},
    encoding as dpd,
};

/// Maps 12-bit BCDs to 10-bit DPDs.
#[allow(clippy::indexing_slicing)]
pub(crate) const BCD_TO_DPD: [u16; 0x999 + 1] = {
    let mut t = [0u16; 0x999 + 1];
    let mut bin = 0;
    while bin <= 999 {
        let bcd = bcd::from_bin(bin);
        let dpd = dpd::pack_via_bits_obvious(bcd);
        t[bcd as usize] = dpd;
        bin += 1;
    }
    t
};

/// Maps 10-bit DPDs to 12-bit BCDs.
#[allow(clippy::indexing_slicing)]
pub(crate) const DPD_TO_BCD: [u16; 1 << 10] = {
    let mut t = [0u16; 1 << 10];
    let mut i = 0;
    while i < t.len() {
        let dpd = i as u16;
        let bcd = dpd::unpack_via_bits(dpd);
        t[i] = bcd;
        i += 1;
    }
    t
};

/// Converts a binary number in [0, 999] to a 10-bit DPD.
#[allow(clippy::indexing_slicing)]
pub(super) const BIN_TO_DPD: [u16; 1000] = {
    let mut t = [0u16; 1000];
    let mut i = 0;
    while i < t.len() {
        let bin = i as u16;
        let bcd = bcd::from_bin(bin);
        let dpd = dpd::pack_via_bits_obvious(bcd);
        t[i] = dpd;
        i += 1;
    }
    t
};

/// Converts a 10-bit DPD to a binary number in [0, 999].
#[allow(clippy::indexing_slicing)]
pub(super) const DPD_TO_BIN: [u16; 1 << 10] = {
    let mut t = [0u16; 1 << 10];
    let mut i = 0;
    while i < t.len() {
        let dpd = i as u16;
        let bcd = dpd::unpack_via_bits(dpd);
        let bin = bcd::to_bin(bcd);
        t[i] = bin;
        i += 1;
    }
    t
};

/// Converts a 10-bit DPD to a three-byte string.
///
/// The high octet contains the number of significant digits in
/// the DPD.
#[allow(clippy::indexing_slicing)]
pub(super) const DPD_TO_STR: [Str3; 1 << 10] = {
    let mut t = [Str3::zero(); 1 << 10];
    let mut i = 0;
    while i < t.len() {
        let dpd = i as u16;
        let s = dpd::unpack_to_str_via_bits(dpd);
        t[i] = s;
        i += 1;
    }
    t
};

#[cfg(test)]
mod tests {
    use super::*;

    // TODO(eric): this isn't a great test; it should test all
    // values in all tables.
    #[test]
    fn test_tables() {
        let mut bin = 0;
        while bin <= 999 {
            let bcd = bcd::from_bin(bin);
            let dpd = dpd::pack_via_bits_obvious(bcd);

            assert_eq!(BCD_TO_DPD[bcd as usize], dpd, "#{bin}");
            assert_eq!(DPD_TO_BCD[dpd as usize], bcd, "#{bin}");
            assert_eq!(BIN_TO_DPD[bin as usize], dpd, "#{bin}");
            assert_eq!(DPD_TO_BIN[dpd as usize], bin, "#{bin}");

            bin += 1;
        }
    }
}
