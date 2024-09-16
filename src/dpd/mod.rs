//! IEEE 754-2008 decimal floating point numbers with densely
//! packed decimal significands.

mod bcd;
mod encoding;
mod macros;
mod tables;

pub(crate) use encoding::*;

macros::impl_dpd! {
    /// A 128-bit decimal floating point number using densely
    /// packed decimal encoding.
    name = Dpd128,
    ucoeff = u128,
    icoeff = i128,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u32,
    pack = pack_bin_u113,
    unpack = unpack_bin_u113,
    bid = crate::bid::Bid128,
}

macros::impl_dpd! {
    /// A 64-bit decimal floating point number using densely
    /// packed decimal encoding.
    name = Dpd64,
    ucoeff = u64,
    icoeff = i64,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u32,
    pack = pack_bin_u53,
    unpack = unpack_bin_u53,
    bid = crate::bid::Bid64,
}

macros::impl_dpd! {
    /// A 32-bit decimal floating point number using densely
    /// packed decimal encoding.
    name = Dpd32,
    ucoeff = u32,
    icoeff = i32,
    biased_exp = u16,
    unbiased_exp = i16,
    comb = u32,
    pack = pack_bin_u23,
    unpack = unpack_bin_u23,
    bid = crate::bid::Bid32,
}
