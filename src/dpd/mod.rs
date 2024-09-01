//! IEEE 754-2008 decimal floating point numbers with densely
//! packed decimal significands.

mod bcd;
mod dpd128;
mod encoding;
mod tables;

pub use dpd128::Dpd128;
pub(crate) use encoding::*;
