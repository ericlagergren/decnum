//! IEEE 754-2008 decimal floating point numbers with densely
//! packed decimal significands.

mod bcd;
mod dpd;
mod dpd128;
mod tables;

pub use dpd128::Dpd128;
