//! IEEE 754-2008 decimal floating point numbers with densely
//! packed decimal significands.

mod bcd;
mod dec128;
mod dpd;
mod tables;

pub use dec128::d128;
