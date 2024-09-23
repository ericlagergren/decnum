//! IEEE 754-2008 decimal floating point numbers with binary
//! integer significands.
//!
//! # Arithmetic Operation Rules
//!
//! - Every operation is carried out ... TODO
//! - +Infinity is larger than every finite number and -Infinity
//!   is smaller than every finite number.
//! - If any operand is NaN... TODO.

mod arith;
mod atod;
mod base;
mod bid128;
mod bid32;
mod bid64;
mod dtoa;
mod util;

pub use bid128::Bid128;
pub use bid32::Bid32;
pub use bid64::Bid64;

macro_rules! canonical {
    ($bits:expr) => {{
        let x = Self::from_bits($bits);
        debug_assert!(x.is_canonical());
        x
    }};
}
pub(crate) use canonical;
