//! `rdfp` is a pure Rust, no-std implementation of IEEE 754-2008
//! decimal floating point numbers.
//!
//! # Features
//!
//! TODO
//!
//! # Cargo Features
//!
//! - `alloc`: Include [`alloc`] support. This is currently
//! unused, but may be used in the future.
//!
//! - `dpd-tables`: Use lookup tables for densely packed decimal
//! conversions.
//!
//! - `rand`: Enable [`rand`] support.
//!
//! - `std`: Include [`std`] support. This is currently
//! unused, but may be used in the future. Implies the `alloc`
//! feature.
//!
//! - `slow-128`: TODO
//!
//! [`alloc`]: https://doc.rust-lang.org/alloc/
//! [`rand`]: https://crates.io/crates/rand
//! [`std`]: https://doc.rust-lang.org/std/

#![allow(dead_code)] // TODO
#![allow(clippy::unusual_byte_groupings)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(any(feature = "std", test)), deny(clippy::std_instead_of_core))]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![deny(clippy::alloc_instead_of_core)]
#![deny(clippy::cast_lossless)]
#![deny(clippy::cast_possible_wrap)]
#![deny(clippy::cast_precision_loss)]
#![deny(clippy::cast_sign_loss)]
#![deny(clippy::expect_used)]
#![deny(clippy::implicit_saturating_sub)]
#![deny(clippy::indexing_slicing)]
#![deny(clippy::missing_panics_doc)]
#![deny(clippy::panic)]
#![deny(clippy::ptr_as_ptr)]
#![deny(clippy::string_slice)]
#![deny(clippy::transmute_ptr_to_ptr)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![deny(clippy::unimplemented)]
#![deny(clippy::unwrap_used)]
#![deny(clippy::wildcard_imports)]
#![deny(missing_docs)]
#![deny(rust_2018_idioms)]
#![deny(unused_lifetimes)]
#![deny(unused_qualifications)]

// #[cfg(feature = "alloc")]
// extern crate alloc;

pub mod bid;
mod conv;
mod ctx;
mod decnumber;
mod dectest;
pub mod dpd;
mod inteldfp;
mod itoa;
mod macros;
mod util;

#[doc(inline)]
#[allow(non_camel_case_types)]
pub use bid::Bid128 as d128;
#[doc(inline)]
#[allow(non_camel_case_types)]
pub use bid::Bid64 as d64;
pub use conv::*;
pub use ctx::*;

/// Simplifies importing common items.
pub mod prelude {
    pub use super::{d128, d64};
}
