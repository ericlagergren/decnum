//! TODO

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

pub use bid::{Bid128, Bid128 as d128};
pub use conv::*;
pub use ctx::*;
pub use dpd::Dpd128;
