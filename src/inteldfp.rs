#![cfg(test)]

use inteldfp as dfp;

use crate::bid::{Bid128, Bid32, Bid64};

macro_rules! trait_impls {
    ($lhs:ty, $rhs:ty) => {
        impl PartialEq<$lhs> for $rhs {
            fn eq(&self, other: &$lhs) -> bool {
                self.to_bits() == other.to_bits()
            }
        }
        impl PartialEq<$rhs> for $lhs {
            fn eq(&self, other: &$rhs) -> bool {
                other == self
            }
        }
    };
}
trait_impls!(Bid32, dfp::Bid32);
trait_impls!(Bid64, dfp::Bid64);
trait_impls!(Bid128, dfp::Bid128);
