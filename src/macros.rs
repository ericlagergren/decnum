use super::uint96::u96;

// implements the unary operator "op &T"
// based on "op T" where T is expected to be `Copy`able
macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        impl ::core::ops::$imp for &$t {
            type Output = <$t as ::core::ops::$imp>::Output;

            #[inline]
            fn $method(self) -> <$t as ::core::ops::$imp>::Output {
                ::core::ops::$imp::$method(*self)
            }
        }
    };
}

// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are expected to be `Copy`able
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> ::core::ops::$imp<$u> for &'a $t {
            type Output = <$t as ::core::ops::$imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: $u) -> <$t as ::core::ops::$imp<$u>>::Output {
                ::core::ops::$imp::$method(*self, other)
            }
        }

        impl ::core::ops::$imp<&$u> for $t {
            type Output = <$t as ::core::ops::$imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: &$u) -> <$t as ::core::ops::$imp<$u>>::Output {
                ::core::ops::$imp::$method(self, *other)
            }
        }

        impl ::core::ops::$imp<&$u> for &$t {
            type Output = <$t as ::core::ops::$imp<$u>>::Output;

            #[inline]
            #[track_caller]
            fn $method(self, other: &$u) -> <$t as ::core::ops::$imp<$u>>::Output {
                ::core::ops::$imp::$method(*self, *other)
            }
        }
    };
}

// implements "T op= &U", based on "T op= U"
// where U is expected to be `Copy`able
macro_rules! forward_ref_op_assign {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl ::core::ops::$imp<&$u> for $t {
            #[inline]
            #[track_caller]
            fn $method(&mut self, other: &$u) {
                ::core::ops::$imp::$method(self, *other);
            }
        }
    };
}

macro_rules! add_impl {
    ($($t:ty)*) => ($(
        impl ::core::ops::Add for $t {
            type Output = $t;

            #[inline]
            #[track_caller]
            fn add(self, other: $t) -> $t {
                self.const_add(other)
            }
        }

        forward_ref_binop! { impl Add, add for $t, $t }
    )*)
}

add_impl! { u96}

macro_rules! sub_impl {
    ($($t:ty)*) => ($(
        impl ::core::ops::Sub for $t {
            type Output = $t;

            #[inline]
            #[track_caller]
            fn sub(self, other: $t) -> $t {
                self.const_sub(other)
            }
        }

        forward_ref_binop! { impl Sub, sub for $t, $t }
    )*)
}

sub_impl! { u96}

macro_rules! mul_impl {
    ($($t:ty)*) => ($(
        impl ::core::ops::Mul for $t {
            type Output = $t;

            #[inline]
            #[track_caller]
            fn mul(self, other: $t) -> $t {
                self.const_mul(other)
            }
        }

        forward_ref_binop! { impl Mul, mul for $t, $t }
    )*)
}

mul_impl! { u96}

macro_rules! div_impl_integer {
    ($(($($t:ty)*) => $panic:expr),*) => ($($(
        /// This operation rounds towards zero, truncating any
        /// fractional part of the exact result.
        ///
        /// # Panics
        ///
        #[doc = $panic]
        impl ::core::ops::Div for $t {
            type Output = $t;

            #[inline]
            #[track_caller]
            fn div(self, other: $t) -> $t {
                self.const_div(other)
            }
        }

        forward_ref_binop! { impl Div, div for $t, $t }
    )*)*)
}

div_impl_integer!((u96) => "This operation will panic if `other == 0`.");

macro_rules! rem_impl_integer {
    ($(($($t:ty)*) => $panic:expr),*) => ($($(
        /// This operation satisfies `n % d == n - (n / d) * d`. The
        /// result has the same sign as the left operand.
        ///
        /// # Panics
        ///
        #[doc = $panic]
        impl ::core::ops::Rem for $t {
            type Output = $t;

            #[inline]
            #[track_caller]
            fn rem(self, other: $t) -> $t {
                self.const_rem(other)
            }
        }

        forward_ref_binop! { impl Rem, rem for $t, $t }
    )*)*)
}

rem_impl_integer!((u96) => "This operation will panic if `other == 0`.");

macro_rules! neg_impl {
    ($($t:ty)*) => ($(
        impl ::core::ops::Neg for $t {
            type Output = $t;

            #[inline]
            fn neg(self) -> $t {
                self.const_neg()
            }
        }

        forward_ref_unop! { impl Neg, neg for $t }
    )*)
}

neg_impl! { u96}

macro_rules! add_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::AddAssign for $t {
            #[inline]
            #[track_caller]
            fn add_assign(&mut self, other: $t) {
                *self = *self + other;
            }
        }

        forward_ref_op_assign! { impl AddAssign, add_assign for $t, $t }
    )+)
}

add_assign_impl! { u96 }

macro_rules! sub_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::SubAssign for $t {
            #[inline]
            #[track_caller]
            fn sub_assign(&mut self, other: $t) {
                *self = *self - other;
            }
        }

        forward_ref_op_assign! { impl SubAssign, sub_assign for $t, $t }
    )+)
}

sub_assign_impl! { u96 }

macro_rules! mul_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::MulAssign for $t {
            #[inline]
            #[track_caller]
            fn mul_assign(&mut self, other: $t) {
                *self = *self * other;
            }
        }

        forward_ref_op_assign! { impl MulAssign, mul_assign for $t, $t }
    )+)
}

mul_assign_impl! { u96 }

macro_rules! div_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::DivAssign for $t {
            #[inline]
            #[track_caller]
            fn div_assign(&mut self, other: $t) {
                *self = *self / other;
            }
        }

        forward_ref_op_assign! { impl DivAssign, div_assign for $t, $t }
    )+)
}

div_assign_impl! { u96 }

macro_rules! rem_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::RemAssign for $t {
            #[inline]
            #[track_caller]
            fn rem_assign(&mut self, other: $t) {
                *self = *self % other;
            }
        }

        forward_ref_op_assign! { impl RemAssign, rem_assign for $t, $t }
    )+)
}

rem_assign_impl! { u96 }
