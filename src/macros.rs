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
pub(crate) use forward_ref_unop;

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
pub(crate) use forward_ref_binop;

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
pub(crate) use forward_ref_op_assign;

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

        $crate::macros::forward_ref_binop! { impl Add, add for $t, $t }
    )*)
}
pub(crate) use add_impl;

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

        $crate::macros::forward_ref_binop! { impl Sub, sub for $t, $t }
    )*)
}
pub(crate) use sub_impl;

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

        $crate::macros::forward_ref_binop! { impl Mul, mul for $t, $t }
    )*)
}
pub(crate) use mul_impl;

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

        $crate::macros::forward_ref_binop! { impl Div, div for $t, $t }
    )*)*)
}
pub(crate) use div_impl_integer;

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

        $crate::macros::forward_ref_binop! { impl Rem, rem for $t, $t }
    )*)*)
}
pub(crate) use rem_impl_integer;

macro_rules! neg_impl {
    ($($t:ty)*) => ($(
        impl ::core::ops::Neg for $t {
            type Output = $t;

            #[inline]
            fn neg(self) -> $t {
                self.const_neg()
            }
        }

        $crate::macros::forward_ref_unop! { impl Neg, neg for $t }
    )*)
}
pub(crate) use neg_impl;

macro_rules! add_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::AddAssign for $t {
            #[inline]
            #[track_caller]
            fn add_assign(&mut self, other: $t) {
                *self = *self + other;
            }
        }

        $crate::macros::forward_ref_op_assign! { impl AddAssign, add_assign for $t, $t }
    )+)
}
pub(crate) use add_assign_impl;

macro_rules! sub_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::SubAssign for $t {
            #[inline]
            #[track_caller]
            fn sub_assign(&mut self, other: $t) {
                *self = *self - other;
            }
        }

        $crate::macros::forward_ref_op_assign! { impl SubAssign, sub_assign for $t, $t }
    )+)
}
pub(crate) use sub_assign_impl;

macro_rules! mul_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::MulAssign for $t {
            #[inline]
            #[track_caller]
            fn mul_assign(&mut self, other: $t) {
                *self = *self * other;
            }
        }

        $crate::macros::forward_ref_op_assign! { impl MulAssign, mul_assign for $t, $t }
    )+)
}
pub(crate) use mul_assign_impl;

macro_rules! div_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::DivAssign for $t {
            #[inline]
            #[track_caller]
            fn div_assign(&mut self, other: $t) {
                *self = *self / other;
            }
        }

        $crate::macros::forward_ref_op_assign! { impl DivAssign, div_assign for $t, $t }
    )+)
}
pub(crate) use div_assign_impl;

macro_rules! rem_assign_impl {
    ($($t:ty)+) => ($(
        impl ::core::ops::RemAssign for $t {
            #[inline]
            #[track_caller]
            fn rem_assign(&mut self, other: $t) {
                *self = *self % other;
            }
        }

        $crate::macros::forward_ref_op_assign! { impl RemAssign, rem_assign for $t, $t }
    )+)
}
pub(crate) use rem_assign_impl;
