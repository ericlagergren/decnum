use core::cmp::Ordering;

pub(super) const fn shl128(_x: u128, _n: u32) -> u128 {
    todo!()
}

pub(super) const fn shr128(_x: u128, _n: u32) -> u128 {
    todo!()
}

pub(super) const fn const_cmp128(lhs: u128, rhs: u128) -> Ordering {
    match lhs.checked_sub(rhs) {
        Some(0) => Ordering::Equal,
        Some(_) => Ordering::Greater,
        None => Ordering::Less,
    }
}
