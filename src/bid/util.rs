use core::cmp::Ordering;

pub(crate) const fn const_cmp_u8(lhs: u8, rhs: u8) -> Ordering {
    match lhs.checked_sub(rhs) {
        Some(0) => Ordering::Equal,
        Some(_) => Ordering::Greater,
        None => Ordering::Less,
    }
}
