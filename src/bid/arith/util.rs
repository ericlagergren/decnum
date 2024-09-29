/// Returns `floor(5 * 10^n)`.
pub(super) const fn point5(n: u32) -> u128 {
    #[allow(
        clippy::indexing_slicing,
        reason = "This is a const initializer, so panicking is okay."
    )]
    const POW5: [u128; 39] = {
        let mut table = [0; 39];
        let mut i = 1;
        table[0] = 0;
        while i < table.len() {
            table[i] = 5 * u128::pow(10, (i - 1) as u32);
            i += 1;
        }
        table
    };

    #[allow(
        clippy::indexing_slicing,
        reason = "Calling code always checks that `n` is in range"
    )]
    POW5[n as usize]
}
