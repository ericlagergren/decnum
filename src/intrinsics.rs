#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    target_feature = "bmi2"
))]
#[target_feature(enable = "bmi2")]
pub(super) unsafe fn pext32(mask: u32, b: u32) -> u32 {
    let mut a = 0;
    unsafe {
        core::arch::asm! (
            "pextl {a}, {b}, {mask}",
            mask = in(reg) mask,
            b = in(reg) b,
            a = in(reg) a,
        );
    }
    a
}
