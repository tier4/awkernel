#[inline(always)]
pub fn get_flag() -> usize {
    awkernel_aarch64::daif::get() as usize
}

#[inline(always)]
pub fn disable() {
    unsafe { core::arch::asm!("msr daifset, #0b0010",) };
}

#[inline(always)]
pub fn set_flag(flag: usize) {
    unsafe { awkernel_aarch64::daif::set(flag as u64) };
}
