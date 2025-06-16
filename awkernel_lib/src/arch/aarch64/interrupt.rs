use crate::interrupt::Interrupt;

impl Interrupt for super::AArch64 {
    fn get_flag() -> usize {
        awkernel_aarch64::daif::get() as usize
    }

    fn disable() {
        unsafe { core::arch::asm!("msr daifset, #0b0010",) };
    }

    fn enable() {
        unsafe { core::arch::asm!("msr daifclr, #0b0010",) };
    }

    fn are_enabled() -> bool {
        let daif = awkernel_aarch64::daif::get();
        (daif & (1 << 7)) == 0
    }

    fn set_flag(flag: usize) {
        unsafe { awkernel_aarch64::daif::set(flag as u64) };
    }
}
