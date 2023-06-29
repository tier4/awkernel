use crate::interrupt::Interrupt;

pub struct ArchInterrupt;

impl Interrupt for ArchInterrupt {
    fn get_flag() -> usize {
        awkernel_aarch64::daif::get() as usize
    }

    fn disable() {
        unsafe { core::arch::asm!("msr daifset, #0b0010",) };
    }

    fn enable() {
        unsafe { core::arch::asm!("msr daifclr, #0b0010",) };
    }

    fn set_flag(flag: usize) {
        unsafe { awkernel_aarch64::daif::set(flag as u64) };
    }
}
