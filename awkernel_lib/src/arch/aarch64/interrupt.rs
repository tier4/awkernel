use crate::interrupt::Interrupt;

pub struct ArchInterrupt;

impl Interrupt for ArchInterrupt {
    fn get_flag() -> usize {
        awkernel_aarch64::daif::get() as usize
    }

    fn disable() {
        unsafe {
            awkernel_aarch64::daif::set(awkernel_aarch64::DISABLE_ALL_EXCEPTIONS);
        }
    }

    fn set_flag(flag: usize) {
        unsafe { awkernel_aarch64::daif::set(flag as u64) };
    }
}
