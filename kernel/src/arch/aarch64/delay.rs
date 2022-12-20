use crate::arch::Delay;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_event() {
        unsafe { core::arch::asm!("wfe") };
    }
}
