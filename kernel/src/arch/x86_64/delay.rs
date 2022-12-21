use crate::delay::Delay;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        super::acpi::wait_usec(usec);
    }
}
