use crate::interrupt::Interrupt;

pub struct ArchInterrupt;

impl Interrupt for ArchInterrupt {
    fn get_flag() -> usize {
        if x86_64::instructions::interrupts::are_enabled() {
            1
        } else {
            0
        }
    }

    fn disable() {
        x86_64::instructions::interrupts::disable();
    }

    fn enable() {
        x86_64::instructions::interrupts::enable();
    }

    fn set_flag(flag: usize) {
        if flag == 0 {
            x86_64::instructions::interrupts::disable();
        } else {
            x86_64::instructions::interrupts::enable();
        }
    }
}
