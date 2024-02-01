use crate::interrupt::Interrupt;

impl Interrupt for super::RV32 {
    fn get_flag() -> usize {
        let x: usize;
        unsafe { core::arch::asm!("csrr {}, mstatus", out(reg) x) };
        x & 0x08
    }

    fn disable() {
        let _x: usize;
        unsafe { core::arch::asm!("csrrc {}, mstatus, 0x08", out(reg) _x) };
    }

    fn enable() {
        let _x: usize;
        unsafe { core::arch::asm!("csrrs {}, mstatus, 0x08", out(reg) _x) };
    }

    fn set_flag(flag: usize) {
        if flag & 0x08 > 0 {
            Self::enable();
        } else {
            Self::disable();
        }
    }
}
