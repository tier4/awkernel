use super::ArchImpl;
use crate::interrupt::Interrupt;
use riscv::register::mstatus;

impl Interrupt for ArchImpl {
    #[inline]
    fn get_flag() -> usize {
        let mie_mask = 0x08;
        mstatus::read().bits() & mie_mask
    }
    #[inline]
    fn disable() {
        unsafe { mstatus::clear_mie() };
    }
    #[inline]
    fn enable() {
        unsafe { mstatus::set_mie() };
    }
    #[inline]
    fn are_enabled() -> bool {
        mstatus::read().mie()
    }
    #[inline]
    fn set_flag(flag: usize) {
        if flag & 0x08 > 0 {
            Self::enable();
        } else {
            Self::disable();
        }
    }
}
