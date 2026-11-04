//! M-mode trap handling for RV64.

use core::arch::global_asm;

global_asm!(include_str!("trap.S"));

const MCAUSE_CODE_MASK: usize = !(1 << (usize::BITS - 1));

const MACHINE_SOFTWARE_INTERRUPT: usize = 3;
const MACHINE_TIMER_INTERRUPT: usize = 7;
const MACHINE_EXTERNAL_INTERRUPT: usize = 11;

/// Called from `rv64_trap_entry` when `mcause` indicates an interrupt.
#[no_mangle]
extern "C" fn riscv_handle_interrupt(mcause: usize) {
    match mcause & MCAUSE_CODE_MASK {
        MACHINE_SOFTWARE_INTERRUPT | MACHINE_TIMER_INTERRUPT | MACHINE_EXTERNAL_INTERRUPT => {
            awkernel_lib::interrupt::handle_irqs(true);
        }
        code => log::warn!("unexpected interrupt: mcause code = {code}"),
    }
}

/// Called from `rv64_trap_entry` when `mcause` indicates an exception.
#[no_mangle]
extern "C" fn riscv_handle_exception(mcause: usize, mepc: usize, mtval: usize) -> ! {
    panic!("unhandled exception: mcause = {mcause:#x}, mepc = {mepc:#x}, mtval = {mtval:#x}");
}
