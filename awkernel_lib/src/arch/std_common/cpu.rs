use core::ptr::{read_volatile, write_volatile};

use crate::cpu::CPU;

#[thread_local]
pub static mut CPU_ID: usize = 0;

pub(crate) struct ArchCPU;

impl CPU for ArchCPU {
    fn cpu_id() -> usize {
        unsafe { read_volatile(&CPU_ID) }
    }
}

pub(super) fn init(cpu_id: usize) {
    unsafe { write_volatile(&mut CPU_ID, cpu_id) };
}
