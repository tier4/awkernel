use core::sync::atomic::{AtomicUsize, Ordering};

use crate::cpu::CPU;

#[thread_local]
pub static CPU_ID: AtomicUsize = AtomicUsize::new(0);

impl CPU for super::StdCommon {
    fn cpu_id() -> usize {
        CPU_ID.load(Ordering::Relaxed)
    }
}

pub(super) fn init(cpu_id: usize) {
    CPU_ID.store(cpu_id, Ordering::Relaxed);
}
