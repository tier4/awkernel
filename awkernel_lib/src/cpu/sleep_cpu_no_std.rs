use crate::delay::wait_microsec;

use super::SleepCpu;

pub(super) struct SleepCpuNoStd;

impl SleepCpu for SleepCpuNoStd {
    fn sleep(&self) {
        // TODO
        wait_microsec(10);
    }

    fn wake_up(_cpu_id: usize) -> bool {
        // TODO
        true
    }
}
