use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

use crate::ntp::{Ntp, SystemTime};

impl Ntp for super::StdCommon {
    /// Get time in microseconds.
    fn get_time() -> SystemTime {
        let mut tp = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut tp) };
        let t = tp.tv_sec as u128 * 1_000_000_000 + tp.tv_nsec as u128;

        SystemTime::new(t)
    }

    fn set_time(new: u64) {}

    fn adjust_time(_offset: SignedDuration) {}
}
