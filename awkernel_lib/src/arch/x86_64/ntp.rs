use core::time::Duration;

use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

use crate::{
    delay,
    ntp::{Ntp, SignedDuration, SystemTime},
};

/// The time offset from the Unix epoch in nanoseconds.
static TIME_BASE: Mutex<u128> = Mutex::new(1004572800_000_000_000); // 2001-11-01

impl Ntp for super::X86 {
    fn get_time() -> SystemTime {
        let up = delay::uptime();
        let mut node = MCSNode::new();
        let guard = TIME_BASE.lock(&mut node);
        let syst = SystemTime::new(*guard as u128);
        syst + Duration::from_micros(up)
    }

    fn set_time(new: u128) {
        let mut node = MCSNode::new();
        let mut guard = TIME_BASE.lock(&mut node);
        let up = delay::uptime() as u128 * 1000;
        *guard = new - up;
    }

    fn adjust_time(offset: SignedDuration) {
        let mut node = MCSNode::new();
        let mut guard = TIME_BASE.lock(&mut node);

        let offset = offset.as_nanos();
        if offset > 0 {
            *guard = guard.wrapping_add(offset as u128);
        } else {
            *guard = guard.wrapping_sub(-offset as u128);
        }
    }
}
