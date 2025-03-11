use core::time::Duration;

use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

use crate::{
    delay,
    ntp::{Ntp, SystemTime},
};

static time_base: Mutex<u64> = Mutex::new(1004572800000); // 2001-11-01

impl Ntp for super::X86 {
    fn get_time() -> SystemTime {
        let up = delay::uptime();
        let mut node = MCSNode::new();
        let guard = time_base.lock(&mut node);
        let syst = SystemTime::new(*guard as u128);
        syst + Duration::from_micros(up)
    }

    fn set_time(new: u64) {}

    fn sync_time() {}
}
