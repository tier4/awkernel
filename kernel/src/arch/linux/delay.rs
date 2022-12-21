use crate::delay::Delay;
use core::ffi::c_uint;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {}

    fn wait_microsec(usec: u32) {
        unsafe { libc::usleep(usec as c_uint) };
    }

    fn wait_forever() -> ! {
        loop {
            Self::wait_microsec(u32::MAX);
        }
    }
}
