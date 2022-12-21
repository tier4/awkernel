use crate::delay::Delay;
use core::ffi::c_uint;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {}

    fn wait_microsec(usec: u64) {
        let tv_sec = usec as i64 / 1000_000;
        let usec = usec as i64 - (tv_sec * 1000_000);

        let mut req = libc::timespec {
            tv_sec,
            tv_nsec: usec / 1000,
        };
        let mut rem = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };

        loop {
            let result = unsafe { libc::nanosleep(&req, &mut rem) };
            if result == -1 {
                let errno = unsafe { *libc::__errno_location() };
                if errno == libc::EINTR {
                    req = rem;
                } else {
                    log::error!("failed nanosleep: {errno}",)
                }
            } else {
                break;
            }
        }
    }

    fn wait_forever() -> ! {
        loop {
            unsafe { libc::sleep(c_uint::MAX) };
        }
    }
}
