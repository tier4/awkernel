use crate::delay::Delay;
use core::{ffi::c_uint, ptr::read_volatile};

static mut TIME_START: libc::timespec = libc::timespec {
    tv_sec: 0,
    tv_nsec: 0,
};

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {}

    fn wait_microsec(usec: u64) {
        let tv_sec = usec as i64 / 1000_000;
        let usec = usec as i64 - (tv_sec * 1000_000);

        let mut req = libc::timespec {
            tv_sec,
            tv_nsec: usec * 1000,
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

    fn uptime() -> u64 {
        let mut tp = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut tp) };

        let t0 = unsafe { read_volatile(&TIME_START.tv_sec) as u64 } * 1000_000
            + unsafe { read_volatile(&TIME_START.tv_nsec) as u64 } / 1000;
        let t1 = tp.tv_sec as u64 * 1000_000 + tp.tv_nsec as u64 / 1000;

        if t0 == 0 {
            0
        } else {
            t1 - t0
        }
    }
}

pub fn init() {
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut TIME_START) };
}
