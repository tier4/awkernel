use crate::delay::Delay;
use core::{ffi::c_uint, ptr::read_volatile};

static mut TIME_START: libc::timespec = libc::timespec {
    tv_sec: 0,
    tv_nsec: 0,
};

impl Delay for super::StdCommon {
    fn wait_interrupt() {}

    fn wait_microsec(usec: u64) {
        let tv_sec = usec / 1_000_000;
        let usec = usec - (tv_sec * 1_000_000);

        nanosleep(tv_sec, usec * 1000);
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

        let t0 = unsafe { read_volatile(&TIME_START.tv_sec) as u64 } * 1_000_000
            + unsafe { read_volatile(&TIME_START.tv_nsec) as u64 } / 1000;
        let t1 = tp.tv_sec as u64 * 1_000_000 + tp.tv_nsec as u64 / 1000;

        if t0 == 0 {
            0
        } else {
            t1 - t0
        }
    }

    fn pause() {
        nanosleep(0, 100);
    }

    fn cpu_counter() -> u64 {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::x86_64::_rdtsc()
        }

        #[cfg(target_arch = "aarch64")]
        {
            let v: u64;
            unsafe { core::arch::asm!("mrs {}, CNTVCT_EL0", lateout(reg) v) };
            v
        }
    }
}

pub fn init() {
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut TIME_START) };
}

fn nanosleep(sec: u64, nsec: u64) {
    let mut req = libc::timespec {
        tv_sec: sec as i64,
        tv_nsec: nsec as i64,
    };
    let mut rem = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };

    loop {
        let result = unsafe { libc::nanosleep(&req, &mut rem) };
        if result == -1 {
            #[cfg(target_os = "macos")]
            let errno = unsafe { *libc::__error() };

            #[cfg(target_os = "linux")]
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
