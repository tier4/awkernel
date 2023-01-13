use crate::arch::ArchDelay;

impl ArchDelay where ArchDelay: Delay {}

pub trait Delay {
    fn wait_interrupt();

    fn wait_microsec(usec: u64);

    fn wait_forever() -> ! {
        loop {
            Self::wait_interrupt();
        }
    }

    fn wait_millisec(msec: u64) {
        assert!(msec < u64::MAX / 1000);
        Self::wait_microsec(msec * 1000);
    }

    fn wait_sec(sec: u64) {
        assert!(sec < u64::MAX / 1000_000);
        Self::wait_microsec(sec * 1000 * 1000);
    }

    /// Return microseconds.
    fn uptime() -> u64;

    fn cpu_counter() -> u64;

    fn pause() {
        core::hint::spin_loop();
    }
}

pub fn wait_interrupt() {
    ArchDelay::wait_interrupt();
}

pub fn wait_microsec(usec: u64) {
    ArchDelay::wait_microsec(usec);
}

pub fn wait_millisec(msec: u64) {
    ArchDelay::wait_millisec(msec);
}

pub fn wait_sec(sec: u64) {
    ArchDelay::wait_sec(sec);
}

pub fn wait_forever() -> ! {
    ArchDelay::wait_forever()
}

/// Microseconds.
pub fn uptime() -> u64 {
    ArchDelay::uptime()
}

pub fn pause() {
    ArchDelay::pause();
}

pub fn cpu_counter() -> u64 {
    ArchDelay::cpu_counter()
}
