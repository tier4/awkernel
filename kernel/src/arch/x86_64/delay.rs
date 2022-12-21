use super::acpi::{get_pm_timer_max, read_pm_timer, ACPI_TMR_HZ};
use crate::delay::Delay;
use synctools::mcs::{MCSLock, MCSNode};

struct Counter {
    start: u64,
    prev: u64,
    overflow: u64,
}

static COUNTER: MCSLock<Counter> = MCSLock::new(Counter {
    start: 0,
    prev: 0,
    overflow: 0,
});

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        super::acpi::wait_usec(usec);
    }

    fn uptime() -> u64 {
        let Some(max) = get_pm_timer_max() else { return 0 };

        let mut node = MCSNode::new();
        let guard = COUNTER.lock(&mut node);

        let diff = {
            let count = max * guard.overflow;
            let count = count + guard.prev;
            count - guard.start
        };

        diff * 1000_000 / ACPI_TMR_HZ as u64
    }

    fn tick() {
        let count = read_pm_timer().unwrap();

        let mut node = MCSNode::new();
        let mut guard = COUNTER.lock(&mut node);

        if count < guard.prev {
            guard.overflow += 1;
        }

        guard.prev = count;
    }
}

pub(super) fn init() {
    let count = read_pm_timer().unwrap();
    let mut node = MCSNode::new();
    let mut guard = COUNTER.lock(&mut node);

    guard.prev = count;
    guard.start = count;
}
