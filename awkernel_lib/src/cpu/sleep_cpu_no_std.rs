use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

use array_macro::array;
use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

use crate::delay::wait_microsec;

use super::{SleepCpu, NUM_MAX_CPU};

static READY: AtomicBool = AtomicBool::new(false);

static CPU_SLEEP_STATES: [Mutex<SleepState>; NUM_MAX_CPU] =
    array![_ => Mutex::new(SleepState::new()); NUM_MAX_CPU];

static WAKE_COUNT: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(0); NUM_MAX_CPU];

#[derive(Debug, Clone, Copy)]
struct SleepState {
    is_awake: bool,
    is_wake_up: bool,
}

impl SleepState {
    const fn new() -> Self {
        Self {
            is_awake: true,
            is_wake_up: false,
        }
    }
}

pub(super) struct SleepCpuNoStd;

impl SleepCpu for SleepCpuNoStd {
    fn sleep(&self) {
        if !READY.load(Ordering::Relaxed) {
            wait_microsec(10);
            return;
        }

        let cpu_id = super::cpu_id();

        {
            let mut node = MCSNode::new();
            let mut guard = CPU_SLEEP_STATES[cpu_id].lock(&mut node);

            if guard.is_wake_up {
                guard.is_wake_up = false;
                drop(guard);
                WAKE_COUNT[cpu_id].fetch_add(1, Ordering::Relaxed);
                return;
            }

            guard.is_awake = false;
        }

        Self::wake_up(0);

        {
            let _int_enable = crate::interrupt::InterruptEnable::new();
            crate::delay::wait_interrupt();
        }

        let cpu_id2 = super::cpu_id();
        assert_eq!(cpu_id, cpu_id2); // check no CPU migration

        {
            let mut node = MCSNode::new();
            let mut guard = CPU_SLEEP_STATES[cpu_id].lock(&mut node);

            guard.is_awake = true;
            guard.is_wake_up = false;
        }

        WAKE_COUNT[cpu_id].fetch_add(1, Ordering::Relaxed);
    }

    fn wake_up(cpu_id: usize) -> bool {
        if !READY.load(Ordering::Relaxed) {
            return false;
        }

        let my_cpu_id = crate::cpu::cpu_id();
        if my_cpu_id == cpu_id {
            return false;
        }

        let mut node = MCSNode::new();
        let mut guard = CPU_SLEEP_STATES[cpu_id].lock(&mut node);

        if guard.is_awake || guard.is_wake_up {
            // The CPU is already awake or already notified.
            return false;
        }

        guard.is_wake_up = true;

        drop(guard);

        let count = WAKE_COUNT[cpu_id].load(Ordering::Relaxed);

        let t = crate::time::Time::now();
        'outer: loop {
            let irq = crate::interrupt::get_wakeup_irq();
            crate::interrupt::send_ipi(irq, cpu_id as u32);

            for _ in 0..100 {
                for _ in 0..10 {
                    if WAKE_COUNT[cpu_id].load(Ordering::Relaxed) != count {
                        break 'outer;
                    }
                }

                {
                    let mut node = MCSNode::new();
                    let guard = CPU_SLEEP_STATES[cpu_id].lock(&mut node);

                    if guard.is_awake {
                        break 'outer;
                    }
                }
            }
        }

        log::debug!("{} [ns]", t.elapsed().as_nanos());

        true
    }
}

pub(super) unsafe fn init() {
    READY.store(true, Ordering::Relaxed);
}

pub(super) fn wait_init() {
    while !READY.load(Ordering::Relaxed) {
        core::hint::spin_loop();
    }
}
