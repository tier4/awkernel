use super::{SleepCpu, NUM_MAX_CPU};
use array_macro::array;
use core::time::Duration;

#[derive(Debug, Clone, Copy)]
struct SleepState {
    is_awake: bool,
    is_wake_up: bool,
}

static MUTEX_COND: [(std::sync::Mutex<SleepState>, std::sync::Condvar); NUM_MAX_CPU - 1] = array![_ => (std::sync::Mutex::new(SleepState{is_awake: true, is_wake_up: false}), std::sync::Condvar::new()); NUM_MAX_CPU - 1];

pub(super) struct SleepCpuStd;

impl SleepCpu for SleepCpuStd {
    fn sleep(&self, timeout: Option<Duration>) {
        // SleepCpuStd::sleep() does not support timeout.
        assert!(timeout.is_none());

        let cpu_id = super::cpu_id();

        // The primary CPU uses epoll/select to wait for events.
        // So, it must not use `sleep()`.
        assert!(cpu_id > 0);

        let (mtx, condvar) = &MUTEX_COND[cpu_id - 1];

        let mut guard = mtx.lock().expect("Error: Failed to lock mutex.");
        if guard.is_wake_up {
            return;
        }

        guard.is_awake = false;

        // In case that there are any tasks to run,
        // wake up the primary CPU to wake me up.
        crate::select::notify();

        loop {
            guard = condvar
                .wait(guard)
                .expect("Error: Failed to wait on condvar.");

            if guard.is_wake_up {
                guard.is_awake = true;
                guard.is_wake_up = false;
                break;
            }

            // Spurious wake up.
        }
    }

    fn wake_up(cpu_id: usize) -> bool {
        if cpu_id == 0 {
            crate::select::notify();
            return true;
        }

        let (mtx, condvar) = &MUTEX_COND[cpu_id - 1];

        let mut guard = mtx.lock().expect("Error: Failed to lock mutex.");
        if guard.is_awake {
            // The CPU is already awake.
            return false;
        }

        guard.is_wake_up = true;
        condvar.notify_one();

        true
    }
}
