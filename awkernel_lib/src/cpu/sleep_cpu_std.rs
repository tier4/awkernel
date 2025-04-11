use super::{SleepCpu, NUM_MAX_CPU};
use array_macro::array;

static MUTEX_COND: [(std::sync::Mutex<bool>, std::sync::Condvar); NUM_MAX_CPU - 1] =
    array![_ => (std::sync::Mutex::new(false), std::sync::Condvar::new()); NUM_MAX_CPU - 1];

pub(super) struct SleepCpuStd;

impl SleepCpu for SleepCpuStd {
    fn sleep(&self) {
        let cpu_id = super::cpu_id();

        // The primary CPU uses epoll/select to wait for events.
        // So, it must not use `sleep()`.
        assert!(cpu_id > 0);

        let (mtx, condvar) = &MUTEX_COND[cpu_id - 1];

        loop {
            let mut guard = mtx.lock().expect("Error: Failed to lock mutex.");
            if *guard {
                return;
            }

            *guard = true;

            // In case that there are any tasks to run,
            // wake up the primary CPU to wake me up.
            crate::select::notify();

            let mut guard = condvar
                .wait(guard)
                .expect("Error: Failed to wait on condvar.");
            if *guard {
                *guard = false;

                return;
            }
        }
    }

    fn wake_up(cpu_id: usize) -> bool {
        if cpu_id == 0 {
            crate::select::notify();
            return true;
        }

        let (mtx, condvar) = &MUTEX_COND[cpu_id - 1];

        let mut guard = mtx.lock().expect("Error: Failed to lock mutex.");
        if !*guard {
            // The CPU is already awake.
            return false;
        }

        *guard = true;
        condvar.notify_one();

        true
    }
}
