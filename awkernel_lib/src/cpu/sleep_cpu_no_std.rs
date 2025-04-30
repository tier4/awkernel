use super::{SleepCpu, NUM_MAX_CPU};
use array_macro::array;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

/// CPU sleep/wakeup states
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SleepTag {
    Idle = 0,    // CPU is running or just woke up
    Waiting = 1, // CPU is halted waiting for wakeup
    Waking = 2,  // Wake-up pending or in progress
}

/// Ready flag for initialization
static READY: AtomicBool = AtomicBool::new(false);

/// Per-CPU sleep state tag
static CPU_SLEEP_TAG: [AtomicU32; NUM_MAX_CPU] =
    array![_ => AtomicU32::new(SleepTag::Idle as u32); NUM_MAX_CPU];

/// SleepCpu implementation using state-machine and edge-triggered IPI
pub(super) struct SleepCpuNoStd;

impl SleepCpu for SleepCpuNoStd {
    fn sleep(&self) {
        // wait until init
        if !READY.load(Ordering::Relaxed) {
            crate::delay::wait_microsec(10);
            return;
        }

        let cpu_id = super::cpu_id();

        // if wake-up already pending, consume and return
        if CPU_SLEEP_TAG[cpu_id].load(Ordering::Relaxed) == SleepTag::Waking as u32 {
            CPU_SLEEP_TAG[cpu_id].store(SleepTag::Idle as u32, Ordering::Release);
            return;
        }

        {
            // enable interrupts and halt until IPI arrives
            let _int_enable = crate::interrupt::InterruptEnable::new();

            // mark waiting before halt
            match CPU_SLEEP_TAG[cpu_id].compare_exchange(
                SleepTag::Idle as u32,
                SleepTag::Waiting as u32,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => (),
                Err(x) if x == SleepTag::Waking as u32 => {
                    CPU_SLEEP_TAG[cpu_id].store(SleepTag::Idle as u32, Ordering::Release);
                    return;
                }
                _ => unreachable!(),
            }

            // In case that there are any tasks to run,
            // wake up the primary CPU to wake me up.
            Self::wake_up(0);

            // check again
            match CPU_SLEEP_TAG[cpu_id].compare_exchange(
                SleepTag::Waking as u32,
                SleepTag::Idle as u32,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => (),
                Err(_) => crate::delay::wait_interrupt(),
            }
        }

        // Rare Case:
        //   IPIs sent here will be ignored because IPIs are edge-trigger.
        //   To notify it again, Awkernel setup a timer by `reset_wakeup_timer()` in interrupt handlers.

        // returned by IPI: set back to idle
        CPU_SLEEP_TAG[cpu_id].store(SleepTag::Idle as u32, Ordering::Release);
    }

    fn wake_up(cpu_id: usize) -> bool {
        // early exit if not ready or targeting self
        if !READY.load(Ordering::Relaxed) {
            return false;
        }
        let my_id = crate::cpu::cpu_id();
        if my_id == cpu_id {
            return false;
        }

        // attempt state transitions until success or redundant
        loop {
            let tag = CPU_SLEEP_TAG[cpu_id].load(Ordering::Acquire);
            match tag {
                x if x == SleepTag::Idle as u32 => {
                    // CPU not yet sleeping: schedule wake-up
                    if CPU_SLEEP_TAG[cpu_id]
                        .compare_exchange(
                            SleepTag::Idle as u32,
                            SleepTag::Waking as u32,
                            Ordering::AcqRel,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return true;
                    }
                }
                x if x == SleepTag::Waiting as u32 => {
                    // CPU is halted: send IPI
                    if CPU_SLEEP_TAG[cpu_id]
                        .compare_exchange(
                            SleepTag::Waiting as u32,
                            SleepTag::Waking as u32,
                            Ordering::AcqRel,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        let irq = crate::interrupt::get_wakeup_irq();
                        crate::interrupt::send_ipi(irq, cpu_id as u32);
                        return true;
                    }
                }
                x if x == SleepTag::Waking as u32 => {
                    // wake-up already pending
                    let irq = crate::interrupt::get_wakeup_irq();
                    crate::interrupt::send_ipi(irq, cpu_id as u32);
                    return false;
                }
                _ => {
                    unreachable!()
                }
            }
            // retry
            core::hint::spin_loop();
        }
    }
}

/// initialize
pub(super) unsafe fn init() {
    use alloc::boxed::Box;

    // Set-up timer interrupt.
    if let Some(irq) = crate::timer::irq_id() {
        crate::interrupt::enable_irq(irq);

        let timer_callback = Box::new(|_irq| {
            // Re-enable timer.
            crate::timer::reset(core::time::Duration::from_micros(100));
        });

        if crate::interrupt::register_handler(irq, "local timer".into(), timer_callback).is_ok() {
            log::info!("A local timer has been initialized.");
        }
    }

    READY.store(true, Ordering::Relaxed);
}

/// wait for init
pub(super) fn wait_init() {
    while !READY.load(Ordering::Relaxed) {
        core::hint::spin_loop();
    }
}

#[inline(always)]
pub fn reset_wakeup_timer() {
    let cpu_id = crate::cpu::cpu_id();

    if CPU_SLEEP_TAG[cpu_id].load(Ordering::Relaxed) == SleepTag::Waiting as u32 {
        crate::timer::reset(core::time::Duration::from_micros(100));
    }
}
