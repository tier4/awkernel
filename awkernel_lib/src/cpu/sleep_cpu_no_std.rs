use super::{SleepCpu, NUM_MAX_CPU};
use array_macro::array;
use core::{
    sync::atomic::{AtomicBool, AtomicU32, Ordering},
    time::Duration,
};

/// CPU sleep/wakeup states
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SleepTag {
    Active = 0,  // CPU is running or just woke up
    Waiting = 1, // CPU is halted waiting for wakeup
    Waking = 2,  // Wake-up pending or in progress
}

/// Ready flag for initialization
static READY: AtomicBool = AtomicBool::new(false);

/// Per-CPU sleep state tag
static CPU_SLEEP_TAG: [AtomicU32; NUM_MAX_CPU] =
    array![_ => AtomicU32::new(SleepTag::Active as u32); NUM_MAX_CPU];

struct ResetTimer;

impl Drop for ResetTimer {
    fn drop(&mut self) {
        crate::timer::disable();
    }
}

/// SleepCpu implementation using state-machine and edge-triggered IPI
pub(super) struct SleepCpuNoStd;

impl SleepCpu for SleepCpuNoStd {
    fn sleep(&self, timeout: Option<Duration>) {
        let start = crate::time::Time::now();

        let _timer = if let Some(timeout) = timeout.as_ref() {
            crate::timer::reset(*timeout);
            Some(ResetTimer)
        } else {
            None
        };

        // wait until init
        if !READY.load(Ordering::Relaxed) {
            crate::delay::wait_microsec(10);
            return;
        }

        let cpu_id = super::cpu_id();

        // if wake-up already pending, consume and return
        if CPU_SLEEP_TAG[cpu_id].load(Ordering::Relaxed) == SleepTag::Waking as u32 {
            CPU_SLEEP_TAG[cpu_id].store(SleepTag::Active as u32, Ordering::Release);
            return;
        }

        {
            // enable interrupts and halt until IPI arrives
            let _int_enable = crate::interrupt::InterruptEnable::new();

            // mark waiting before halt
            match CPU_SLEEP_TAG[cpu_id].compare_exchange(
                SleepTag::Active as u32,
                SleepTag::Waiting as u32,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => (),
                Err(x) if x == SleepTag::Waking as u32 => {
                    CPU_SLEEP_TAG[cpu_id].store(SleepTag::Active as u32, Ordering::Release);
                    return;
                }
                _ => unreachable!(),
            }

            // Because x86 APIC timers are edge-triggered interrupts,
            // timer interrupts that occur during interrupt handlers (when interrupts are disabled)
            // will be lost.
            // Therefore, the timeout is checked here.
            if let Some(timeout) = timeout.as_ref() {
                let elapsed = start.elapsed();
                if *timeout > elapsed {
                    let dur = *timeout - elapsed;
                    if dur.as_micros() < 1000 {
                        CPU_SLEEP_TAG[cpu_id].store(SleepTag::Active as u32, Ordering::Release);
                        return;
                    }
                } else {
                    CPU_SLEEP_TAG[cpu_id].store(SleepTag::Active as u32, Ordering::Release);
                    return;
                }
            }

            // In case that there are any tasks to run,
            // wake up the primary CPU to wake me up.
            Self::wake_up(0);

            // check again
            match CPU_SLEEP_TAG[cpu_id].compare_exchange(
                SleepTag::Waking as u32,
                SleepTag::Active as u32,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(x) if x == SleepTag::Waiting as u32 => crate::delay::wait_interrupt(),
                Err(_) => unreachable!(),
            }
        }

        // Rare Case:
        //   IPIs sent during interrupt handlers invoked here will be ignored because IPIs are edge-triggered.
        //   To notify it again, Awkernel setup a timer by `reset_wakeup_timer()` in interrupt handlers.

        // returned by IPI: set back to idle
        CPU_SLEEP_TAG[cpu_id].store(SleepTag::Active as u32, Ordering::Release);
    }

    fn wake_up(cpu_id: usize) -> bool {
        // early exit if not ready or targeting self
        if !READY.load(Ordering::Acquire) {
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
                x if x == SleepTag::Active as u32 => {
                    // CPU not yet sleeping: schedule wake-up
                    if CPU_SLEEP_TAG[cpu_id]
                        .compare_exchange(
                            SleepTag::Active as u32,
                            SleepTag::Waking as u32,
                            Ordering::AcqRel,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return false;
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

    READY.store(true, Ordering::Release);
}

/// wait for init
pub(super) fn wait_init() {
    while !READY.load(Ordering::Acquire) {
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
