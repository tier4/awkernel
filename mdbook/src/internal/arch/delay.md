# Delay

The `Delay` trait provides a way to wait for a certain amount of time and to get the time.
It is defined in [awkernel_lib/src/delay.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/delay.rs) as follows.

```rust
pub trait Delay {
    /// Wait interrupt.
    fn wait_interrupt();

    /// Wait microseconds.
    fn wait_microsec(usec: u64);

    /// Never return.
    fn wait_forever() -> ! {
        loop {
            Self::wait_interrupt();
        }
    }

    /// Wait milliseconds.
    fn wait_millisec(msec: u64) {
        assert!(msec < u64::MAX / 1000);
        Self::wait_microsec(msec * 1000);
    }

    /// Wait seconds.
    fn wait_sec(sec: u64) {
        assert!(sec < u64::MAX / 1_000_000);
        Self::wait_microsec(sec * 1000 * 1000);
    }

    /// This function returns uptime in microseconds.
    fn uptime() -> u64;

    /// Return CPU cycle counter.
    fn cpu_counter() -> u64;

    /// Pause a CPU during busy loop to reduce CPU power consumption.
    fn pause() {
        core::hint::spin_loop();
    }
}
```

There are several functions regarding the `Delay` trait in [awkernel_lib/src/delay.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/delay.rs).

|  function             | description |
|-----------------------|-------------|
| `fn wait_interrupt()` | Wait interrupt. |
| `fn wait_microsec(usec: u64)` | Wait microseconds. |
| `fn wait_millisec(msec: u64)` | Wait milliseconds. |
| `fn wait_sec(sec: u64)` | Wait seconds. |
| `fn wait_forever() -> !` | Never return. |
| `fn uptime() -> u64` | Return uptime in microseconds. |
| `fn cpu_counter() -> u64` | Return CPU cycle counter. |
| `fn pause()` | Pause a CPU during busy loop to reduce CPU power consumption. |

# Implementation

## x86_64

For x86_64, the the [`X86`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64.rs) structure implements the `Delay` trait in
[awkernel_lib/src/arch/x86_64/delay.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64/delay.rs) as follows.

```rust
impl Delay for super::X86 {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        let start = uptime();
        loop {
            let diff = uptime() - start;
            if diff >= usec {
                break;
            }

            core::hint::spin_loop();
        }
    }

    fn uptime() -> u64 {
        let base = HPET_BASE.load(Ordering::Relaxed);
        let hz = HPET_COUNTER_HZ.load(Ordering::Relaxed);
        let start = HPET_COUNTER_START.load(Ordering::Relaxed);

        if hz == 0 {
            0
        } else {
            let now = HPET_MAIN_COUNTER.read(base);
            let diff = now - start;

            diff * 1_000_000 / hz
        }
    }

    fn cpu_counter() -> u64 {
        unsafe { core::arch::x86_64::_rdtsc() }
    }
}
```

Awkernel currently uses High Precision Event Timer (HPET) to get uptime in microseconds.
So, if you want to use Awkernel on KVM, you need to enable HPET in the virtual machine settings.
To get the cpu cycle counter, Awkernel uses the `_rdtsc` instruction.

## AArch64

For x86_64, the [`AArch64`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64.rs) structure implements the `Delay` trait in [awkernel_lib/src/arch/aarch64/delay.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/delay.rs) as follows.

```rust
impl Delay for super::AArch64 {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u64) {
        let frq = awkernel_aarch64::cntfrq_el0::get();
        let t = awkernel_aarch64::cntvct_el0::get();

        let end = t + ((frq / 1000) * usec) / 1000;

        while awkernel_aarch64::cntvct_el0::get() < end {
            awkernel_aarch64::isb();
        }
    }

    fn uptime() -> u64 {
        let start = unsafe { read_volatile(addr_of!(COUNT_START)) };

        let frq = awkernel_aarch64::cntfrq_el0::get();
        let now = awkernel_aarch64::cntvct_el0::get();

        let diff = now - start;

        diff * 1_000_000 / frq
    }

    fn cpu_counter() -> u64 {
        awkernel_aarch64::pmccntr_el0::get()
    }
}
```

To get uptime in microseconds, Awkernel uses the counter-timer frequency register (CNTFRQ_EL0) and the counter-timer virtual count register (CNTVCT_EL0) of AArch64.
To get the cpu cycle counter, Awkernel uses the performance monitors cycle count register (PMCCNTR_EL0).
