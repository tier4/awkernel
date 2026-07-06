#[cfg(not(feature = "std"))]
pub use crate::arch::config::*;

/// Backup Heap size is 64 MiB
#[allow(dead_code)]
pub const BACKUP_HEAP_SIZE: usize = 64 * 1024 * 1024;

/// Auto-trace: record a task execution trace automatically after boot and
/// dump it to the serial console in the `TRACE_*` format.
///
/// Intended for real hardware where no shell input is available; capture the
/// serial output on the host (e.g. `minicom -D /dev/ttyUSB0 -C trace.log`)
/// and plot it with `awkernel_script/trace_view/plot_trace.py`.
///
/// Set `AUTO_TRACE_ENABLED` to `false` to use only the shell commands
/// (`(trace_start)` / `(trace_stop)` / `(trace)`) instead.
#[allow(dead_code)]
pub const AUTO_TRACE_ENABLED: bool = true;

/// Seconds to wait after boot before starting the auto-trace
/// (skips driver-initialization noise).
#[allow(dead_code)]
pub const AUTO_TRACE_START_DELAY_SECS: u64 = 10;

/// Length of the auto-trace recording in seconds.
#[allow(dead_code)]
pub const AUTO_TRACE_DURATION_SECS: u64 = 5;

#[cfg(test)]
#[allow(dead_code)]
pub const HEAP_START: usize = 0;

/// Initialize the architecture specific configuration.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn init() {
    #[cfg(all(feature = "x86", not(feature = "linux")))]
    {
        awkernel_lib::config::set_stack_size(STACK_SIZE);
        awkernel_lib::config::set_stack_start(STACK_START);
    }
}
