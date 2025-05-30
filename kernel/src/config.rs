#[cfg(not(feature = "std"))]
pub use crate::arch::config::*;

/// Backup Heap size is 64 MiB
#[allow(dead_code)]
pub const BACKUP_HEAP_SIZE: usize = 64 * 1024 * 1024;

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
