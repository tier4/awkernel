static mut STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
static mut STACK_START: usize = 256 * 1024 * 1024; // 256MiB

/// Set the stack size.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn set_stack_size(size: usize) {
    STACK_SIZE = size;
}

/// Get the stack size.
#[inline(always)]
pub fn get_stack_size() -> usize {
    unsafe { STACK_SIZE }
}

/// Set the stack start.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn set_stack_start(start: usize) {
    STACK_START = start;
}

/// Get the stack start.
#[inline(always)]
pub fn get_stack_start() -> usize {
    unsafe { STACK_START }
}
