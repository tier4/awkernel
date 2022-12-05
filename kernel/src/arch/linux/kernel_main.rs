use crate::{heap, kernel_info::KernelInfo};

#[start]
#[no_mangle]
pub extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
    super::console::init();

    if unsafe { super::heap::mmap() }.is_err() {
        let msg = b"failed to initialize heap memory\n";
        unsafe { libc::write(0, msg.as_ptr() as _, msg.len()) };
        return -1;
    };

    heap::init(); // Enable heap allocator.

    let kernel_info = KernelInfo::<()> {
        info: (),
        cpu_id: 0,
    };
    crate::main(kernel_info);

    0
}
