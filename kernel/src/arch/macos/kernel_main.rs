use crate::{
    arch::std_common::{
        console,
        thread::{join, nprocs, thread_create},
    },
    kernel_info::KernelInfo,
};

#[start]
#[no_mangle]
pub extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
    awkernel_lib::arch::macos::init();
    console::init();

    // Create worker threads.
    let mut threads = Vec::new();
    for i in 1..nprocs() {
        if let Some(th) = thread_create(i) {
            threads.push(th);
        } else {
            log::error!("Failed to create thread.");
        }
    }

    // Execute main.
    let kernel_info = KernelInfo::<()> {
        info: (),
        cpu_id: 0,
    };
    crate::main(kernel_info);

    // Join the threads.
    for th in threads {
        join(th);
    }

    0
}
