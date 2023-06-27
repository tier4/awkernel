use crate::{arch::std_common::console, kernel_info::KernelInfo};
use alloc::vec::Vec;
use core::{mem::MaybeUninit, ptr::null_mut};
use libc::c_void;

// #[cfg(target_os = "linux")]
// use core::mem::size_of;

#[start]
#[no_mangle]
pub extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
    // Initialize.
    awkernel_lib::arch::std_common::init();
    awkernel_lib::arch::std_common::init_per_thread(0);
    console::init();

    #[cfg(target_os = "linux")]
    {
        if !set_fifo_scheduler() {
            log::warn!("Failed to SCHED_FIFO.");
        }
    }

    // Create worker threads.
    let mut threads = Vec::new();
    for i in 1..nprocs() {
        if let Some(th) = thread_create(i) {
            threads.push(th);
        } else {
            log::error!("Failed to create thread.");
        }
    }

    // Use CPU #0.
    // #[cfg(target_os = "linux")]
    // set_affinity(pthread_self(), 0);

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

// #[cfg(target_os = "linux")]
// fn pthread_self() -> libc::pthread_t {
//     unsafe { libc::pthread_self() }
// }

fn join(thread: libc::pthread_t) {
    unsafe { libc::pthread_join(thread, null_mut()) };
}

/// Get the number of logical CPUs.
fn nprocs() -> usize {
    let result = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    assert_ne!(result, 0);
    result as usize
}

// #[cfg(target_os = "linux")]
// fn set_affinity(thread: libc::pthread_t, cpu: usize) {
//     unsafe {
//         let mut cpuset: libc::cpu_set_t = MaybeUninit::zeroed().assume_init();
//         libc::CPU_SET(cpu, &mut cpuset);

//         if libc::pthread_setaffinity_np(thread, size_of::<libc::cpu_set_t>(), &cpuset) != 0 {
//             log::warn!("Failed to set CPU affinity: thread = {thread}, cpu = {cpu}");
//         }
//     }
// }

fn thread_create(cpu: usize) -> Option<libc::pthread_t> {
    unsafe {
        let mut attr: libc::pthread_attr_t = MaybeUninit::zeroed().assume_init();
        libc::pthread_attr_init(&mut attr);

        let mut thread: libc::pthread_t = MaybeUninit::zeroed().assume_init();
        let result = libc::pthread_create(&mut thread, &attr, thread_func, cpu as *mut _);
        if result == 0 {
            // #[cfg(target_os = "linux")]
            // set_affinity(thread, cpu);

            Some(thread)
        } else {
            None
        }
    }
}

extern "C" fn thread_func(cpu: *mut c_void) -> *mut c_void {
    awkernel_lib::arch::std_common::init_per_thread(cpu as usize);

    let kernel_info = KernelInfo::<()> {
        info: (),
        cpu_id: cpu as usize,
    };
    crate::main(kernel_info);

    null_mut()
}

#[cfg(target_os = "linux")]
fn set_fifo_scheduler() -> bool {
    unsafe {
        let param = libc::sched_param { sched_priority: 1 };
        libc::sched_setscheduler(0, libc::SCHED_FIFO, &param) == 0
    }
}
