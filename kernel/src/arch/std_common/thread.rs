use core::{mem::MaybeUninit, ptr::null_mut};

use libc::c_void;

use crate::kernel_info::KernelInfo;

/// Get the number of logical CPUs.
pub fn nprocs() -> usize {
    let result = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    assert_ne!(result, 0);
    result as usize
}

pub fn thread_create(cpu: usize) -> Option<libc::pthread_t> {
    unsafe {
        let mut attr: libc::pthread_attr_t = MaybeUninit::zeroed().assume_init();
        libc::pthread_attr_init(&mut attr);

        let mut thread: libc::pthread_t = MaybeUninit::zeroed().assume_init();
        let result = libc::pthread_create(&mut thread, &attr, thread_func, cpu as *mut _);
        if result == 0 {
            set_affinity(thread, cpu);
            Some(thread)
        } else {
            None
        }
    }
}

fn set_affinity(thread: libc::pthread_t, cpu: usize) {
    // unsafe {
    //     let mut cpuset: libc::cpu_set_t = MaybeUninit::zeroed().assume_init();
    //     libc::CPU_SET(cpu, &mut cpuset);

    //     if libc::pthread_setaffinity_np(thread, size_of::<libc::cpu_set_t>(), &cpuset) != 0 {
    //         log::warn!("Failed to set CPU affinity: thread = {thread}, cpu = {cpu}");
    //     }
    // }
}

extern "C" fn thread_func(cpu: *mut c_void) -> *mut c_void {
    let kernel_info = KernelInfo::<()> {
        info: (),
        cpu_id: cpu as usize,
    };
    crate::main(kernel_info);

    null_mut()
}

pub fn join(thread: libc::pthread_t) {
    unsafe { libc::pthread_join(thread, null_mut()) };
}
