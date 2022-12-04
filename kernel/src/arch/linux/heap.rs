use libc::c_void;

pub unsafe fn mmap() -> Result<*mut c_void, &'static str> {
    let result = libc::mmap(
        crate::config::HEAP_START as _,
        crate::config::HEAP_SIZE as _,
        libc::PROT_READ | libc::PROT_WRITE,
        libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_FIXED | libc::MAP_POPULATE,
        -1,
        0,
    );

    if result == libc::MAP_FAILED {
        Err("failed mmap")
    } else {
        Ok(result)
    }
}

pub unsafe fn munmap(addr: *mut c_void) {
    libc::munmap(addr, crate::config::HEAP_SIZE as _);
}
