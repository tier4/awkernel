use libc::STDOUT_FILENO;

pub mod config;
mod console;
pub mod delay;
mod heap;
mod kernel_main;

pub unsafe fn puts(data: &str) {
    libc::write(
        STDOUT_FILENO,
        data.as_ptr() as *const _,
        data.as_bytes().len(),
    );
}
