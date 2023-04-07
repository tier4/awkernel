use core::arch::global_asm;
global_asm!(include_str!("crt0.S"));

#[no_mangle]
pub extern "C" fn main() -> u32 {
    let uart = 0x1000_0000 as *mut u8;
    for c in b"Hello, World!\n".iter() {
        unsafe {
            *uart = *c as u8;
        }
    }
    return 0;
}
