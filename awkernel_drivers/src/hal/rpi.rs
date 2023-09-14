use core::arch::asm;

pub mod gpio;
pub mod i2c;
pub mod pwm;
pub mod spi;

/// Wait N CPU cycles
fn wait_cycles(n: usize) {
    if n > 0 {
        for _ in 0..n {
            unsafe { asm!("nop;") };
        }
    }
}
