use core::arch::asm;

pub mod clock;
pub mod gpio;
pub mod i2c;
pub mod pwm;
pub mod spi;
pub mod uart;

/// Wait N CPU cycles
fn wait_cycles(n: usize) {
    if n > 0 {
        for _ in 0..n {
            unsafe { asm!("nop;") };
        }
    }
}
