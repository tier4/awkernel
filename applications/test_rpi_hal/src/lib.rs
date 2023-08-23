#![no_std]

use awkernel_drivers::hal::rpi::gpio::GpioPin;
use core::time::Duration;
use embedded_hal::digital::v2::OutputPin;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

pub async fn run_rpi_hal() {
    let pin = GpioPin::new(26).unwrap();
    let mut gpio26 = pin.into_output();

    let mut flag = true;
    loop {
        if flag {
            gpio26.set_high().unwrap();
        } else {
            gpio26.set_low().unwrap();
        }

        flag = !flag;

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
