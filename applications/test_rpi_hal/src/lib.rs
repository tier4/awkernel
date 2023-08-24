#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_drivers::hal::rpi::gpio::GpioPin;
use core::time::Duration;
use embedded_hal::digital::OutputPin;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

pub async fn run_rpi_hal() {
    awkernel_async_lib::spawn("blink LED".into(), blink_led(), SchedulerType::FIFO).await;
}

pub async fn blink_led() {
    let pin = GpioPin::new(26).unwrap(); // Use GPIO26
    let mut gpio26 = pin.into_output(); // Make GPIO26 the output mode

    let mut flag = true;
    loop {
        if flag {
            gpio26.set_high().unwrap(); // On
        } else {
            gpio26.set_low().unwrap(); // Off
        }

        flag = !flag;

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
