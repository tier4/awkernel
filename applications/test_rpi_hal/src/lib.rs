#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_drivers::hal::rpi::gpio::{GpioPin, PullMode};
use core::time::Duration;
use embedded_hal::digital::{InputPin, OutputPin};

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

pub async fn run_rpi_hal() {
    awkernel_async_lib::spawn(
        "switching (Pull-down)".into(),
        switching_pull_down(),
        SchedulerType::FIFO,
    )
    .await;
}

pub async fn _blink_led() {
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

pub async fn switching_pull_down() {
    let pin = GpioPin::new(26).unwrap(); // Use GPIO26
    let mut gpio26 = pin.into_output(); // Make GPIO26 the output mode

    let pin = GpioPin::new(16).unwrap(); // Use GPIO16
    let gpio16 = pin.into_input(PullMode::Down).unwrap();

    loop {
        if gpio16.is_high().unwrap() {
            gpio26.set_high().unwrap(); // On
        } else {
            gpio26.set_low().unwrap(); // Off
        }

        awkernel_async_lib::sleep(Duration::from_millis(20)).await;
    }
}

pub async fn _switching_pull_up() {
    let pin = GpioPin::new(26).unwrap(); // Use GPIO26
    let mut gpio26 = pin.into_output(); // Make GPIO26 the output mode

    let pin = GpioPin::new(16).unwrap(); // Use GPIO16
    let gpio16 = pin.into_input(PullMode::Up).unwrap();

    loop {
        if gpio16.is_high().unwrap() {
            gpio26.set_high().unwrap(); // On
        } else {
            gpio26.set_low().unwrap(); // Off
        }

        awkernel_async_lib::sleep(Duration::from_millis(20)).await;
    }
}
