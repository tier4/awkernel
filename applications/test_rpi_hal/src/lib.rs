#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_drivers::hal::{
    i2c::write_quick,
    rpi::{
        gpio::{GpioPin, PullMode},
        i2c::I2cBus,
    },
};
use core::time::Duration;
use embedded_hal::{
    digital::{InputPin, OutputPin},
    i2c::I2c,
};

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

pub async fn run_rpi_hal() {
    awkernel_async_lib::spawn(
        "blink and switch".into(),
        blink_and_switch(),
        SchedulerType::FIFO,
    )
    .await;

    scan_i2c_devices().await;
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

pub async fn _switching_pull_down() {
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

pub async fn blink_and_switch() {
    let pin = GpioPin::new(26).unwrap(); // Use GPIO26
    let mut gpio26 = pin.into_output(); // Make GPIO26 the output mode

    let pin = GpioPin::new(16).unwrap(); // Use GPIO16
    let gpio16 = pin.into_input(PullMode::Up).unwrap();

    let mut flag = true;

    loop {
        if gpio16.is_high().unwrap() {
            if flag {
                gpio26.set_high().unwrap(); // On
            } else {
                gpio26.set_low().unwrap(); // Off
            }
        } else {
            gpio26.set_low().unwrap(); // Off
        }

        // i += 1;
        // if i == 50 {
        //     i = 0;
        //     flag = !flag;
        // }

        flag = !flag;

        awkernel_async_lib::sleep(Duration::from_millis(20)).await;
    }
}

async fn scan_i2c_devices() {
    let mut i2c = I2cBus::new(150_000_000, false).unwrap();

    let mut has_adt7410 = false;

    for addr in 4..=0x7f {
        if write_quick(&mut i2c, addr).is_ok() {
            log::info!("I2C #{addr} has been found.");

            if addr == 72 {
                has_adt7410 = true;
            }
        }
    }

    if has_adt7410 {
        awkernel_async_lib::spawn(
            "temperature monitor".into(),
            temperature_adt7410(i2c),
            SchedulerType::FIFO,
        )
        .await;
    }
}

async fn temperature_adt7410(mut i2c: I2cBus) {
    loop {
        let mut buf: [u8; 2] = [0, 0];

        i2c.write_read(72, &[0], &mut buf).unwrap();
        let temp = ((buf[0] as u16) << 8) | buf[1] as u16;

        log::info!("Temperature is {} [C].", (temp as i16 >> 3) as f64 / 16.0);

        awkernel_async_lib::sleep(Duration::from_secs(10)).await;
    }
}
