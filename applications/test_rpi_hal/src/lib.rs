#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_drivers::hal::{
    i2c::write_quick,
    raspi::{
        gpio::{GpioPin, PullMode},
        i2c::I2cBus,
        pwm,
        uart::{Uart, Uarts},
    },
};
use core::time::Duration;
use embedded_hal::{
    digital::{InputPin, OutputPin},
    i2c::I2c,
    pwm::SetDutyCycle,
};
use embedded_hal_nb::serial::{Read, Write};

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

pub async fn run() {
    awkernel_async_lib::spawn(
        "blink and switch".into(),
        blink_and_switch(),
        SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn("test PWM".into(), test_pwm(), SchedulerType::FIFO).await;

    awkernel_async_lib::spawn("test UART2".into(), test_uart2(), SchedulerType::FIFO).await;

    scan_i2c_devices().await;
}

pub async fn test_uart2() {
    let mut uart2 = Uart::new(Uarts::Uart2, 230400).unwrap();
    let (tx2, rx2) = uart2.get_gpio_pins(); // Get the GPIO pins for UART2.

    log::debug!("UART2: tx = {tx2}, rx = {rx2}");

    let write_buf = b"Hello, world!\r\n";

    for data in write_buf.iter() {
        uart2.write(*data).unwrap();
    }

    loop {
        if let Ok(data) = uart2.read() {
            loop {
                match uart2.write(data) {
                    Ok(_) => break,
                    Err(embedded_hal_nb::nb::Error::WouldBlock) => {
                        awkernel_async_lib::r#yield().await;
                    }
                    Err(_) => {
                        // Some error occurred.
                        break;
                    }
                }
            }
        }
        awkernel_async_lib::sleep(Duration::from_millis(5)).await;
    }
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
    let mut gpio16 = pin.into_input(PullMode::Down).unwrap();

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
    let mut gpio16 = pin.into_input(PullMode::Up).unwrap();

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
    let mut gpio16 = pin.into_input(PullMode::Up).unwrap();

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

async fn test_pwm() {
    let mut pwm0 = pwm::Pwm::new(pwm::Channel::Ch0, true).unwrap();

    pwm0.enable().unwrap();
    pwm0.set_frequency(500).unwrap();
    pwm0.set_duty_cycle_percent(85).unwrap();

    let mut pwm1 = pwm::Pwm::new(pwm::Channel::Ch1, false).unwrap();

    pwm1.enable().unwrap();

    loop {
        for i in (0..=100).chain((1..100).rev()) {
            pwm1.set_duty_cycle(i).unwrap();
            awkernel_async_lib::sleep(Duration::from_millis(10)).await;
        }
    }
}
