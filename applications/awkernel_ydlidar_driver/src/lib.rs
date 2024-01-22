#![feature(async_closure)]
#![feature(prelude_2024)]
#![no_std]

#[macro_use]
extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;
use alloc::collections::VecDeque;

use core::time::Duration;
use core::result::Result;
use core::assert;
use core::cfg;
use core::result::Result::{Err, Ok};
use core::option::Option::{None, Some};
use core::iter::Iterator;
use core::default::Default;
use core::convert::Into;
use core::convert::TryInto;

use awkernel_async_lib::channel::bounded::{Sender, Receiver};
use awkernel_async_lib::channel::bounded;
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_drivers::hal::rpi::uart::{Uart, Uarts};
use embedded_hal_nb::serial::{Read, Write, ErrorType};

use ydlidar_signal_parser::{
    HEADER_SIZE,
    validate_response_header, calc_angles, calc_distances, get_intensities, get_flags,
    err_if_checksum_mismatched, sendable_packet_range, Scan, is_beginning_of_cycle
};

mod device_info;
mod ydlidar_models;

const LIDAR_CMD_GET_DEVICE_HEALTH: u8 = 0x92;
const LIDAR_CMD_GET_DEVICE_INFO: u8 = 0x90;
const LIDAR_CMD_SYNC_BYTE: u8 = 0xA5;
const LIDAR_CMD_FORCE_STOP: u8 = 0x00;
const LIDAR_CMD_RESTART: u8 = 0x40;
const LIDAR_CMD_STOP: u8 = 0x65;
const LIDAR_CMD_SCAN: u8 = 0x60;
const LIDAR_ANS_TYPE_DEVINFO: u8 = 0x4;
const LIDAR_ANS_TYPE_DEVHEALTH: u8 = 0x6;
const LIDAR_ANS_TYPE_MEASUREMENT: u8 = 0x81;

// Link error occurs without this decleration
#[no_mangle]
extern "C" fn fmod(x: f64, y: f64) -> f64 {
    libm::fmod(x, y)
}

fn send_data(port: &mut Uart, data: &[u8]) {
    for e in data {
        if let Err(e) = port.write(*e) {
            log::error!("Send error: {:?}", e);
        }
    }
}

fn send_command(port: &mut Uart, command: u8) {
    let data: [u8; 2] = [LIDAR_CMD_SYNC_BYTE, command];
    send_data(port, &data);
}

fn flush(port: &mut Uart) {
    for _ in 0..32 {
        if let Ok(data) = port.read() {
        }
    }
}

fn read(port: &mut Uart, data_size: usize) -> Result<Vec<u8>, <Uart as ErrorType>::Error> {
    assert!(data_size > 0);
    let mut data = vec![0u8; data_size];
    let mut index = 0;
    while index < data_size {
        if let Ok(s) = port.read() {
            data[index] = s;
            index += 1;
            continue;
        }
    }
    return Ok(data);
}

fn get_device_info(port: &mut Uart) -> device_info::DeviceInfo {
    send_command(port, LIDAR_CMD_GET_DEVICE_INFO);
    let header = read(port, HEADER_SIZE).unwrap();
    log::info!("device info header = {:02X?}", header);
    validate_response_header(&header, Some(20), LIDAR_ANS_TYPE_DEVINFO).unwrap();
    let info = read(port, 20).unwrap();
    log::info!("device info = {:02X?}", info);
    return device_info::DeviceInfo {
        model_number: info[0],
        firmware_major_version: info[2],
        firmware_minor_version: info[1],
        hardware_version: info[3],
        serial_number: info[4..20].try_into().unwrap(),
    };
}

fn check_device_health(port: &mut Uart) -> Result<(), String> {
    send_command(port, LIDAR_CMD_GET_DEVICE_HEALTH);
    let header = read(port, HEADER_SIZE).unwrap();
    log::info!("device health header = {:02X?}", header);
    validate_response_header(&header, Some(3), LIDAR_ANS_TYPE_DEVHEALTH).unwrap();
    let health = read(port, 3).unwrap();
    log::info!("device health = {:02X?}", health);

    if health[0] != 0 {
        // Last two bit are reserved bits, which should be ignored.
        return Err(alloc::format!(
            "Device health error. Error code = {:#010b}. \
                 See the development manual for details.",
            health[0]
        ));
    }
    return Ok(());
}

fn start_scan(port: &mut Uart) {
    send_command(port, LIDAR_CMD_SCAN);
    let header = read(port, HEADER_SIZE).unwrap();
    log::info!("start scan response header = {:02X?}", header);
    validate_response_header(&header, None, LIDAR_ANS_TYPE_MEASUREMENT).unwrap();
}

fn stop_scan(port: &mut Uart) {
    send_command(port, LIDAR_CMD_FORCE_STOP);
    send_command(port, LIDAR_CMD_STOP);
}

fn stop_scan_and_flush(port: &mut Uart) {
    stop_scan(port);
    flush(port);
}

fn read_device_signal(
    mut port: Uart// ,
    // scan_data_tx: Sender<u8>,
) {
    loop {
        let Ok(signal) = port.read() else {
            // awkernel_async_lib::sleep(Duration::from_millis(10)).await;
            continue;
        };
        log::info!("Received signal = {:02X}", signal);
        // if let Err(e) = scan_data_tx.send(signal).await {
        //     log::error!("Send error. {:?}", e);
        // }
    }
}

async fn parse_packets(
    scan_data_rx: Receiver<u8>,
    scan_tx: Sender<Scan>,
) {
    let mut buffer = VecDeque::<u8>::new();
    let mut scan = Scan::new();
    loop {
        match scan_data_rx.try_recv() {
            Ok(data) => {
                buffer.push_back(data);
            }
            Err(_) => {
                awkernel_async_lib::sleep(Duration::from_millis(10)).await;
            }
        }

        if buffer.len() == 0 {
            continue;
        }

        log::info!("buffer = {:02X?}", buffer);

        let (start_index, n_packet_bytes) = match sendable_packet_range(&buffer) {
            Ok(t) => t,
            Err(s) => { log::info!("{}", s); continue; },
        };

        if buffer.len() >= start_index + n_packet_bytes {
            log::info!("buffer = {:02X?}", buffer);
            let range = buffer
                .range(start_index..(start_index+n_packet_bytes))
                .copied().collect::<Vec<_>>();
            log::info!("buffer[{}..{}] = {:02X?}", start_index, start_index+n_packet_bytes, range);
        }

        buffer.drain(..start_index); // remove leading bytes
        if buffer.len() < n_packet_bytes {
            log::info!("Insufficient buffer size: packet size = {}, buffer size = {}", n_packet_bytes, buffer.len());
            // insufficient buffer size to extract a packet
            continue;
        }
        let packet = buffer.drain(0..n_packet_bytes).collect::<Vec<_>>();
        if is_beginning_of_cycle(&packet) {
            // scan_tx.send(scan).await.unwrap();
            scan = Scan::new();
        }

        log::info!("packet.len() = {}, n_packet_bytes = {n_packet_bytes}, start_index = {start_index}", packet.len());
        log::info!("packet = {:02X?}", packet);
        if let Err(e) = err_if_checksum_mismatched(&packet) {
            log::error!("Checksum error. {:?}", e);
            continue;
        }

        calc_angles(&packet, &mut scan.angles_radian);
        calc_distances(&packet, &mut scan.distances);
        get_intensities(&packet, &mut scan.intensities);
        get_flags(&packet, &mut scan.flags);

        log::info!("Received {} scan points", scan.distances.len());
    }
}

pub async fn run_driver() {
    let baud_rate = 230400; // fixed baud rate for YDLiDAR T-mini Pro
    let mut port = Uart::new(Uarts::Uart4, baud_rate).unwrap();

    if !(cfg!(test)) {
        // In testing, disable flushing to receive dummy signals
        stop_scan_and_flush(&mut port);
    }

    check_device_health(&mut port).unwrap();
    let device_info = get_device_info(&mut port);
    if device_info.model_number != ydlidar_models::YdlidarModels::T_MINI_PRO {
        log::error!("This package can handle only YDLiDAR T-mini Pro.");
        return;
    }

    log::info!("Starting scan");
    start_scan(&mut port);

    let (scan_data_tx, scan_data_rx) = bounded::new::<u8>(Default::default());
    read_device_signal(port);

    // awkernel_async_lib::spawn(
    //     "read device signal".into(),
    //     (move || {
    //         read_device_signal(port, scan_data_tx)
    //     })(),
    //     SchedulerType::FIFO).await;

    // let (scan_tx, scan_rx) = bounded::new::<Scan>(Default::default());
    // awkernel_async_lib::spawn(
    //     "parse packets".into(),
    //     parse_packets(scan_data_rx, scan_tx),
    //     SchedulerType::FIFO).await;
}

pub async fn run_ydlidar_driver() {
    awkernel_async_lib::spawn(
        "YDLiDAR driver".into(),
        run_driver(),
        SchedulerType::FIFO,
    )
    .await;
}
