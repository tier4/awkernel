#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use awkernel_async_lib::net::{udp::UdpConfig, IpAddr};
use awkernel_lib::ntp::{packet::NtpPacket, SignedDuration, SystemClock, SystemTime};

// 10.0.2.0/24 is the IP address range of the Qemu's network.
// const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 64);
// const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 52); // For experiment.
const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 122, 24); // libvirt

// time-a-g.nist.gov
// const NTP_SERVER_ADDR: Ipv4Addr = Ipv4Addr::new(129, 6, 15, 28);

// Execute this to start a local NTP server on host:
// $ scripts/ntpserver.py 0.0.0.0 26099
const NTP_SERVER_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 122, 1);
const NTP_SERVER_PORT: u16 = 26099;
const INTERFACE_ID: u64 = 0;

pub async fn run() {
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);

    awkernel_async_lib::spawn(
        "poll time from server".into(),
        poll_time_from_server(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "syncronize with server and adjust the system clock".into(),
        synchronize_with_server(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "get time from kernel".into(),
        get_time_from_kernel(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "set time from kernel".into(),
        set_time(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn get_time_from_server() -> Result<(SignedDuration, SignedDuration), ()> {
    let config = UdpConfig {
        addr: IpAddr::new_v4(INTERFACE_ADDR),
        port: Some(20000),
        ..Default::default()
    };
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(INTERFACE_ID, &config).map_err(
            |e| {
                log::error!("Failed to bind UDP socket: {:?}", e);
                ()
            },
        )?;
    let server_addr = IpAddr::new_v4(NTP_SERVER_ADDR);
    let mut buf = [0u8; 48];

    let mut packet = NtpPacket::new();
    let originate_ts = SystemClock::now().into();

    packet.transmit_timestamp = originate_ts;

    socket
        .send(&packet.to_bytes(), &server_addr, NTP_SERVER_PORT)
        .await
        .map_err(|e| {
            log::error!("Failed to send a NTP packet: {:?}", e);
        })?;

    socket.recv(&mut buf).await.unwrap();

    let destination_ts = SystemClock::now().into();
    let packet = NtpPacket::from_bytes(&buf);
    let (delay, ofs) = packet.parse_response(originate_ts, destination_ts);

    Ok((delay, ofs))
}

async fn poll_time_from_server() {
    for _ in 0..3 {
        match get_time_from_server().await {
            Ok((delay, ofs)) => {
                log::info!("Delay: {:?}", delay);
                log::info!("Offset: {:?}", ofs);
            }
            Err(_) => {
                log::error!("Failed to get time from server");
            }
        };

        awkernel_async_lib::sleep(Duration::from_secs(2)).await;
    }
}

async fn set_time() {
    SystemClock::set(1041379200_000_000_000); // 2003-11-01

    let clock = SystemClock::now();
    log::info!("set_time_from_packet: Current time: {:?}", clock);

    let st = SystemTime::new(1041379200_000_000_000);
    assert!(
        clock.duration_since(st).unwrap().as_micros() < 100,
        "Time set incorrectly",
    );
}

async fn get_time_from_kernel() {
    let clock = SystemClock::now();
    log::info!("get_time_from_packet: Current time: {:?}", clock);
}

async fn synchronize_with_server() {
    let (_delay, offset) = match get_time_from_server().await {
        Ok((delay, offset)) => (delay, offset),
        Err(_) => {
            log::error!("Failed to get time from server");
            return;
        }
    };

    log::info!("Time before adjustment: {:?}", SystemClock::now());
    SystemClock::adjust(offset);
    log::info!("Time set to: {:?}", SystemClock::now());
}
