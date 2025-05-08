#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use alloc::format;
use awkernel_async_lib::{
    net::{tcp::TcpConfig, udp::UdpConfig, IpAddr},
    uptime,
};
use awkernel_lib::{
    net::NetManagerError, ntp::packet::NtpPacket, ntp::timestamp::NtpTimestamp, ntp::SystemClock,
};

// 10.0.2.0/24 is the IP address range of the Qemu's network.
const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 64);

// const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 52); // For experiment.

// 10.0.2.2 is the IP address of the Qemu's host.
const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 2);

const UDP_DST_PORT: u16 = 26099;

const MULTICAST_ADDR: Ipv4Addr = Ipv4Addr::new(224, 0, 0, 123);
const MULTICAST_PORT: u16 = 20001;

const NTP_SERVER_ADDR: Ipv4Addr = Ipv4Addr::new(129, 6, 15, 28); // time-a-g.nist.gov
const INTERFACE_ID: u64 = 0;

pub async fn run() {
    awkernel_lib::net::set_default_gateway_ipv4(INTERFACE_ID, DEFAULT_GATEWAY).unwrap();
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);

    let a = awkernel_lib::net::get_default_gateway_ipv4(INTERFACE_ID).unwrap();
    log::error!("gateway {a:?}");

    // awkernel_async_lib::spawn(
    //     "test udpp".into(),
    //     udp_test(),
    //     awkernel_async_lib::scheduler::SchedulerType::FIFO,
    // )
    // .await;

    awkernel_async_lib::spawn(
        "test ntp".into(),
        synchronize_ntp(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "test ntp".into(),
        get_time_from_kernel(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "test ntp".into(),
        set_time_from_packet(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

/// Get the current time in NTP format.
/// start_time is the time when the system started in microseconds since the UNIX epoch.
fn now(start_time: u64) -> NtpTimestamp {
    let uptime_us = uptime() * 1000;
    NtpTimestamp::from_epoch_us(start_time + uptime_us)
}

async fn synchronize_ntp() {
    log::error!("test_ntp being called");
    log::debug!("test_ntp debug");
    log::info!("test_ntp info");
    log::warn!("test_ntp warn");
    let config = UdpConfig {
        addr: IpAddr::new_v4(INTERFACE_ADDR),
        port: Some(20000),
        ..Default::default()
    };
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(INTERFACE_ID, config).unwrap();
    let server_addr = IpAddr::new_v4(NTP_SERVER_ADDR);
    let mut buf = [0u8; 48];

    // offset + uptime = ntp time
    let mut offset: u64 = 1729585092_000_000;
    let upt = uptime(); // uptime in us

    let stub_resp_buf = NtpPacket {
        li_vn_mode: 28,
        stratum: 3,
        poll: 0,
        precision: -26,
        root_delay: 7306,
        root_dispersion: 28,
        ref_id: 184158212,
        ref_timestamp: NtpTimestamp(16970635707839472514),
        origin_timestamp: NtpTimestamp(16970635902767787245),
        recv_timestamp: NtpTimestamp(16970635902849344207),
        transmit_timestamp: NtpTimestamp(16970635902849753858),
    }
    .to_bytes();

    loop {
        // log::info!("sending packet");
        // let mut packet = NtpPacket::new();

        let originate_ts = now(offset);
        let originate_ts = NtpTimestamp(16970635902767787245);

        // packet.transmit_timestamp = originate_ts;

        // // Send a UDP packet
        // if let Err(e) = socket
        //     .send(&packet.to_bytes(), &server_addr, UDP_DST_PORT)
        //     .await
        // {
        //     log::error!("Failed to send a NTP packet: {:?}", e);
        //     awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        //     continue;
        // }

        // Receive a UDP packet.
        log::info!("sent packet. waiting...");
        // socket.recv(&mut buf).await.unwrap();
        let buf = stub_resp_buf;

        let destination_ts = now(offset);
        let packet = NtpPacket::from_bytes(&buf);
        let (delay, ofs) = packet.parse_response(originate_ts, destination_ts);

        log::info!("Delay: {:?}", delay);
        log::info!("Offset: {:?}", ofs);

        awkernel_async_lib::sleep(Duration::from_secs(5)).await;
    }
}

async fn udp_test() {
    // Create a UDP socket on interface 0.
    let config = UdpConfig {
        addr: IpAddr::new_v4(INTERFACE_ADDR),
        port: Some(2006),
        ..Default::default()
    };
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(INTERFACE_ID, config).unwrap();

    let dst_addr = IpAddr::new_v4(UDP_TCP_DST_ADDR);

    let mut buf = [0u8; 1024 * 2];

    loop {
        let t0 = awkernel_lib::delay::uptime();

        // Send a UDP packet.
        if let Err(e) = socket
            .send(b"Hello Awkernel!", &dst_addr, UDP_DST_PORT)
            .await
        {
            log::error!("Failed to send a UDP packet: {:?}", e);
            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            continue;
        }

        // Receive a UDP packet.
        socket.recv(&mut buf).await.unwrap();

        let t1 = awkernel_lib::delay::uptime();
        let _rtt = t1 - t0;

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}

async fn set_time_from_packet() {
    SystemClock::set(1041379200_000_000_000); // 2003-11-01

    let clock = SystemClock::now();
    log::info!("set_time_from_packet: Current time: {:?}", clock);
}

async fn get_time_from_kernel() {
    let clock = SystemClock::now();
    log::info!("get_time_from_packet: Current time: {:?}", clock);
}
