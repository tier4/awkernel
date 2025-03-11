#![no_std]

extern crate alloc;

mod ntp;

use core::{net::Ipv4Addr, time::Duration};

use alloc::format;
use awkernel_async_lib::{
    net::{tcp::TcpConfig, udp::UdpConfig, IpAddr},
    uptime,
};
use awkernel_lib::net::NetManagerError;
use ntp::NtpTimestamp;

use crate::ntp::{parse_response, NtpPacket};

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
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);

    awkernel_async_lib::spawn(
        "test ntp".into(),
        ntp_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

fn now(offset: u64) -> NtpTimestamp {
    let uptime = uptime();
    NtpTimestamp(uptime + offset)
}

async fn ntp_test() {
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

    loop {
        let mut packet = NtpPacket::new();
        let originate_ts = now(offset);
        packet.transmit_timestamp = originate_ts;

        // Send a UDP packet
        if let Err(e) = socket
            .send(&packet.to_bytes(), &server_addr, UDP_DST_PORT)
            .await
        {
            log::error!("Failed to send a NTP packet: {:?}", e);
            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            continue;
        }

        // Receive a UDP packet.
        socket.recv(&mut buf).await.unwrap();

        let destination_ts = now(offset);
        let (delay, ofs) = parse_response(buf, originate_ts.into(), destination_ts.into());

        log::info!("Delay: {:?}", delay);
        log::info!("Offset: {:?}", ofs);

        awkernel_async_lib::sleep(Duration::from_secs(5)).await;
    }
}

async fn udp_test() {
    // Create a UDP socket on interface 0.
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(0, Default::default()).unwrap();

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
