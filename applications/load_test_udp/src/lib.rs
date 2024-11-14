#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use alloc::format;
use awkernel_async_lib::net::{tcp::TcpConfig, udp::UdpConfig, IpAddr};
use awkernel_lib::net::NetManagerError;

const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 0, 2);

const BASE_PORT: u16 = 20000;
const NUM_WORKERS: usize = 100;

pub async fn run() {
    awkernel_lib::net::add_ipv4_addr(1, INTERFACE_ADDR, 24);

    for worker_id in 0..NUM_WORKERS {
        let port = BASE_PORT + worker_id as u16;

        awkernel_async_lib::spawn(
            "test udp".into(),
            udp_server(port),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;
    }
}

async fn udp_server(port: u16) {
    let config = UdpConfig {
        addr: IpAddr::new_v4(Ipv4Addr::new(192, 168, 0, 2)),
        port: Some(port),
        ..Default::default()
    };

    let mut socket = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(1, config).unwrap();

    const MAX_DATAGRAM_SIZE: usize = 65_507;
    let mut buf = [0u8; MAX_DATAGRAM_SIZE];

    loop {
        match socket.recv(&mut buf).await {
            Ok((read_bytes, client_addr, port)) => {
                let received_data = &buf[..read_bytes];

                if let Err(e) = socket.send(&received_data, &client_addr, port).await {
                    log::error!("Failed to send a UDP packet: {:?}", e);
                    awkernel_async_lib::sleep(Duration::from_secs(1)).await;
                    continue;
                }
            }
            Err(e) => {
                log::error!("Error receiving data: {:?}", e);
            }
        }
    }
}
