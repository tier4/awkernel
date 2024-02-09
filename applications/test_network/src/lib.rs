#![no_std]

extern crate alloc;

use core::{convert::Into, net::Ipv4Addr, time::Duration};

const NETWORK_SERVICE_NAME: &str = "test network";

pub async fn run() {
    awkernel_lib::net::add_ipv4_addr(1, Ipv4Addr::new(192, 168, 100, 64), 24);

    awkernel_async_lib::spawn(
        NETWORK_SERVICE_NAME.into(),
        udp_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn udp_test() {
    // Create a UDP socket on interface 1.
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(1, 0, 1024 * 64).unwrap();

    let dst_addr = awkernel_lib::net::udp_socket::IpAddr::new_v4(Ipv4Addr::new(192, 168, 100, 1));

    let mut buf = [0u8; 1024 * 2];

    loop {
        let t0 = awkernel_lib::delay::uptime();

        // Send a UDP packet.
        socket
            .send(b"Hello Awkernel!", &dst_addr, 26099)
            .await
            .unwrap();

        // Receive a UDP packet.
        socket.recv(&mut buf).await.unwrap();

        let t1 = awkernel_lib::delay::uptime();
        let rtt = t1 - t0;
        log::debug!("UDP RTT: {} us", rtt);

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
