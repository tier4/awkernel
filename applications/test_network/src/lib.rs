#![no_std]

extern crate alloc;

use core::{convert::Into, net::Ipv4Addr, time::Duration};

use awkernel_async_lib::net::{tcp::TcpConfig, IpAddr};

pub async fn run() {
    awkernel_lib::net::add_ipv4_addr(0, Ipv4Addr::new(192, 168, 100, 64), 24);

    awkernel_async_lib::spawn(
        "test udp".into(),
        udp_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "test tcp listen".into(),
        tcp_listen_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn tcp_listen_test() {
    let mut config = TcpConfig::default();
    config.port = Some(8080);

    let Ok(mut tcp_listener) = awkernel_async_lib::net::tcp::TcpListener::bind_on_interface(
        0,
        config
    ) else {
        panic!("Failed to bind TCP listener.");
    };

    loop {
        let Ok(mut tcp_stream) = tcp_listener.accept().await else {
            log::error!("Failed to accept TCP connection.");
            continue;
        };

        tcp_stream.send(b"Hello Awkernel!\r\n").await.unwrap();

        log::debug!("Accepted a TCP connection.");
    }
}

async fn udp_test() {
    // Create a UDP socket on interface 1.
    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(0, Default::default()).unwrap();

    let dst_addr = IpAddr::new_v4(Ipv4Addr::new(192, 168, 100, 2));

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
        // log::debug!("UDP RTT: {} us", rtt);

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
