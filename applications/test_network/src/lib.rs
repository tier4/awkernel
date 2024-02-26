#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use alloc::format;
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

    awkernel_async_lib::spawn(
        "test tcp connect".into(),
        tcp_connect_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn tcp_connect_test() {
    let Ok(mut stream) = awkernel_async_lib::net::tcp::TcpStream::connect(
        0,
        IpAddr::new_v4(Ipv4Addr::new(192, 168, 100, 2)),
        8080,
        Default::default(),
    ) else {
        return;
    };

    stream.send(b"Hello, Awkernel!\r\n").await.unwrap();
}

async fn tcp_listen_test() {
    let config = TcpConfig {
        port: Some(8080),
        ..Default::default()
    };

    let Ok(mut tcp_listener) =
        awkernel_async_lib::net::tcp::TcpListener::bind_on_interface(0, config)
    else {
        return;
    };

    loop {
        let Ok(tcp_stream) = tcp_listener.accept().await else {
            log::error!("Failed to accept TCP connection.");
            continue;
        };

        log::debug!("Accepted a TCP connection. {:?}", tcp_stream.remote_addr());

        awkernel_async_lib::spawn(
            "bogus HTTP server".into(),
            bogus_http_server(tcp_stream),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;
    }
}

async fn bogus_http_server(mut stream: awkernel_async_lib::net::tcp::TcpStream) {
    let mut buf = [0u8; 1024 * 2];

    let n = stream.recv(&mut buf).await.unwrap();

    let request = core::str::from_utf8(&buf[..n]).unwrap();
    log::debug!("Received HTTP request: {}", request);

    static MSG: &str = "<html><body><h1>Hello, Awkernel!</h1></body></html>\r\n";

    let len = MSG.len();
    let response = format!("HTTP/1.0 200 OK\r\nContent-Type: text/html; charset=UTF-8\r\nContent-Length: {len}\r\n\r\n");
    stream.send(response.as_bytes()).await.unwrap();
    stream.send(MSG.as_bytes()).await.unwrap();
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
        let _rtt = t1 - t0;

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
