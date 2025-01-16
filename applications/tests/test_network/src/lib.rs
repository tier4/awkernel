#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use alloc::format;
use awkernel_async_lib::net::{tcp::TcpConfig, udp::UdpConfig, IpAddr};
use awkernel_lib::net::NetManagerError;

const INTERFACE_INDEX: u64 = 1;

// 10.0.2.0/24 is the IP address range of the Qemu's network.
// const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 64);

const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 52); // For experiment.

// 10.0.2.2 is the IP address of the Qemu's host.
// const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 2);

const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 1);

const UDP_DST_PORT: u16 = 26099;

const MULTICAST_ADDR: Ipv4Addr = Ipv4Addr::new(224, 0, 0, 123);
const MULTICAST_PORT: u16 = 20001;

pub async fn run() {
    awkernel_lib::net::add_ipv4_addr(INTERFACE_INDEX, INTERFACE_ADDR, 24);

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

    awkernel_async_lib::spawn(
        "test IPv4 multicast recv".into(),
        ipv4_multicast_recv_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        "test IPv4 multicast send".into(),
        ipv4_multicast_send_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn ipv4_multicast_send_test() {
    // Create a UDP socket on interface 0.
    let mut socket = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
        INTERFACE_INDEX,
        Default::default(),
    )
    .unwrap();

    let dst_addr = IpAddr::new_v4(MULTICAST_ADDR);

    loop {
        // Send a UDP packet.
        if let Err(e) = socket
            .send(b"Hello Awkernel!", &dst_addr, MULTICAST_PORT)
            .await
        {
            log::error!("Failed to send a UDP packet: {:?}", e);
            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            continue;
        }

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}

async fn ipv4_multicast_recv_test() {
    // Open a UDP socket for multicast.
    let mut config = UdpConfig::default();
    config.port = Some(MULTICAST_PORT);

    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(INTERFACE_INDEX, config)
            .unwrap();

    loop {
        // Join the multicast group.
        loop {
            match awkernel_lib::net::join_multicast_v4(INTERFACE_INDEX, MULTICAST_ADDR) {
                Ok(_) => {
                    log::debug!("Joined the multicast group.");
                    break;
                }
                Err(NetManagerError::SendError) => (),
                _ => {
                    log::error!("Failed to join the multicast group.");
                    return;
                }
            }

            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        }

        let mut buf = [0u8; 1024 * 2];

        for _ in 0..10 {
            // Receive a UDP packet.
            let result = socket.recv(&mut buf).await.unwrap();

            let msg = format!(
                "Received a Multicast packet from {}:{}: {}",
                result.1.get_addr(),
                result.2,
                core::str::from_utf8(&buf[..result.0]).unwrap()
            );

            log::debug!("{msg}");
        }

        // Leave the multicast group.
        loop {
            match awkernel_lib::net::leave_multicast_v4(INTERFACE_INDEX, MULTICAST_ADDR) {
                Ok(_) => {
                    log::debug!("Left the multicast group.");
                    break;
                }
                Err(NetManagerError::SendError) => (),
                Err(e) => {
                    log::error!("Failed to leave the multicast group. {e:?}");
                    return;
                }
            }

            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        }
    }
}

async fn tcp_connect_test() {
    let Ok(mut stream) = awkernel_async_lib::net::tcp::TcpStream::connect(
        INTERFACE_INDEX,
        IpAddr::new_v4(UDP_TCP_DST_ADDR),
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
        awkernel_async_lib::net::tcp::TcpListener::bind_on_interface(INTERFACE_INDEX, config)
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
    // Create a UDP socket on interface 0.
    let mut socket = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
        INTERFACE_INDEX,
        Default::default(),
    )
    .unwrap();

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
