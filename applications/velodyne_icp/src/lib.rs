#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_async_lib::net::tcp::TcpConfig;
use awkernel_async_lib::net::udp::UdpConfig;
use awkernel_async_lib::net::IpAddr;
use core::net::Ipv4Addr;
use core::time::Duration;


const VLP16_PACKET_DATA_SIZE: usize = 1206;

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
    }
}

async fn udp() {
    log::info!("Start the connection");

    let dst_addr = IpAddr::new_v4(Ipv4Addr::new(0, 0, 0, 0));

    let udp_config = UdpConfig {
        addr: dst_addr,
        port: Some(2368),
        rx_buffer_size: VLP16_PACKET_DATA_SIZE,
        tx_buffer_size: 1024 * 64,
    };

    let mut buf = [0u8; VLP16_PACKET_DATA_SIZE];

    let mut socket =
        awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(0, udp_config).unwrap();

    loop {
        socket.recv(&mut buf).await.unwrap();
        log::info!("Received a packet: {:?}", buf);
    }
}

pub async fn run() {
    awkernel_async_lib::spawn("udp".into(), udp(), SchedulerType::FIFO).await;
}
