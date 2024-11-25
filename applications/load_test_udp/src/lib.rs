#![no_std]

extern crate alloc;

use core::{net::Ipv4Addr, time::Duration};

use awkernel_async_lib::net::{udp::UdpConfig, IpAddr};

const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 0, 3);

const BASE_PORT: u16 = 20000;

pub async fn run() {
    //const NUM_TASKS: [usize; 11] = [1000, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000];
    const NUM_TASKS: [usize; 2] = [3, 5];
    awkernel_lib::net::add_ipv4_addr(1, INTERFACE_ADDR, 24);

    for num_task in NUM_TASKS {
        log::info!("num_task:{:?}", num_task);
        let mut join = alloc::vec::Vec::new();
        for task_id in 0..num_task {
            let port = BASE_PORT + task_id as u16;
            log::info!("port:{:?}", port);

            let hdl = awkernel_async_lib::spawn(
                "test udp".into(),
                udp_server(port),
                awkernel_async_lib::scheduler::SchedulerType::RR,
            )
            .await;

            join.push(hdl);
        }

        for hdl in join {
            let _ = hdl.join().await;
        }
    }
}

async fn udp_server(port: u16) {
    let config = UdpConfig {
        addr: IpAddr::new_v4(Ipv4Addr::new(192, 168, 0, 3)),
        port: Some(port),
        ..Default::default()
    };

    let mut socket = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(1, config).unwrap();

    const MAX_DATAGRAM_SIZE: usize = 65_507;
    let mut buf = [0u8; MAX_DATAGRAM_SIZE];

    loop {
        match socket.recv(&mut buf).await {
            Ok((read_bytes, client_addr, client_port)) => {
                if read_bytes == 1 {
                    break;
                }
                let received_data = &buf[..read_bytes];
                //log::info!(
                //"received_data:{:?} client_addr:{:?} client_port:{:?}",
                //received_data,
                //client_addr,
                //client_port
                //);

                if let Err(e) = socket.send(received_data, &client_addr, client_port).await {
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
