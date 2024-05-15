#![no_std]

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_async_lib::net::udp::UdpConfig;
use awkernel_async_lib::net::IpAddr;
use velodyne_driver::{Point, PointCloudCalculator, parse_config};
use velodyne_driver::{N_SEQUENCES, CHANNELS_PER_SEQUENCE, PointProcessor};
use awkernel_async_lib::pubsub::{create_publisher, create_subscriber};
use awkernel_async_lib::pubsub;

use core::net::Ipv4Addr;

use ndarray::Array2;

const VLP16_PACKET_DATA_SIZE: usize = 1206;

const N_PACKETS_PER_SCAN: usize = 75;

struct Scan {
    packet_index: usize,
    pub points: Array2<f64>,
}

impl Default for Scan {
    fn default() -> Self {
        Scan {
            packet_index: 0,
            points: Array2::zeros((N_SEQUENCES * CHANNELS_PER_SEQUENCE, 3)),
        }
    }
}

impl PointProcessor for Scan {
    fn process(&mut self, sequence_index: usize, channel: usize, point: &Point) {
        let (x, y, z) = point;
        let index = sequence_index * CHANNELS_PER_SEQUENCE + channel;
        self.points[[index, 0]] = *x;
        self.points[[index, 1]] = *y;
        self.points[[index, 2]] = *z;
    }
}

impl Scan {
    fn try_get(&self) -> Option<&Array2<f64>> {
        if self.packet_index != N_PACKETS_PER_SCAN {
            return None;
        }
        Some(&self.points)
    }
}

const SCAN_TOPIC: &str = "scan";

async fn scan_buffer() {
    let subscriber =
        create_subscriber::<Array2<f64>>(SCAN_TOPIC.into(), pubsub::Attribute::default()).unwrap();

    loop {
    }
}

async fn receive_scan() {
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

    let vlp16_config_str = include_str!("../VLP16db.yaml");
    let config = parse_config(vlp16_config_str).unwrap();
    let calculator = PointCloudCalculator::new(&config);

    let publisher = create_publisher::<Array2<f64>>(SCAN_TOPIC.into(), pubsub::Attribute::default()).unwrap();

    let mut scan = Scan::default();

    loop {
        socket.recv(&mut buf).await.unwrap();
        calculator.calculate(&mut scan, &buf);
        if let Some(points) = scan.try_get() {
            publisher.send(points.clone());
        };
    }
}

pub async fn run() {
    awkernel_async_lib::spawn("udp".into(), receive_scan(), SchedulerType::FIFO).await;
}
