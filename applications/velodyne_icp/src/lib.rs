#![no_std]

extern crate alloc;

use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_async_lib::net::udp::UdpConfig;
use awkernel_async_lib::net::IpAddr;
use velodyne_driver::{Point, PointCloudCalculator, parse_config};
use velodyne_driver::{N_SEQUENCES, CHANNELS_PER_SEQUENCE, PointProcessor};
use awkernel_async_lib::pubsub::{create_publisher, create_subscriber};
use awkernel_async_lib::pubsub;

use core::borrow::Borrow;
use alloc::boxed::Box;
use alloc::sync::Arc;
use core::net::Ipv4Addr;

const VLP16_PACKET_DATA_SIZE: usize = 1206;

const PACKETS_PER_SCAN: usize = 75;

#[derive(PartialEq)]
struct Scan {
    packet_index: usize,
    pub points: [icp::Vector2; PACKETS_PER_SCAN * N_SEQUENCES],
}

impl Default for Scan {
    fn default() -> Self {
        Scan {
            packet_index: 0,
            points: [icp::Vector2::zeros(); PACKETS_PER_SCAN * N_SEQUENCES],
        }
    }
}

impl PointProcessor for Scan {
    fn process(&mut self, sequence_index: usize, channel: usize, point: &Point) {
        assert!(!self.is_full());
        if channel != 1 {
            return;
        }

        let (x, y, _z) = point;
        let index = self.packet_index * N_SEQUENCES + sequence_index;
        self.points[index] = icp::Vector2::new(*x, *y);
    }
}

impl Scan {
    fn increment(&mut self) {
        self.packet_index += 1;
    }

    fn is_full(&self) -> bool {
        self.packet_index == PACKETS_PER_SCAN
    }
}

const SCAN_TOPIC: &str = "scan";

fn run_icp(transform: &icp::Transform, src_scan: &Arc<Box<Scan>>, dst_scan: &Arc<Box<Scan>>) -> icp::Transform {
    let src: &Box<Scan> = src_scan.borrow();
    let dst: &Box<Scan> = dst_scan.borrow();
    icp::icp_2dscan(transform, &src.points, &dst.points)
}

async fn icp() {
    let subscriber =
        create_subscriber::<Arc<Box<Scan>>>(SCAN_TOPIC.into(), pubsub::Attribute::default()).unwrap();

    let mut transform = icp::Transform::identity();
    let mut maybe_reference_scan = None;
    loop {
        let scan_message: pubsub::Data<Arc<Box<Scan>>> = subscriber.recv().await;
        let scan: Arc<Box<Scan>> = scan_message.data;

        if let Some(ref reference_scan) = maybe_reference_scan {
           transform = run_icp(&transform, &scan, &reference_scan);
        }

        log::info!("transform.R:");
        log::info!("{:?}", transform.rot);
        log::info!("transform.t:");
        log::info!("{:?}", transform.t);
        maybe_reference_scan = Some(scan);
    }
}

async fn receive_scan_packets() {
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

    let publisher =
        create_publisher::<Arc<Box<Scan>>>(SCAN_TOPIC.into(), pubsub::Attribute::default()).unwrap();

    let mut scan = Box::new(Scan::default());

    loop {
        socket.recv(&mut buf).await.unwrap();
        calculator.calculate(scan.as_mut(), &buf);
        scan.increment();

        if scan.is_full() {
            publisher.send(Arc::new(scan)).await;
            scan = Box::new(Scan::default());
        }
    }
}

pub async fn run() {
    awkernel_async_lib::spawn("udp".into(), receive_scan_packets(), SchedulerType::FIFO).await;
    awkernel_async_lib::spawn("icp".into(), icp(), SchedulerType::FIFO).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scan() {
        let mut scan = Scan::default();

        let mut i = 0;
        for _packet_index in 0..PACKETS_PER_SCAN {
            for sequence_index in 0..N_SEQUENCES {
                for channel in 0..CHANNELS_PER_SEQUENCE {
                    let i_f64 = i as f64;
                    scan.process(sequence_index, channel, &(i_f64, i_f64, i_f64));
                    i += 1;
                }
            }
            scan.increment();
        }

        for i in 0..PACKETS_PER_SCAN * N_SEQUENCES * CHANNELS_PER_SEQUENCE {
            let i_f64 = i as f64;
            let expected = icp::Vector3::new(i_f64, i_f64, i_f64);
            assert_eq!(scan.points[i], expected);
        }
    }
}
