#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use awkernel_async_lib::net::udp::UdpConfig;
use awkernel_async_lib::net::IpAddr;
use awkernel_async_lib::pubsub;
use awkernel_async_lib::pubsub::{create_publisher, create_subscriber};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::graphics;
use velodyne_driver::{parse_config, PointCloudCalculator};
use velodyne_driver::{PointProcessor, CHANNELS_PER_SEQUENCE, N_SEQUENCES};

use embedded_graphics::geometry;
use embedded_graphics::pixelcolor::Rgb888;
use embedded_graphics::prelude::RgbColor;

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::borrow::Borrow;
use core::net::Ipv4Addr;

const VLP16_PACKET_DATA_SIZE: usize = 1206;

const PACKETS_PER_SCAN: usize = 75;

const SCREEN_SCALE: f64 = 25.;

const N_USED_CHANNELS: usize = 1;

#[derive(PartialEq)]
struct Scan {
    packet_index: usize,
    pub points: [icp::Vector2; PACKETS_PER_SCAN * N_SEQUENCES * N_USED_CHANNELS],
}

impl Default for Scan {
    fn default() -> Self {
        Scan {
            packet_index: 0,
            points: [icp::Vector2::zeros(); PACKETS_PER_SCAN * N_SEQUENCES * N_USED_CHANNELS],
        }
    }
}

impl PointProcessor for Scan {
    fn process(&mut self, sequence_index: usize, channel: usize, point: &velodyne_driver::Point) {
        assert!(!self.is_full());

        let c = if channel == 1 {
            0
        } else {
            return;
        };

        let (x, y, _z) = point;
        let index = self.packet_index * N_SEQUENCES * N_USED_CHANNELS
            + sequence_index * N_USED_CHANNELS
            + c;
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

const POSITION_TOPIC: &str = "position";
const SCAN_TOPIC: &str = "scan";

fn run_icp(
    prior: &icp::Transform,
    src_scan: &Arc<Box<Scan>>,
    dst_scan: &Arc<Box<Scan>>,
) -> icp::Transform {
    let src: &Box<Scan> = src_scan.borrow();
    let dst: &Box<Scan> = dst_scan.borrow();
    icp::icp_2dscan(prior, &src.points, &dst.points)
}

async fn icp() {
    let scan_subscriber =
        create_subscriber::<Arc<Box<Scan>>>(SCAN_TOPIC.into(), pubsub::Attribute::default())
            .unwrap();
    let transform_publisher = create_publisher::<Arc<Box<icp::Transform>>>(
        POSITION_TOPIC.into(),
        pubsub::Attribute::default(),
    )
    .unwrap();

    let mut transform = icp::Transform::identity();
    let mut maybe_reference_scan = None;
    loop {
        let scan_message: pubsub::Data<Arc<Box<Scan>>> = scan_subscriber.recv().await;
        let scan: Arc<Box<Scan>> = scan_message.data;

        if let Some(ref reference_scan) = maybe_reference_scan {
            transform = run_icp(&transform, &reference_scan, &scan);
            transform_publisher
                .send(Arc::new(Box::new(transform)))
                .await;
            continue;
        }

        maybe_reference_scan = Some(scan);
    }
}

fn to_screen_coordinate(
    point: &(f64, f64),
    scale: f64,
    offset: &embedded_graphics::prelude::Point,
) -> embedded_graphics::prelude::Point {
    let (x, y) = point;
    let u = (x * scale) as i32;
    let v = (y * scale) as i32;
    embedded_graphics::prelude::Point::new(u, v) + *offset
}

fn screen_center(
    screen: &embedded_graphics::primitives::Rectangle,
) -> embedded_graphics::prelude::Point {
    embedded_graphics::prelude::Point::new(
        (screen.size.width / 2) as i32,
        (screen.size.height / 2) as i32,
    )
}

fn is_out_of_screen(
    p: &embedded_graphics::prelude::Point,
    screen: &embedded_graphics::primitives::Rectangle,
) -> bool {
    p.x < 0 || screen.size.width as i32 <= p.x || p.y < 0 || screen.size.height as i32 <= p.y
}

fn draw_scan_points(
    scan: &Arc<Box<Scan>>,
    transform: &icp::Transform,
    screen_bbox: &embedded_graphics::primitives::Rectangle,
) {
    let offset = screen_center(&screen_bbox);
    let inv_transform = transform.inverse();
    for p in scan.points.iter() {
        let b = inv_transform.transform(&p);
        let x = b[(0, 0)];
        let y = b[(1, 0)];
        let point = to_screen_coordinate(&(x, y), SCREEN_SCALE, &offset);

        if is_out_of_screen(&point, &screen_bbox) {
            continue;
        }

        let _ = graphics::circle(point, 1, &Rgb888::BLACK, 1, true);
    }
}

fn draw_axes(transform: &icp::Transform, screen_bbox: &embedded_graphics::primitives::Rectangle) {
    let t = transform.t;
    let x = transform.transform(&icp::Vector2::new(1.0, 0.));
    let y = transform.transform(&icp::Vector2::new(0., 1.0));

    let offset = screen_center(&screen_bbox);
    let origin = to_screen_coordinate(&(t[0], t[1]), SCREEN_SCALE, &offset);
    let x_axis = to_screen_coordinate(&(x[0], x[1]), SCREEN_SCALE, &offset);
    let y_axis = to_screen_coordinate(&(y[0], y[1]), SCREEN_SCALE, &offset);
    let _ = graphics::line(origin, x_axis, &Rgb888::RED, 1);
    let _ = graphics::line(origin, y_axis, &Rgb888::BLUE, 1);
}

struct Trajectory {
    coordinates: Vec<embedded_graphics::prelude::Point>,
}

impl Trajectory {
    fn new() -> Self {
        Trajectory {
            coordinates: Vec::new(),
        }
    }

    fn add(&mut self, coordinate: &embedded_graphics::prelude::Point) {
        self.coordinates.push(*coordinate);
    }

    fn draw(&self) {
        for i in 0..self.coordinates.len() - 1 {
            let _ = graphics::line(
                self.coordinates[i],
                self.coordinates[i + 1],
                &Rgb888::GREEN,
                1,
            );
        }
    }
}

async fn draw() {
    let scan_subscriber =
        create_subscriber::<Arc<Box<Scan>>>(SCAN_TOPIC.into(), pubsub::Attribute::default())
            .unwrap();
    let transform_subscriber = create_subscriber::<Arc<Box<icp::Transform>>>(
        POSITION_TOPIC.into(),
        pubsub::Attribute::default(),
    )
    .unwrap();

    let screen_bbox = graphics::bounding_box();
    let offset = screen_center(&screen_bbox);

    let mut trajectory = Trajectory::new();
    loop {
        graphics::fill(&Rgb888::WHITE);
        let scan_message: pubsub::Data<Arc<Box<Scan>>> = scan_subscriber.recv().await;
        let scan: Arc<Box<Scan>> = scan_message.data;

        let transform_message = transform_subscriber.recv().await;
        let transform: Arc<Box<icp::Transform>> = transform_message.data;

        draw_axes(&transform, &screen_bbox);
        draw_scan_points(&scan, &transform, &screen_bbox);

        let (x, y) = (transform.t[0], transform.t[1]);
        let curr = to_screen_coordinate(&(x, y), SCREEN_SCALE, &offset);

        if is_out_of_screen(&curr, &screen_bbox) {
            continue;
        }

        log::info!("current position on screen = {}", curr);

        trajectory.add(&curr);
        trajectory.draw();

        graphics::flush();
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

    let scan_publisher =
        create_publisher::<Arc<Box<Scan>>>(SCAN_TOPIC.into(), pubsub::Attribute::default())
            .unwrap();

    let mut scan = Box::new(Scan::default());

    loop {
        socket.recv(&mut buf).await.unwrap();
        calculator.calculate(scan.as_mut(), &buf);
        scan.increment();

        if scan.is_full() {
            scan_publisher.send(Arc::new(scan)).await;
            scan = Box::new(Scan::default());
        }
    }
}

pub async fn run() {
    awkernel_async_lib::spawn("draw".into(), draw(), SchedulerType::FIFO).await;
    awkernel_async_lib::spawn(
        "receive_scan_packets".into(),
        receive_scan_packets(),
        SchedulerType::FIFO,
    )
    .await;
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
