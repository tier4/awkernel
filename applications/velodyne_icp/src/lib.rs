#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use awkernel_async_lib::net::udp::UdpConfig;
use awkernel_async_lib::net::IpAddr;
use awkernel_async_lib::pubsub;
use awkernel_async_lib::pubsub::{create_publisher, create_subscriber};
use awkernel_async_lib::pubsub::{Publisher, Subscriber};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::graphics;
use velodyne_driver::{parse_config, PointCloudCalculator};
use velodyne_driver::{PointProcessor, CHANNELS_PER_SEQUENCE, N_SEQUENCES};

use embedded_graphics::pixelcolor::Rgb888;
use embedded_graphics::prelude::RgbColor;

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::marker::{Send, Sync};
use core::net::Ipv4Addr;

const VLP16_PACKET_DATA_SIZE: usize = 1206;

// We can caputure only about four degrees per packet so we need to collect 75 packets to capture
// 360 degree scan
const PACKETS_PER_SCAN: usize = 75;

const SCREEN_SCALE: f64 = 25.;

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
    fn process(&mut self, sequence_index: usize, channel: usize, point: &velodyne_driver::Point) {
        assert!(!self.is_full());
        // Temporarily use only channel 1 in 16 scans to reduce the number of input 3D points for ICP
        // TODO Optimze ICP for speed up and use the whole input point cloud
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

const POSITION_TOPIC: &str = "position";
const SRC_SCAN_TOPIC: &str = "scan";
const DST_SCAN_TOPIC: &str = "target_scan";

fn create_default_publisher<T: Send + Sync + 'static>(
    topic_name: &'static str,
) -> Publisher<Arc<Box<T>>> {
    create_publisher::<Arc<Box<T>>>(topic_name.into(), pubsub::Attribute::default()).unwrap()
}

fn create_default_subscriber<T: Send + Sync + 'static>(
    topic_name: &'static str,
) -> Subscriber<Arc<Box<T>>> {
    create_subscriber::<Arc<Box<T>>>(topic_name.into(), pubsub::Attribute::default()).unwrap()
}

// Run ICP (Iterative Closest Point)
async fn icp() {
    let scan_subscriber = create_default_subscriber::<Scan>(SRC_SCAN_TOPIC);
    let dst_scan_publisher = create_default_publisher::<Scan>(DST_SCAN_TOPIC);
    let transform_publisher = create_default_publisher::<icp::Transform>(POSITION_TOPIC);

    // Regard the first arriving scan as the target point cloud and
    // estimate the transform from a received scan to the target point cloud in
    // every iteration.
    let mut maybe_icp: Option<icp::Icp2d> = None;
    let mut transform = icp::Transform::identity();
    let mut dst_scan: Arc<Box<Scan>> = Arc::default();
    loop {
        let scan_message: pubsub::Data<Arc<Box<Scan>>> = scan_subscriber.recv().await;
        let scan: Arc<Box<Scan>> = scan_message.data;

        if let Some(ref icp) = maybe_icp {
            transform = icp.estimate(&scan.points, &transform, 3);
            dst_scan_publisher.send(dst_scan.clone()).await;
            transform_publisher
                .send(Arc::new(Box::new(transform)))
                .await;
            continue;
        }

        dst_scan = scan; // keep the reference so that the scan will not be freed
        let icp = icp::Icp2d::new(&dst_scan.points);
        maybe_icp = Some(icp);
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

    // Invert Y-axis since y value increses as the screen coordinate goes down
    embedded_graphics::prelude::Point::new(u, -v) + *offset
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

fn get_xy(p: &icp::Vector3) -> icp::Vector2 {
    icp::Vector2::new(p[0], p[1])
}

fn draw_scan_points(
    scan: &Arc<Box<Scan>>,
    transform: &icp::Transform,
    screen_bbox: &embedded_graphics::primitives::Rectangle,
    color: &Rgb888,
) {
    let offset = screen_center(&screen_bbox);
    for p in scan.points.iter() {
        let b = transform.transform(&p);
        let x = b[(0, 0)];
        let y = b[(1, 0)];
        let point = to_screen_coordinate(&(x, y), SCREEN_SCALE, &offset);

        if is_out_of_screen(&point, &screen_bbox) {
            continue;
        }

        let _ = graphics::circle(point, 1, &color, 1, true);
    }
}

fn draw_axes(transform: &icp::Transform, screen_bbox: &embedded_graphics::primitives::Rectangle) {
    let t = transform.t;
    let x = transform.transform(&icp::Vector2::new(1.0, 0.0));
    let y = transform.transform(&icp::Vector2::new(0.0, 1.0));

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
    let src_scan_subscriber = create_default_subscriber::<Scan>(SRC_SCAN_TOPIC);
    let dst_scan_subscriber = create_default_subscriber::<Scan>(DST_SCAN_TOPIC);
    let transform_subscriber = create_default_subscriber::<icp::Transform>(POSITION_TOPIC);

    let identity = icp::Transform::identity();

    let screen_bbox = graphics::bounding_box();
    let offset = screen_center(&screen_bbox);

    let mut trajectory = Trajectory::new();
    loop {
        graphics::fill(&Rgb888::WHITE);

        let transform_message = transform_subscriber.recv().await;
        let transform: Arc<Box<icp::Transform>> = transform_message.data;
        draw_axes(&transform, &screen_bbox);

        let src_scan_message: pubsub::Data<Arc<Box<Scan>>> = src_scan_subscriber.recv().await;
        let dst_scan_message: pubsub::Data<Arc<Box<Scan>>> = dst_scan_subscriber.recv().await;

        let src_scan: Arc<Box<Scan>> = src_scan_message.data;
        let dst_scan: Arc<Box<Scan>> = dst_scan_message.data;

        draw_scan_points(&src_scan, &transform, &screen_bbox, &Rgb888::YELLOW);
        draw_scan_points(&dst_scan, &identity, &screen_bbox, &Rgb888::BLACK);

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

    // See velodyne manual for this IP addr configuration
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

    let scan_publisher = create_default_publisher::<Scan>(SRC_SCAN_TOPIC);

    let mut scan = Box::new(Scan::default());

    loop {
        socket.recv(&mut buf).await.unwrap();
        // Calculate the point cloud from the packet
        calculator.calculate(scan.as_mut(), &buf);

        // Publish the point cloud if we get the whole 360 degree scan
        scan.increment();
        if scan.is_full() {
            scan_publisher.send(Arc::new(scan)).await;
            scan = Box::new(Scan::default());
        }
    }
}

// Launched first
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
