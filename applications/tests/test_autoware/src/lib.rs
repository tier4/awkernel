#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, collections::VecDeque, format, string::String, sync::Arc, vec, vec::Vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::net::IpAddr;
use awkernel_async_lib::scheduler::SchedulerType;
#[cfg(feature = "dag-send-period")]
use awkernel_async_lib::task::perf::get_period_count;
use awkernel_lib::delay::wait_microsec;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::net::Ipv4Addr;
use core::time::Duration;
use csv_core::{ReadRecordResult, Reader};
// Thread-safe state management using atomic operations
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
// Global gyro odometer core instance with proper synchronization
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};

use imu_corrector::{ImuCorrector, ImuWithCovariance, Transform};
use imu_driver::{Header, ImuMsg, TamagawaImuParser, Vector3};

use vehicle_velocity_converter::{
    reactor_helpers, Twist, TwistWithCovariance, TwistWithCovarianceStamped,
    VehicleVelocityConverter, VelocityReport,
};

use gyro_odometer::{GyroOdometerConfig, GyroOdometerCore};

use ekf_localizer::{EKFModule, EKFParameters, Point3D, Pose, PoseWithCovariance, Quaternion};

/// EKF Odometry structure for publishing (equivalent to C++ nav_msgs::msg::Odometry)
#[derive(Debug, Clone)]
pub struct EKFOdometry {
    pub header: imu_driver::Header,
    pub child_frame_id: &'static str,
    pub pose: PoseWithCovariance,
    pub twist: TwistWithCovariance,
}

const LOG_ENABLE: bool = true;

// EKF pose covariance (6x6 matrix flattened to array)
// Layout: [x, xy, xz, xr, xp, xy_yaw,
//          yx, y, yz, yr, yp, y_yaw,
//          zx, zy, z, zr, zp, z_yaw,
//          rx, ry, rz, r, rp, r_yaw,
//          px, py, pz, pr, p, p_yaw,
//          yaw_x, yaw_y, yaw_z, yaw_r, yaw_p, yaw]
const EKF_POSE_COVARIANCE: [f64; 36] = [
    0.0225, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0225, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0225, 0.0, 0.0,
    0.0, 0.0, 0.0, 0.0, 0.000625, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.000625, 0.0, 0.0, 0.0, 0.0, 0.0,
    0.0, 0.000625,
];

// EKF twist covariance (6x6 matrix flattened to array)
// For twist, we mainly care about linear.x (vx) and angular.z (wz)
// Layout: [vx_x, vx_y, vx_z, vx_rx, vx_ry, vx_wz,
//          vy_x, vy_y, vy_z, vy_rx, vy_ry, vy_wz,
//          vz_x, vz_y, vz_z, vz_rx, vz_ry, vz_wz,
//          wx_x, wx_y, wx_z, wx_rx, wx_ry, wx_wz,
//          wy_x, wy_y, wy_z, wy_rx, wy_ry, wy_wz,
//          wz_x, wz_y, wz_z, wz_rx, wz_ry, wz]
// Based on Autoware's typical twist uncertainty (0.01 m/s for linear, 0.01 rad/s for angular)
const EKF_TWIST_COVARIANCE: [f64; 36] = [
    0.01, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.01, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.01, 0.0, 0.0, 0.0,
    0.0, 0.0, 0.0, 0.0001, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0001, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0,
    0.0001,
];

static LAST_DR_TIMESTAMP: AtomicU64 = AtomicU64::new(0);

const INTERFACE_ID: u64 = 0;

// 10.0.2.0/24 is the IP address range of the Qemu's network.
const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 64);

// 10.0.2.2 is the IP address of the Qemu's host.
const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 2);

const UDP_DST_PORT: u16 = 26099;
const TCP_DST_PORT: u16 = 26099;
const TCP_LISTEN_PORT: u16 = 26100;

static mut LATEST_JSON_DATA: Option<String> = None;
static JSON_DATA_READY: AtomicBool = AtomicBool::new(false);
static JSON_DATA_LENGTH: AtomicUsize = AtomicUsize::new(0);

const IMU_CSV_DATA_STR: &str = include_str!("../imu_raw.csv");
const VELOCITY_CSV_DATA_STR: &str = include_str!("../velocity_status.csv");

#[derive(Clone, Debug)]
struct ImuCsvRow {
    timestamp: u64,
    orientation: imu_driver::Quaternion,
    angular_velocity: imu_driver::Vector3,
    linear_acceleration: imu_driver::Vector3,
}

#[derive(Clone, Debug)]
struct VelocityCsvRow {
    timestamp: u64,
    longitudinal_velocity: f64,
    lateral_velocity: f64,
    heading_rate: f64,
}

static mut IMU_CSV_DATA: Option<Vec<ImuCsvRow>> = None;
static mut VELOCITY_CSV_DATA: Option<Vec<VelocityCsvRow>> = None;
static IMU_CSV_COUNT: Mutex<usize> = Mutex::new(0);
static VELOCITY_CSV_COUNT: Mutex<usize> = Mutex::new(0);

// Global EKF Localizer instance with proper synchronization
static EKF_LOCALIZER: AtomicPtr<EKFModule> = AtomicPtr::new(null_mut());

#[cfg(feature = "dag-send-period")]
type DagMsg<T> = (T, u32);
#[cfg(not(feature = "dag-send-period"))]
type DagMsg<T> = T;

#[cfg(feature = "dag-send-period")]
fn pack_dag_msg<T>(value: T, period_id: u32) -> DagMsg<T> {
    (value, period_id)
}

#[cfg(not(feature = "dag-send-period"))]
fn pack_dag_msg<T>(value: T, _period_id: u32) -> DagMsg<T> {
    value
}

#[cfg(feature = "dag-send-period")]
fn unpack_dag_msg<T>(msg: DagMsg<T>) -> (T, u32) {
    msg
}

#[cfg(not(feature = "dag-send-period"))]
fn unpack_dag_msg<T>(msg: DagMsg<T>) -> (T, u32) {
    (msg, 0)
}

#[cfg(feature = "dag-send-period")]
fn current_period_id(dag_id: u32) -> u32 {
    get_period_count(dag_id as usize) as u32
}

#[cfg(not(feature = "dag-send-period"))]
fn current_period_id(_dag_id: u32) -> u32 {
    0
}

pub async fn run() {
    wait_microsec(1000000);

    if let Err(e) = initialize_csv_data() {
        log::warn!("Failed to initialize CSV data: {}", e);
    }

    log::info!("Starting Autoware test application with simplified TCP networking");

    let dag = create_dag();
    let dag_id = dag.get_id();

    dag.register_periodic_reactor::<_, (DagMsg<i32>, DagMsg<i32>, DagMsg<i32>)>(
        "start_dummy_data".into(),
        move || -> (DagMsg<i32>, DagMsg<i32>, DagMsg<i32>) {
            let period_id = current_period_id(dag_id);
            (
                pack_dag_msg(1, period_id),
                pack_dag_msg(2, period_id),
                pack_dag_msg(3, period_id),
            )
        },
        vec![
            Cow::from("start_imu"),
            Cow::from("start_vel"),
            Cow::from("start_pose"),
        ],
        SchedulerType::GEDF(5),
        Duration::from_millis(50),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<ImuMsg>,)>(
        "imu_driver".into(),
        move |(start_msg,): (DagMsg<i32>,)| -> (DagMsg<ImuMsg>,) {
            let (_a, period_id) = unpack_dag_msg(start_msg);
            let mut node = MCSNode::new();
            let mut count_guard = IMU_CSV_COUNT.lock(&mut node);
            let count = *count_guard;
            let data = unsafe { IMU_CSV_DATA.as_ref() };

            let imu_msg = if let Some(csv_data) = data {
                if csv_data.is_empty() {
                    let mut parser = TamagawaImuParser::new("imu_link");
                    let awkernel_timestamp = get_awkernel_uptime_timestamp();
                    let static_dummy_data = parser.generate_static_dummy_data(awkernel_timestamp);
                    parser
                        .parse_binary_data(&static_dummy_data, awkernel_timestamp)
                        .unwrap_or_default()
                } else {
                    let idx = count % csv_data.len();
                    let row = &csv_data[idx];
                    let awkernel_timestamp = get_awkernel_uptime_timestamp();
                    ImuMsg {
                        header: Header {
                            frame_id: "imu_link",
                            timestamp: awkernel_timestamp,
                        },
                        orientation: row.orientation.clone(),
                        angular_velocity: row.angular_velocity.clone(),
                        linear_acceleration: row.linear_acceleration.clone(),
                    }
                }
            } else {
                let mut parser = TamagawaImuParser::new("imu_link");
                let awkernel_timestamp = get_awkernel_uptime_timestamp();
                let static_dummy_data = parser.generate_static_dummy_data(awkernel_timestamp);
                parser
                    .parse_binary_data(&static_dummy_data, awkernel_timestamp)
                    .unwrap_or_default()
            };

            *count_guard += 1;
            if *count_guard >= 5700 {
                *count_guard = 0;
                log::info!("rust_e2e_app: finish csv for IMU");
                loop {}
            }

            if LOG_ENABLE {
                log::debug!(
                    "IMU data in imu_driver_node,num={}, timestamp={}",
                    count,
                    imu_msg.header.timestamp
                );
            }

            (pack_dag_msg(imu_msg, period_id),)
        },
        vec![Cow::from("start_imu")],
        vec![Cow::from("imu_data")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<TwistWithCovarianceStamped>,)>(
        "vehicle_velocity_converter".into(),
        move |(start_msg,): (DagMsg<i32>,)| -> (DagMsg<TwistWithCovarianceStamped>,) {
            let (_b, period_id) = unpack_dag_msg(start_msg);
            let converter = VehicleVelocityConverter::default();
            
            let mut node = MCSNode::new();
            let mut count_guard = VELOCITY_CSV_COUNT.lock(&mut node);
            let count = *count_guard;
            let data = unsafe { VELOCITY_CSV_DATA.as_ref() };
            
            let csv_data = data.expect("VELOCITY_CSV_DATA must be initialized");
            let idx = count % csv_data.len();
            let row = &csv_data[idx];
            let awkernel_timestamp = get_awkernel_uptime_timestamp();
            let velocity_report = VelocityReport {
                header: Header {
                    frame_id: "base_link",
                    timestamp: awkernel_timestamp,
                },
                longitudinal_velocity: row.longitudinal_velocity,
                lateral_velocity: row.lateral_velocity,
                heading_rate: row.heading_rate,
            };
            
            *count_guard += 1;
            if *count_guard >= 5700 {
                *count_guard = 0;
                log::info!("rust_e2e_app: finish csv for Velocity");
                loop {}
            }
            
            let twist_msg = converter.convert_velocity_report(&velocity_report);
            
            if LOG_ENABLE {
                log::debug!("Vehicle velocity converter: Converted velocity report to twist - linear.x={:.3}, angular.z={:.3}, awkernel_timestamp={}",
                    twist_msg.twist.twist.linear.x,
                    twist_msg.twist.twist.angular.z,
                    twist_msg.header.timestamp
                );
            }
            
            (pack_dag_msg(twist_msg, period_id),)
        },
        vec![Cow::from("start_vel")],
        vec![Cow::from("velocity_twist")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<ImuMsg>,), (DagMsg<ImuWithCovariance>,)>(
        "imu_corrector".into(),
        |(imu_msg,): (DagMsg<ImuMsg>,)| -> (DagMsg<ImuWithCovariance>,) {
            let (imu_msg, period_id) = unpack_dag_msg(imu_msg);
            let corrector = ImuCorrector::new();
            let corrected = corrector.correct_imu_with_covariance(&imu_msg, None);
            (pack_dag_msg(corrected, period_id),)
        },
        vec![Cow::from("imu_data")],
        vec![Cow::from("corrected_imu_data")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<ImuWithCovariance>, DagMsg<TwistWithCovarianceStamped>), (DagMsg<TwistWithCovarianceStamped>,)>(
        "gyro_odometer".into(),
        |(imu_msg, vehicle_msg): (DagMsg<ImuWithCovariance>, DagMsg<TwistWithCovarianceStamped>)| -> (DagMsg<TwistWithCovarianceStamped>,) {
            let (imu_with_cov, period_imu) = unpack_dag_msg(imu_msg);
            let (vehicle_twist, _period_twist) = unpack_dag_msg(vehicle_msg);
            let current_timestamp = imu_with_cov.header.timestamp;
            let current_time = get_awkernel_uptime_timestamp();
            
            let gyro_odometer = match gyro_odometer::get_or_initialize() {
                Ok(core) => core,
                Err(_) => {
                    return (pack_dag_msg(reactor_helpers::create_empty_twist(current_timestamp), period_imu),);
                }
            };

            gyro_odometer.add_vehicle_twist(vehicle_twist);
            gyro_odometer.add_imu(imu_with_cov);

            match gyro_odometer.process_and_get_result(current_time) {
                Some(result) => (pack_dag_msg(gyro_odometer.process_result(result), period_imu),),
                None => (pack_dag_msg(reactor_helpers::create_empty_twist(current_timestamp), period_imu),)
            }
        },
        vec![Cow::from("corrected_imu_data"),Cow::from("velocity_twist")],
        vec![Cow::from("twist_with_covariance")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<Pose>,)>(
        "pose_dummy_generator".into(),
        move |(start_msg,): (DagMsg<i32>,)| -> (DagMsg<Pose>,) {
            let (_counter, period_id) = unpack_dag_msg(start_msg);
            let x = 0.0;
            let y = 0.0;
            let z = 0.0;

            let pose = Pose {
                position: Point3D { x, y, z },
                orientation: Quaternion {
                    x: 0.0,
                    y: 0.0,
                    z: 0.0,
                    w: 1.0,
                },
            };

            (pack_dag_msg(pose, period_id),)
        },
        vec![Cow::from("start_pose")],
        vec![Cow::from("dummy_pose")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<Pose>, DagMsg<TwistWithCovarianceStamped>), (DagMsg<Pose>, DagMsg<EKFOdometry>)>(
        "ekf_localizer".into(),
        |(pose_msg, twist_msg): (DagMsg<Pose>, DagMsg<TwistWithCovarianceStamped>)| -> (DagMsg<Pose>, DagMsg<EKFOdometry>) {
            let (pose, period_pose) = unpack_dag_msg(pose_msg);
            let (twist, _period_twist) = unpack_dag_msg(twist_msg);
            if get_ekf_localizer().is_none() {
                if let Err(_e) = initialize_ekf_localizer() {
                    return (pack_dag_msg(pose, period_pose), pack_dag_msg(EKFOdometry {
                        header: imu_driver::Header {
                            frame_id: "map",
                            timestamp: twist.header.timestamp,
                        },
                        child_frame_id: "base_link",
                        pose: PoseWithCovariance {
                            pose: pose,
                            covariance: EKF_POSE_COVARIANCE,
                        },
                        twist: TwistWithCovariance {
                            twist: Twist {
                                linear: imu_driver::Vector3::new(0.0, 0.0, 0.0),
                                angular: imu_driver::Vector3::new(0.0, 0.0, 0.0),
                            },
                            covariance: EKF_TWIST_COVARIANCE,
                        },
                    }, period_pose));
                }
            }
            
            let ekf = get_ekf_localizer().unwrap();

            static mut INITIALIZED: bool = false;
            unsafe {
                if !INITIALIZED {
                    ekf.initialize(pose.clone());
                    LAST_DR_TIMESTAMP.store(twist.header.timestamp, Ordering::Relaxed);
                    INITIALIZED = true;
                }
            }

            // Use a fixed 50ms timestep to match the Autoware publisher cadence.
            const FIXED_DT: f64 = 0.05;
            let dt = FIXED_DT;

            if dt > 0.0 {
                ekf.predict(dt);
            }

            let vx = twist.twist.twist.linear.x;
            let wz = twist.twist.twist.angular.z;
            ekf.update_velocity(vx, wz);

            let ekf_pose = ekf.get_current_pose(false);

            let pose_covariance = ekf.get_current_pose_covariance();
            let twist_covariance = ekf.get_current_twist_covariance();

            let ekf_twist = ekf.get_current_twist();

            let odometry = EKFOdometry {
                header: imu_driver::Header {
                    frame_id: "map",
                    timestamp: twist.header.timestamp,
                },
                child_frame_id: "base_link",
                pose: PoseWithCovariance {
                    pose: ekf_pose.clone(),
                    covariance: pose_covariance,
                },
                twist: TwistWithCovariance {
                    twist: Twist {
                        linear: imu_driver::Vector3::new(ekf_twist.linear.x, ekf_twist.linear.y, ekf_twist.linear.z),
                        angular: imu_driver::Vector3::new(ekf_twist.angular.x, ekf_twist.angular.y, ekf_twist.angular.z),
                    },
                    covariance: twist_covariance,
                },
            };

            (pack_dag_msg(ekf_pose, period_pose), pack_dag_msg(odometry, period_pose))
        },
        vec![Cow::from("dummy_pose"), Cow::from("twist_with_covariance")],
        vec![Cow::from("estimated_pose"), Cow::from("ekf_odometry")],
        SchedulerType::GEDF(5),
    )
    .await;

    dag.register_sink_reactor::<_, (DagMsg<Pose>, DagMsg<EKFOdometry>)>(
        "ekf_sink".into(),
        move |(pose_msg, odom_msg): (DagMsg<Pose>, DagMsg<EKFOdometry>)| {
            let (_pose, _period_pose) = unpack_dag_msg(pose_msg);
            let (ekf_odom, _period_odom) = unpack_dag_msg(odom_msg);

            let json_data = format!(
                r#"{{"header":{{"frame_id":"{}","timestamp":{}}},"child_frame_id":"{}","pose":{{"pose":{{"position":{{"x":{:.6},"y":{:.6},"z":{:.6}}},"orientation":{{"x":{:.6},"y":{:.6},"z":{:.6},"w":{:.6}}}}},"covariance":[{}]}},"twist":{{"twist":{{"linear":{{"x":{:.6},"y":{:.6},"z":{:.6}}},"angular":{{"x":{:.6},"y":{:.6},"z":{:.6}}}}},"covariance":[{}]}}}}"#,
                ekf_odom.header.frame_id,
                ekf_odom.header.timestamp,
                ekf_odom.child_frame_id,
                ekf_odom.pose.pose.position.x,
                ekf_odom.pose.pose.position.y,
                ekf_odom.pose.pose.position.z,
                ekf_odom.pose.pose.orientation.x,
                ekf_odom.pose.pose.orientation.y,
                ekf_odom.pose.pose.orientation.z,
                ekf_odom.pose.pose.orientation.w,
                ekf_odom.pose.covariance.iter().map(|&x| format!("{:.6}", x)).collect::<Vec<_>>().join(","),
                ekf_odom.twist.twist.linear.x,
                ekf_odom.twist.twist.linear.y,
                ekf_odom.twist.twist.linear.z,
                ekf_odom.twist.twist.angular.x,
                ekf_odom.twist.twist.angular.y,
                ekf_odom.twist.twist.angular.z,
                ekf_odom.twist.covariance.iter().map(|&x| format!("{:.6}", x)).collect::<Vec<_>>().join(",")
            );

            save_json_data_to_global(json_data);
        },
        vec![Cow::from("estimated_pose"), Cow::from("ekf_odometry")],
        SchedulerType::GEDF(5),
        Duration::from_millis(50),
    )
    .await;

    let result = finish_create_dags(&[dag.clone()]).await;

    match result {
        Ok(_) => {
            log::info!("Autoware test application DAGs created successfully");
        }
        Err(errors) => {
            log::error!("Failed to create Autoware test application DAGs");
            for error in errors {
                log::error!("- {error}");
            }
        }
    }

    log::info!("Autoware test application DAG completed");

    log::info!("=== Network test start ===");
    log::info!("Interface ID: {}", INTERFACE_ID);
    log::info!("Interface IP: {}", INTERFACE_ADDR);
    log::info!("Destination IP: {}", UDP_TCP_DST_ADDR);
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);
    log::info!(
        "Configured IPv4 address {} on interface {}",
        INTERFACE_ADDR,
        INTERFACE_ID
    );

    log::info!("Waiting for network stack initialization...");
    awkernel_async_lib::sleep(Duration::from_secs(2)).await;

    log::info!("Starting periodic UDP sender task");
    start_periodic_udp_sender().await;

    log::info!("Waiting for JSON data to become ready...");
    let mut wait_count = 0;
    const MAX_WAIT_COUNT: u32 = 3;

    while !JSON_DATA_READY.load(Ordering::Relaxed) && wait_count < MAX_WAIT_COUNT {
        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        wait_count += 1;
    }

    if JSON_DATA_READY.load(Ordering::Relaxed) {
    } else {
        log::warn!("JSON data was not ready. Periodic UDP sender task remains waiting");
    }

    log::info!("Autoware test application completed");
}

fn initialize_csv_data() -> Result<(), &'static str> {
    unsafe {
        if IMU_CSV_DATA.is_none() {
            let imu_data = parse_imu_csv(IMU_CSV_DATA_STR)?;
            if imu_data.is_empty() {
                return Err("IMU CSV is empty");
            }
            log::info!("Loaded IMU CSV data: {} rows", imu_data.len());
            IMU_CSV_DATA = Some(imu_data);
        }

        if VELOCITY_CSV_DATA.is_none() {
            let velocity_data = parse_velocity_csv(VELOCITY_CSV_DATA_STR)?;
            if velocity_data.is_empty() {
                return Err("Velocity CSV is empty");
            }
            log::info!("Loaded velocity CSV data: {} rows", velocity_data.len());
            VELOCITY_CSV_DATA = Some(velocity_data);
        }
    }

    Ok(())
}

fn parse_imu_csv(csv: &str) -> Result<Vec<ImuCsvRow>, &'static str> {
    let mut rows = Vec::new();

    parse_csv_records(csv, |fields| {
        if fields.len() < 12 {
            return Err("IMU CSV has insufficient columns");
        }

        let timestamp = parse_timestamp(fields[0], fields[1])?;
        let orientation = imu_driver::Quaternion {
            x: parse_f64(fields[2])?,
            y: parse_f64(fields[3])?,
            z: parse_f64(fields[4])?,
            w: parse_f64(fields[5])?,
        };
        let angular_velocity = imu_driver::Vector3::new(
            parse_f64(fields[6])?,
            parse_f64(fields[7])?,
            parse_f64(fields[8])?,
        );
        let linear_acceleration = imu_driver::Vector3::new(
            parse_f64(fields[9])?,
            parse_f64(fields[10])?,
            parse_f64(fields[11])?,
        );

        rows.push(ImuCsvRow {
            timestamp,
            orientation,
            angular_velocity,
            linear_acceleration,
        });
        Ok(())
    })?;

    Ok(rows)
}

fn parse_velocity_csv(csv: &str) -> Result<Vec<VelocityCsvRow>, &'static str> {
    let mut rows = Vec::new();

    parse_csv_records(csv, |fields| {
        if fields.len() < 5 {
            return Err("Velocity CSV has insufficient columns");
        }

        let timestamp = parse_timestamp(fields[0], fields[1])?;
        let longitudinal_velocity = parse_f64(fields[2])?;
        let lateral_velocity = parse_f64(fields[3])?;
        let heading_rate = parse_f64(fields[4])?;

        rows.push(VelocityCsvRow {
            timestamp,
            longitudinal_velocity,
            lateral_velocity,
            heading_rate,
        });
        Ok(())
    })?;

    Ok(rows)
}

fn parse_csv_records<F>(csv: &str, mut on_record: F) -> Result<(), &'static str>
where
    F: FnMut(&[&str]) -> Result<(), &'static str>,
{
    let mut reader = Reader::new();
    let mut input = csv.as_bytes();
    let mut output = vec![0u8; 4096];
    let mut ends = vec![0usize; 32];
    let mut header_skipped = false;

    loop {
        let (result, in_read, _out_written, num_fields) =
            reader.read_record(input, &mut output, &mut ends);
        input = &input[in_read..];

        if matches!(result, ReadRecordResult::OutputFull) {
            return Err("CSV output buffer is too small");
        }

        if num_fields == 0 {
            if matches!(result, ReadRecordResult::InputEmpty | ReadRecordResult::End) {
                break;
            }
            continue;
        }

        let mut fields: Vec<&str> = Vec::with_capacity(num_fields);
        let mut start = 0usize;
        for i in 0..num_fields {
            let end = ends[i];
            let slice = &output[start..end];
            let field = core::str::from_utf8(slice).map_err(|_| "Failed to decode CSV UTF-8")?;
            fields.push(field);
            start = end;
        }

        if !header_skipped {
            header_skipped = true;
        } else {
            on_record(&fields)?;
        }

        if matches!(result, ReadRecordResult::End) {
            break;
        }
    }

    Ok(())
}

fn parse_timestamp(sec: &str, nsec: &str) -> Result<u64, &'static str> {
    let sec_val = parse_u64(sec)?;
    let nsec_val = parse_u64(nsec)?;
    let ts = sec_val
        .checked_mul(1_000_000_000)
        .and_then(|v| v.checked_add(nsec_val))
        .ok_or("Timestamp calculation overflowed")?;
    Ok(ts)
}

fn parse_u64(field: &str) -> Result<u64, &'static str> {
    let trimmed = field.trim();
    if trimmed.is_empty() {
        return Ok(0);
    }
    trimmed
        .parse::<u64>()
        .map_err(|_| "Failed to parse u64")
}

fn parse_f64(field: &str) -> Result<f64, &'static str> {
    let trimmed = field.trim();
    if trimmed.is_empty() {
        return Ok(0.0);
    }
    trimmed
        .parse::<f64>()
        .map_err(|_| "Failed to parse f64")
}

// Returns monotonic uptime in nanoseconds clamped to u64.
fn get_awkernel_uptime_timestamp() -> u64 {
    let uptime_nanos = awkernel_lib::delay::uptime_nano();
    if uptime_nanos > u64::MAX as u128 {
        u64::MAX
    } else {
        uptime_nanos as u64
    }
}

pub async fn start_periodic_udp_sender() {
    awkernel_async_lib::spawn(
        "periodic_udp_sender".into(),
        periodic_udp_sender_task(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;
}

async fn periodic_udp_sender_task() {
    let socket_result = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
        INTERFACE_ID,
        &Default::default(),
    );

    let mut socket = match socket_result {
        Ok(socket) => socket,
        Err(e) => {
            log::error!("Periodic UDP sender task: failed to create UDP socket: {:?}", e);
            return;
        }
    };

    let dst_addr = IpAddr::new_v4(UDP_TCP_DST_ADDR);
    let mut counter = 0;

    loop {
        if !JSON_DATA_READY.load(Ordering::Relaxed) {
            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            continue;
        }

        let json_data = unsafe { LATEST_JSON_DATA.as_ref().map(|s| s.clone()) };

        if let Some(data) = json_data {
            match socket.send(data.as_bytes(), &dst_addr, UDP_DST_PORT).await {
                Ok(_) => {
                    counter += 1;
                    log::info!(
                        "Periodic UDP sender task: send success #{} ({} bytes)",
                        counter,
                        data.len()
                    );

                    let mut buf = [0u8; 1024];
                    if let Some(Ok((n, src_addr, src_port))) = awkernel_async_lib::timeout(
                        Duration::from_millis(100),
                        socket.recv(&mut buf),
                    )
                    .await
                    {
                        if let Ok(response) = core::str::from_utf8(&buf[..n]) {
                            log::debug!(
                                "Periodic UDP sender task: response received: {}:{} - {}",
                                src_addr.get_addr(),
                                src_port,
                                response
                            );
                        }
                    }
                }
                Err(e) => {
                    log::warn!("Periodic UDP sender task: send failed: {:?}", e);
                }
            }
        } else {
            log::warn!("Periodic UDP sender task: failed to get JSON data");
        }

        awkernel_async_lib::sleep(Duration::from_millis(5)).await;
    }
}

fn save_json_data_to_global(json_data: String) {
    unsafe {
        LATEST_JSON_DATA = Some(json_data.clone());
    }
    JSON_DATA_READY.store(true, Ordering::Relaxed);
    JSON_DATA_LENGTH.store(json_data.len(), Ordering::Relaxed);
}

// Transform error handling function
fn get_transform_safely(from_frame: &str, to_frame: &str) -> Result<Transform, &'static str> {
    // For now, return identity transform
    // In a real implementation, this would query the transform tree
    if from_frame == to_frame {
        Ok(Transform::identity())
    } else {
        // Simulate transform lookup
        Ok(Transform::identity())
    }
}

// Initialize EKF Localizer safely
fn initialize_ekf_localizer() -> Result<(), &'static str> {
    let params = EKFParameters::default();
    let ekf = EKFModule::new(params);

    // Allocate on heap and store pointer
    let boxed_ekf = alloc::boxed::Box::new(ekf);
    let ptr = alloc::boxed::Box::into_raw(boxed_ekf);

    // Try to store the pointer atomically
    let old_ptr = EKF_LOCALIZER.compare_exchange(
        null_mut(),
        ptr,
        AtomicOrdering::Acquire,
        AtomicOrdering::Relaxed,
    );

    match old_ptr {
        Ok(_) => Ok(()),
        Err(_) => {
            // Another thread already initialized it, clean up our allocation
            unsafe {
                let _ = alloc::boxed::Box::from_raw(ptr);
            }
            Ok(())
        }
    }
}

// Get EKF Localizer safely
fn get_ekf_localizer() -> Option<&'static mut EKFModule> {
    let ptr = EKF_LOCALIZER.load(AtomicOrdering::Acquire);
    if ptr.is_null() {
        None
    } else {
        unsafe { Some(&mut *ptr) }
    }
}
