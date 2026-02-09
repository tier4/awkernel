#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec, vec::Vec, collections::VecDeque, string::String, format, sync::Arc};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::net::{add_ipv4_addr, poll_interface, get_all_interface};
use awkernel_async_lib::net::{tcp::TcpStream, tcp::TcpConfig, udp::{UdpConfig, UdpSocketError},IpAddr};
use awkernel_lib::delay::wait_microsec;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::time::Duration;
use core::net::Ipv4Addr;
use csv_core::{Reader, ReadRecordResult};
// Thread-safe state management using atomic operations
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize,Ordering};
// Global gyro odometer core instance with proper synchronization
use core::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use core::ptr::null_mut;


// IMU ドライバーライブラリをインポート
use imu_driver::{ImuMsg,TamagawaImuParser, Header, Vector3};
use imu_corrector::{ImuCorrector, ImuWithCovariance, Transform};

// Vehicle Velocity Converter ライブラリをインポート（C++のpubsub機能に対応）
use vehicle_velocity_converter::{
    VehicleVelocityConverter, VelocityReport, TwistWithCovarianceStamped,
    TwistWithCovariance, Twist, reactor_helpers};

// Gyro Odometer ライブラリをインポート
use gyro_odometer::{
    GyroOdometerCore, GyroOdometerConfig};

// EKF Localizer ライブラリをインポート
use ekf_localizer::{EKFModule, EKFParameters, Pose, Point3D, Quaternion, PoseWithCovariance};
// COMMENTED OUT: 手動積分用の関数をコメントアウトしたためlibmは不要
// use libm::{atan2, cos, sin};

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
    0.0225, 0.0,    0.0,    0.0,      0.0,      0.0,
    0.0,    0.0225, 0.0,    0.0,      0.0,      0.0,
    0.0,    0.0,    0.0225, 0.0,      0.0,      0.0,
    0.0,    0.0,    0.0,    0.000625, 0.0,      0.0,
    0.0,    0.0,    0.0,    0.0,      0.000625, 0.0,
    0.0,    0.0,    0.0,    0.0,      0.0,      0.000625,
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
    0.01,   0.0,    0.0,    0.0,     0.0,     0.0,
    0.0,    0.01,   0.0,    0.0,     0.0,     0.0,
    0.0,    0.0,    0.01,   0.0,     0.0,     0.0,
    0.0,    0.0,    0.0,    0.0001,  0.0,     0.0,
    0.0,    0.0,    0.0,    0.0,     0.0001,  0.0,
    0.0,    0.0,    0.0,    0.0,     0.0,     0.0001,
];

static LAST_DR_TIMESTAMP: AtomicU64 = AtomicU64::new(0);

// ネットワーク状態管理
const INTERFACE_ID: u64 = 0;

// 10.0.2.0/24 is the IP address range of the Qemu's network.
const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 64);

// const INTERFACE_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 52); // For experiment.

// 10.0.2.2 is the IP address of the Qemu's host.
const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(10, 0, 2, 2);

// const UDP_TCP_DST_ADDR: Ipv4Addr = Ipv4Addr::new(192, 168, 100, 1); // For experiment.

const UDP_DST_PORT: u16 = 26099;
const TCP_DST_PORT: u16 = 26099;
const TCP_LISTEN_PORT: u16 = 26100;

// JSONデータ保存用のグローバル変数
static mut LATEST_JSON_DATA: Option<String> = None;
static JSON_DATA_READY: AtomicBool = AtomicBool::new(false);
static JSON_DATA_LENGTH: AtomicUsize = AtomicUsize::new(0);

// CSVデータ埋め込み
const IMU_CSV_DATA_STR: &str = include_str!("../imu_raw.csv");
const VELOCITY_CSV_DATA_STR: &str = include_str!("../velocity_status.csv");

// CSVパース結果の保存
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

// COMMENTED OUT: 手動積分用のDR_POSEはEKF内部状態からポーズを取得するようになったため不要
// static mut DR_POSE: Option<Pose> = None;


pub async fn run() {
    wait_microsec(1000000);

    if let Err(e) = initialize_csv_data() {
        log::warn!("CSVデータの初期化に失敗しました: {}", e);
    }

    //log::info!("Starting Autoware test application with simplified TCP networking");
    
    // 初期ネットワークインターフェース情報を表示
    //print_network_interfaces();

    let dag = create_dag();

    // ダミーデータ送信用リアクター
    // MODIFIED: 周期を10msから50msに変更（Autowareのekf_data_publisher.pyと同じ周期）
    // これにより、CSVデータの消費速度が両システムで一致する
    dag.register_periodic_reactor::<_, (i32,i32,i32)>(
        "start_dummy_data".into(),
        || -> (i32,i32,i32) {
            
                       
            return (1, 2, 3); // 通常のデータ処理用の値
        },
        vec![Cow::from("start_imu"),Cow::from("start_vel"),Cow::from("start_pose")],
        SchedulerType::GEDF(5),
        Duration::from_millis(50)  // CHANGED: 10ms -> 50ms (Autowareと同じ)
    )
    .await;

    // IMU driver node (periodic_reactor) - Dummy data generator
    dag.register_reactor::<_, (i32,),(ImuMsg,)>(
        "imu_driver".into(),
        move |(a,):(i32,)| -> (ImuMsg,) {
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
                    count, imu_msg.header.timestamp
                );
            }

            (imu_msg,)
        },
        vec![Cow::from("start_imu")],
        vec![Cow::from("imu_data")],
        SchedulerType::GEDF(5),
    )
    .await;

    // Vehicle Velocity Converter node - VelocityReport to TwistWithCovarianceStamped converter
    dag.register_reactor::<_, (i32,), (TwistWithCovarianceStamped,)>(
        "vehicle_velocity_converter".into(),
        move |(b,): (i32,)| -> (TwistWithCovarianceStamped,) {
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
            
            (twist_msg,)
        },
        vec![Cow::from("start_vel")], // Subscribe to start_vel topic
        vec![Cow::from("velocity_twist")], // Publish to twist_with_covariance topic
        SchedulerType::GEDF(5),
    )
    .await;

    //Imu Corrector
    dag.register_reactor::<_, (ImuMsg,), (ImuWithCovariance,)>(
        "imu_corrector".into(),
        |(imu_msg,): (ImuMsg,)| -> (ImuWithCovariance,) {
            
            let corrector = ImuCorrector::new();
            // Use the enhanced corrector that outputs ImuWithCovariance
            let corrected = corrector.correct_imu_with_covariance(&imu_msg, None);
            // if LOG_ENABLE {
            //     log::debug!("IMU corrected in imu_corrector node with covariance");
            // }
            (corrected,)
        },
        vec![Cow::from("imu_data")],
        vec![Cow::from("corrected_imu_data")],
        SchedulerType::GEDF(5),
    )
    .await;

    // Gyro Odometer node - Simplified single processing step
    dag.register_reactor::<_, (ImuWithCovariance, TwistWithCovarianceStamped,), (TwistWithCovarianceStamped,)>(
        "gyro_odometer".into(),
        |(imu_with_cov, vehicle_twist): (ImuWithCovariance, TwistWithCovarianceStamped)| -> (TwistWithCovarianceStamped,) {
            let current_timestamp = imu_with_cov.header.timestamp;
            let current_time = get_awkernel_uptime_timestamp();
            
            // Get or initialize gyro odometer core
            let gyro_odometer = match gyro_odometer::get_or_initialize() {
                Ok(core) => core,
                Err(_) => {
                    return (reactor_helpers::create_empty_twist(current_timestamp),);
                }
            };

            // Add both messages to queues (both arrive together in test_autoware)
            gyro_odometer.add_vehicle_twist(vehicle_twist);
            gyro_odometer.add_imu(imu_with_cov);
            
            // Process once with current time and return result
            match gyro_odometer.process_and_get_result(current_time) {
                Some(result) => (gyro_odometer.process_result(result),),
                None => (reactor_helpers::create_empty_twist(current_timestamp),)
            }
        },
        vec![Cow::from("corrected_imu_data"),Cow::from("velocity_twist")],
        vec![Cow::from("twist_with_covariance")],
        SchedulerType::GEDF(5),
    )
    .await;

    // Pose dummy data generator reactor
    dag.register_reactor::<_, (i32,), (Pose,)>(
        "pose_dummy_generator".into(),
        move |(counter,): (i32,)| -> (Pose,) {
            // Generate dummy pose data that moves in a circle
            // let time = counter as f64 * 0.1; // Time progression
            // let radius = 10.0; // Circle radius
            // let angular_velocity = 0.5; // rad/s
            
            // aip_x1_description/config/sensors_calibration.yaml
            // if needed, comment out and use fixed values below
            // let x = 0.86419;
            // let y = 0.0;
            // let z = 2.18096;
            // let yaw = angular_velocity * time;
            // for initial pose 
            let x = 0.0;
            let y = 0.0;
            let z = 0.0;
            
            let pose = Pose {
                position: Point3D { x,y,z},
                orientation: Quaternion {
                    x: 0.0,
                    y: 0.0,
                    z: 0.0,
                    w: 1.0,
                },
            };
            
            // if LOG_ENABLE {
            //     log::debug!("Generated dummy pose: x={:.3}, y={:.3}, yaw={:.3}, counter={}",
            //         pose.position.x, pose.position.y, yaw, counter);
            // }
            
            (pose,)
        },
        vec![Cow::from("start_pose")],
        vec![Cow::from("dummy_pose")],
        SchedulerType::GEDF(5),
    )
    .await;

    // EKF Localizer reactor - combines pose and twist data
    // MODIFIED: 手動積分（integrated_pose）を廃止し、EKFの内部状態から直接ポーズを取得するように変更
    dag.register_reactor::<_, (Pose, TwistWithCovarianceStamped), (Pose, EKFOdometry)>(
        "ekf_localizer".into(),
        |(pose, twist): (Pose, TwistWithCovarianceStamped)| -> (Pose, EKFOdometry) {
            // Initialize EKF Localizer if not already done
            if get_ekf_localizer().is_none() {
                if let Err(e) = initialize_ekf_localizer() {
                    // if LOG_ENABLE {
                        // log::error!("Failed to initialize EKF Localizer: {}", e);
                    // }
                    return (pose, EKFOdometry {
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
                    });
                }
            }
            
            let ekf = get_ekf_localizer().unwrap();
            
            // Initialize EKF with first pose if not already initialized
            static mut INITIALIZED: bool = false;
            unsafe {
                if !INITIALIZED {
                    ekf.initialize(pose.clone());
                    // COMMENTED OUT: 手動積分用の変数は使用しない
                    // DR_POSE = Some(pose.clone());
                    LAST_DR_TIMESTAMP.store(twist.header.timestamp, Ordering::Relaxed);
                    INITIALIZED = true;
                    // if LOG_ENABLE {
                        // log::info!("EKF Localizer initialized with initial pose");
                    // }
                }
            }
            
            // Predict step using measured time gap
            // MODIFIED: CSVタイムスタンプ差ではなく、固定dtを使用
            // Autowareのekf_data_publisher.pyは50ms固定周期でデータをpublishする
            // EKFは実際の経過時間（システムクロック）を使用するため、
            // Awkernelも同様に固定dtを使用することで挙動を一致させる
            //
            // OLD CODE (CSVタイムスタンプ差を使用):
            // let current_ts = twist.header.timestamp;
            // let last_ts = LAST_DR_TIMESTAMP.swap(current_ts, Ordering::Relaxed);
            // let dt = if last_ts == 0 {
            //     0.0
            // } else {
            //     (current_ts.saturating_sub(last_ts)) as f64 / 1_000_000_000.0
            // };
            //
            // NEW CODE: 固定dt = 50ms (0.05秒) - Autowareと同じ周期
            const FIXED_DT: f64 = 0.05;  // 50ms in seconds
            let dt = FIXED_DT;

            if dt > 0.0 {
                ekf.predict(dt);
            }

            // ADDED: EKFに速度観測値を更新（カルマンフィルタの観測更新ステップ）
            let vx = twist.twist.twist.linear.x;
            let wz = twist.twist.twist.angular.z;
            ekf.update_velocity(vx, wz);

            // COMMENTED OUT: 手動積分（Dead Reckoning）処理
            // Autowareとの精度向上のため、EKF内部状態から直接ポーズを取得するように変更
            // let mut integrated_pose = unsafe { DR_POSE.clone().unwrap_or_else(|| pose.clone()) };
            // let yaw = quaternion_to_yaw(&integrated_pose.orientation);
            // let vx = twist.twist.twist.linear.x;
            // let vy = twist.twist.twist.linear.y;
            // let vz = twist.twist.twist.linear.z;
            // let wz = twist.twist.twist.angular.z;
            //
            // if dt > 0.0 {
            //     let cos_yaw = cos(yaw);
            //     let sin_yaw = sin(yaw);
            //     let new_yaw = yaw + wz * dt;
            //
            //     integrated_pose.position.x += (vx * cos_yaw - vy * sin_yaw) * dt;
            //     integrated_pose.position.y += (vx * sin_yaw + vy * cos_yaw) * dt;
            //     integrated_pose.position.z += vz * dt;
            //     integrated_pose.orientation = yaw_to_quaternion(new_yaw);
            // }
            //
            // unsafe {
            //     DR_POSE = Some(integrated_pose.clone());
            // }
            
            // MODIFIED: EKFの内部状態から直接ポーズを取得
            // get_biased_yaw=false でyaw_biasを考慮したポーズを取得
            let ekf_pose = ekf.get_current_pose(false);
            
            // MODIFIED: EKFから動的な共分散を取得（固定値ではなく）
            // これにより、走行距離や時間の経過に伴う不確かさの変化を反映
            let pose_covariance = ekf.get_current_pose_covariance();
            let twist_covariance = ekf.get_current_twist_covariance();
            
            // COMMENTED OUT: 固定共分散の使用
            // let pose_covariance = EKF_POSE_COVARIANCE;
            // let twist_covariance = EKF_TWIST_COVARIANCE;
            
            // Get EKF's estimated twist
            let ekf_twist = ekf.get_current_twist();
            
            // Create odometry message using EKF's estimated pose and twist
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
                    // Use EKF's estimated twist instead of input twist
                    twist: Twist {
                        linear: imu_driver::Vector3::new(ekf_twist.linear.x, ekf_twist.linear.y, ekf_twist.linear.z),
                        angular: imu_driver::Vector3::new(ekf_twist.angular.x, ekf_twist.angular.y, ekf_twist.angular.z),
                    },
                    covariance: twist_covariance,
                },
            };
            
            // if LOG_ENABLE {
                // log::debug!("EKF Localizer: ekf_pose=({:.3}, {:.3}, {:.3}), dt={:.3}, awkernel_timestamp={}",
                    // ekf_pose.position.x, ekf_pose.position.y, ekf_pose.position.z, dt, odometry.header.timestamp);
                // log::debug!("EKF Localizer: ekf_twist=({:.3}, {:.3}, {:.3}), angular=({:.3}, {:.3}, {:.3})",
                    // ekf_twist.linear.x, ekf_twist.linear.y, ekf_twist.linear.z,
                    // ekf_twist.angular.x, ekf_twist.angular.y, ekf_twist.angular.z);
            // }
            
            // COMMENTED OUT: 手動積分のポーズを返していた
            // (integrated_pose, odometry)
            // MODIFIED: EKFの推定ポーズを返す
            (ekf_pose, odometry)
        },
        vec![Cow::from("dummy_pose"), Cow::from("twist_with_covariance")],
        vec![Cow::from("estimated_pose"), Cow::from("ekf_odometry")],
        SchedulerType::GEDF(5),
    )
    .await;

    // Sink reactor for EKF Localizer output with TCP sending
    dag.register_sink_reactor::<_, (Pose, EKFOdometry)>(
        "ekf_sink".into(),
        move|(pose, ekf_odom): (Pose, EKFOdometry)| {
            // log::info!("=== EKF Sink Reactor 実行 ===");
            
            // if LOG_ENABLE {
            //     log::info!("Estimated Pose:");
            //     log::info!("  Position: x={:.3}, y={:.3}, z={:.3}", 
            //         pose.position.x, pose.position.y, pose.position.z);
            //     log::info!("  Orientation: x={:.3}, y={:.3}, z={:.3}, w={:.3}", 
            //         pose.orientation.x, pose.orientation.y, pose.orientation.z, pose.orientation.w);
                
            //     log::info!("EKF Odometry (ekf_odom):");
            //     log::info!("  Frame: {} -> {}", ekf_odom.header.frame_id, ekf_odom.child_frame_id);
            //     log::info!("  Timestamp: {}", ekf_odom.header.timestamp);
            //     log::info!("  Position: x={:.3}, y={:.3}, z={:.3}", 
            //         ekf_odom.pose.pose.position.x, ekf_odom.pose.pose.position.y, ekf_odom.pose.pose.position.z);
            //     log::info!("  Orientation: x={:.3}, y={:.3}, z={:.3}, w={:.3}", 
            //         ekf_odom.pose.pose.orientation.x, ekf_odom.pose.pose.orientation.y, 
            //         ekf_odom.pose.pose.orientation.z, ekf_odom.pose.pose.orientation.w);
            //     log::info!("  Linear Velocity: x={:.3}, y={:.3}, z={:.3}", 
            //         ekf_odom.twist.twist.linear.x, ekf_odom.twist.twist.linear.y, ekf_odom.twist.twist.linear.z);
            //     log::info!("  Angular Velocity: x={:.3}, y={:.3}, z={:.3}", 
            //         ekf_odom.twist.twist.angular.x, ekf_odom.twist.twist.angular.y, ekf_odom.twist.twist.angular.z);
            //     log::info!("=============================");
            // }
            
            // JSONデータを作成してグローバル変数に保存
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
            
            let awkernel_timestamp = get_awkernel_uptime_timestamp();
            // log::info!("JSONデータ作成完了: {} bytes, awkernel_timestamp={}", json_data.len(), awkernel_timestamp);
            
            // グローバル変数にJSONデータを保存
            save_json_data_to_global(json_data);
        },
        vec![Cow::from("estimated_pose"), Cow::from("ekf_odometry")],
        SchedulerType::GEDF(5),
        Duration::from_millis(50),  // CHANGED: 10ms -> 50ms (Autowareと同じ)
    )
    .await;

    // DAG の作成を完了
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

    // ノード数の確認
    // assert_eq!(dag.node_count(), 9); // 1つの periodic reactor + 8つの reactor（network_info_display追加）
    // assert_eq!(dag.edge_count(), 10); // トピックエッジの数

    // log::info!("Autoware test application DAG completed");
// 
    // log::info!("=== ネットワークテスト開始 ===");
    // log::info!("インターフェースID: {}", INTERFACE_ID);
    // log::info!("インターフェースIP: {}", INTERFACE_ADDR);
    // log::info!("宛先IP: {}", UDP_TCP_DST_ADDR);
    
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);
    // log::info!("IPv4アドレス設定完了: {} をインターフェース {} に追加", INTERFACE_ADDR, INTERFACE_ID);

    // ネットワークスタックの初期化を待つ
    // log::info!("ネットワークスタック初期化のため待機中...");
    awkernel_async_lib::sleep(Duration::from_secs(2)).await;
    
    // リアクターAPIに干渉しない周期UDP送信タスクを開始
    // log::info!("周期UDP送信タスクを開始します");
    start_periodic_udp_sender().await;
    
    // または、設定可能な周期で開始する場合
    // start_configurable_udp_sender(2).await; // 2秒間隔
    
    // JSONデータが準備されるまで待機（最大3秒）
    // log::info!("JSONデータの準備を待機中...");
    let mut wait_count = 0;
    const MAX_WAIT_COUNT: u32 = 3;
    
    while !JSON_DATA_READY.load(Ordering::Relaxed) && wait_count < MAX_WAIT_COUNT {
        // log::info!("JSONデータ待機中... ({}/{})", wait_count + 1, MAX_WAIT_COUNT);
        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        wait_count += 1;
    }
    
    if JSON_DATA_READY.load(Ordering::Relaxed) {
        // log::info!("JSONデータが準備されました。周期UDP送信タスクが動作中です");
        // 周期UDP送信タスクは既に動作中なので、ここでは何もしない
    } else {
        log::warn!("JSONデータが準備されませんでした。周期UDP送信タスクは待機中です");
    }

    log::info!("Autoware test application completed");
}

fn initialize_csv_data() -> Result<(), &'static str> {
    unsafe {
        if IMU_CSV_DATA.is_none() {
            let imu_data = parse_imu_csv(IMU_CSV_DATA_STR)?;
            if imu_data.is_empty() {
                return Err("IMU CSVが空です");
            }
            log::info!("IMU CSVデータをロード: {} rows", imu_data.len());
            IMU_CSV_DATA = Some(imu_data);
        }

        if VELOCITY_CSV_DATA.is_none() {
            let velocity_data = parse_velocity_csv(VELOCITY_CSV_DATA_STR)?;
            if velocity_data.is_empty() {
                return Err("Velocity CSVが空です");
            }
            log::info!("Velocity CSVデータをロード: {} rows", velocity_data.len());
            VELOCITY_CSV_DATA = Some(velocity_data);
        }
    }

    // let imu_start = find_first_active_imu_index();
    // IMU_CSV_INDEX.store(imu_start, Ordering::Relaxed);
    // let velocity_start = find_first_moving_velocity_index();
    // VELOCITY_CSV_INDEX.store(velocity_start, Ordering::Relaxed);
    // log::info!(
    //     "CSV開始インデックス: IMU={}, Velocity={}",
    //     imu_start,
    //     velocity_start
    // );

    Ok(())
}

fn parse_imu_csv(csv: &str) -> Result<Vec<ImuCsvRow>, &'static str> {
    let mut rows = Vec::new();

    parse_csv_records(csv, |fields| {
        if fields.len() < 12 {
            return Err("IMU CSVの列数が不足しています");
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
            return Err("Velocity CSVの列数が不足しています");
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
        let (result, in_read, _out_written, num_fields) = reader.read_record(input, &mut output, &mut ends);
        input = &input[in_read..];

        if matches!(result, ReadRecordResult::OutputFull) {
            return Err("CSV出力バッファが不足しています");
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
            let field = core::str::from_utf8(slice).map_err(|_| "CSV UTF-8変換に失敗しました")?;
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
        .ok_or("timestamp計算でオーバーフローしました")?;
    Ok(ts)
}

fn parse_u64(field: &str) -> Result<u64, &'static str> {
    let trimmed = field.trim();
    if trimmed.is_empty() {
        return Ok(0);
    }
    trimmed.parse::<u64>().map_err(|_| "u64パースに失敗しました")
}

fn parse_f64(field: &str) -> Result<f64, &'static str> {
    let trimmed = field.trim();
    if trimmed.is_empty() {
        return Ok(0.0);
    }
    trimmed.parse::<f64>().map_err(|_| "f64パースに失敗しました")
}

// fn find_first_moving_velocity_index() -> usize {
    // const EPS: f64 = 1.0e-6;
    // let data = unsafe { VELOCITY_CSV_DATA.as_ref() };
    // if let Some(rows) = data {
        // for (idx, row) in rows.iter().enumerate() {
            // if row.longitudinal_velocity.abs() > EPS || row.lateral_velocity.abs() > EPS {
                // return idx;
            // }
        // }
    // }
    // 0
// }
// 
// fn find_first_active_imu_index() -> usize {
    // const EPS: f64 = 1.0e-6;
    // let data = unsafe { IMU_CSV_DATA.as_ref() };
    // if let Some(rows) = data {
        // for (idx, row) in rows.iter().enumerate() {
            // if row.angular_velocity.x.abs() > EPS
                // || row.angular_velocity.y.abs() > EPS
                // || row.angular_velocity.z.abs() > EPS
                // || row.linear_acceleration.x.abs() > EPS
                // || row.linear_acceleration.y.abs() > EPS
                // || row.linear_acceleration.z.abs() > EPS
            // {
                // return idx;
            // }
        // }
    // }
    // 0
// }

// Awkernel起動時間からのタイムスタンプを取得する関数
fn get_awkernel_uptime_timestamp() -> u64 {
    // awkernel_lib::delay::uptime_nano()はu128を返すが、JSONではu64を使用
    // ナノ秒単位のタイムスタンプを取得
    let uptime_nanos = awkernel_lib::delay::uptime_nano();
    // u128からu64に変換（オーバーフローを防ぐため、適切な範囲に制限）
    if uptime_nanos > u64::MAX as u128 {
        u64::MAX
    } else {
        uptime_nanos as u64
    }
}

// リアクターAPIに干渉しないUDP送信タスク（一定周期実行）
pub async fn start_periodic_udp_sender() {
    log::info!("=== 周期UDP送信タスク開始 ===");
    
    // 独立したタスクとして実行
    awkernel_async_lib::spawn(
        "periodic_udp_sender".into(),
        periodic_udp_sender_task(),
        awkernel_async_lib::scheduler::SchedulerType::GEDF(5),
    )
    .await;
    
    // log::info!("周期UDP送信タスクを開始しました");
}

// 周期UDP送信タスクの実装
async fn periodic_udp_sender_task() {
    // log::info!("周期UDP送信タスク: 開始");
    
    // UDPソケットを作成（一度だけ）
    let socket_result = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
        INTERFACE_ID,
        &Default::default(),
    );
    
    let mut socket = match socket_result {
        Ok(socket) => {
            // log::info!("周期UDP送信タスク: UDPソケット作成成功");
            socket
        }
        Err(e) => {
            log::error!("周期UDP送信タスク: UDPソケット作成失敗: {:?}", e);
            return;
        }
    };
    
    let dst_addr = IpAddr::new_v4(UDP_TCP_DST_ADDR);
    let mut counter = 0;
    
    // 無限ループで一定周期実行
    loop {
        // JSONデータの準備チェック
        if !JSON_DATA_READY.load(Ordering::Relaxed) {
            log::debug!("周期UDP送信タスク: JSONデータ未準備、待機中...");
            awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            continue;
        }
        
        // 安全にJSONデータを取得
        let json_data = unsafe {
            LATEST_JSON_DATA.as_ref().map(|s| s.clone())
        };
        
        if let Some(data) = json_data {
            // UDP送信を実行
            match socket.send(data.as_bytes(), &dst_addr, UDP_DST_PORT).await {
                Ok(_) => {
                    counter += 1;
                    log::info!("周期UDP送信タスク: 送信成功 #{} ({} bytes)", counter, data.len());
                    
                    // レスポンス受信（オプション、タイムアウト付き）
                    let mut buf = [0u8; 1024];
                    if let Some(Ok((n, src_addr, src_port))) = 
                        awkernel_async_lib::timeout(
                            Duration::from_millis(100), // 短いタイムアウト
                            socket.recv(&mut buf)
                        ).await {
                        if let Ok(response) = core::str::from_utf8(&buf[..n]) {
                            log::debug!("周期UDP送信タスク: レスポンス受信: {}:{} - {}", 
                                src_addr.get_addr(), src_port, response);
                        }
                    }
                }
                Err(e) => {
                    log::warn!("周期UDP送信タスク: 送信失敗: {:?}", e);
                }
            }
        } else {
            log::warn!("周期UDP送信タスク: JSONデータが取得できませんでした");
        }
        
        // 一定周期で待機（例: 2秒間隔 - DAGの実行周期と衝突を避けるため）
        awkernel_async_lib::sleep(Duration::from_millis(5)).await;
    }
}

// リアクターAPIに干渉しないUDP送信タスク（設定可能な周期）
// pub async fn start_configurable_udp_sender(interval_sec: u64) {
//     log::info!("=== 設定可能周期UDP送信タスク開始 (間隔: {}秒) ===", interval_sec);
    
//     // 独立したタスクとして実行
//     awkernel_async_lib::spawn(
//         "configurable_udp_sender".into(),
//         configurable_udp_sender_task(interval_sec),
//         awkernel_async_lib::scheduler::SchedulerType::GEDF(5),
//     )
//     .await;
    
//     log::info!("設定可能周期UDP送信タスクを開始しました");
// }

// 設定可能な周期UDP送信タスクの実装
// async fn configurable_udp_sender_task(interval_sec: u64) {
//     log::info!("設定可能周期UDP送信タスク: 開始 (間隔: {}秒)", interval_sec);
    
//     // UDPソケットを作成
//     let socket_result = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
//         INTERFACE_ID,
//         &Default::default(),
//     );
    
//     let mut socket = match socket_result {
//         Ok(socket) => {
//             log::info!("設定可能周期UDP送信タスク: UDPソケット作成成功");
//             socket
//         }
//         Err(e) => {
//             log::error!("設定可能周期UDP送信タスク: UDPソケット作成失敗: {:?}", e);
//             return;
//         }
//     };
    
//     let dst_addr = IpAddr::new_v4(UDP_TCP_DST_ADDR);
//     let mut counter = 0;
    
//     loop {
//         // ネットワーク初期化チェック
//         if !NETWORK_INITIALIZED.load(Ordering::Relaxed) {
//             log::debug!("設定可能周期UDP送信タスク: ネットワーク未初期化、待機中...");
//             awkernel_async_lib::sleep(Duration::from_secs(1)).await;
//             continue;
//         }
        
//         // JSONデータの準備チェック
//         if !JSON_DATA_READY.load(Ordering::Relaxed) {
//             log::debug!("設定可能周期UDP送信タスク: JSONデータ未準備、待機中...");
//             awkernel_async_lib::sleep(Duration::from_secs(1)).await;
//             continue;
//         }
        
//         // 安全にJSONデータを取得
//         let json_data = unsafe {
//             LATEST_JSON_DATA.as_ref().map(|s| s.clone())
//         };
        
//         if let Some(data) = json_data {
//             // UDP送信を実行
//             match socket.send(data.as_bytes(), &dst_addr, UDP_DST_PORT).await {
//                 Ok(_) => {
//                     counter += 1;
//                     log::info!("設定可能周期UDP送信タスク: 送信成功 #{} ({} bytes, 間隔: {}秒)", 
//                         counter, data.len(), interval_sec);
//                 }
//                 Err(e) => {
//                     log::warn!("設定可能周期UDP送信タスク: 送信失敗: {:?}", e);
//                 }
//             }
//         } else {
//             log::warn!("設定可能周期UDP送信タスク: JSONデータが取得できませんでした");
//         }
        
//         // 設定された周期で待機
//         awkernel_async_lib::sleep(Duration::from_secs(interval_sec)).await;
//     }
// }

// JSONデータをグローバル変数に保存する関数
fn save_json_data_to_global(json_data: String) {
    unsafe {
        LATEST_JSON_DATA = Some(json_data.clone());
    }
    JSON_DATA_READY.store(true, Ordering::Relaxed);
    JSON_DATA_LENGTH.store(json_data.len(), Ordering::Relaxed);
    // log::info!("JSONデータをグローバル変数に保存: {} bytes", json_data.len());
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

// COMMENTED OUT: 手動積分用の関数はEKF内部状態からポーズを取得するようになったため不要
// EKFModule内にquaternion_to_yawとrpy_to_quaternionがあるため、そちらを使用
// fn quaternion_to_yaw(q: &Quaternion) -> f64 {
//     // Yaw extraction for dead reckoning heading propagation
//     let siny_cosp = 2.0 * (q.w * q.z + q.x * q.y);
//     let cosy_cosp = 1.0 - 2.0 * (q.y * q.y + q.z * q.z);
//     atan2(siny_cosp, cosy_cosp)
// }
// 
// fn yaw_to_quaternion(yaw: f64) -> Quaternion {
//     let half = yaw * 0.5;
//     Quaternion {
//         x: 0.0,
//         y: 0.0,
//         z: sin(half),
//         w: cos(half),
//     }
// }

// Get EKF Localizer safely
fn get_ekf_localizer() -> Option<&'static mut EKFModule> {
    let ptr = EKF_LOCALIZER.load(AtomicOrdering::Acquire);
    if ptr.is_null() {
        None
    } else {
        unsafe { Some(&mut *ptr) }
    }
}