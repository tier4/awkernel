#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec, vec::Vec, collections::VecDeque, string::String, format};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::net::{add_ipv4_addr, poll_interface, get_all_interface};
use awkernel_async_lib::net::{tcp::TcpStream, tcp::TcpConfig, udp::{UdpConfig, UdpSocketError},IpAddr};
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;
use core::net::Ipv4Addr;
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
use libm::{atan2, cos, sin};

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

static VEHICLE_TWIST_ARRIVED: AtomicBool = AtomicBool::new(false);
static IMU_ARRIVED: AtomicBool = AtomicBool::new(false);
static LAST_VEHICLE_TWIST_TIMESTAMP: AtomicU64 = AtomicU64::new(0);
static LAST_IMU_TIMESTAMP: AtomicU64 = AtomicU64::new(0);
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
static NETWORK_INITIALIZED: AtomicBool = AtomicBool::new(false);
static ARP_RESOLUTION_ATTEMPTED: AtomicBool = AtomicBool::new(false);
static TCP_CONNECTION_READY: AtomicBool = AtomicBool::new(false);
static TCP_STREAM_AVAILABLE: AtomicBool = AtomicBool::new(false);

// TCP送信キュー
static mut TCP_SEND_QUEUE: Option<VecDeque<String>> = None;
const MAX_QUEUE_SIZE: usize = 5;

// ARP 解決トリガーとして送信する TCP パケットの送信先ポート
const ARP_TRIGGER_DST_PORT: u16 = 26099;
// JSONデータ保存用のグローバル変数
static mut LATEST_JSON_DATA: Option<String> = None;
static JSON_DATA_READY: AtomicBool = AtomicBool::new(false);
static JSON_DATA_LENGTH: AtomicUsize = AtomicUsize::new(0);


static GYRO_ODOMETER_CORE: AtomicPtr<GyroOdometerCore> = AtomicPtr::new(null_mut());

// Global EKF Localizer instance with proper synchronization
static EKF_LOCALIZER: AtomicPtr<EKFModule> = AtomicPtr::new(null_mut());

// Queue management for storing multiple messages (matching C++ implementation)
static mut VEHICLE_TWIST_QUEUE: Option<VecDeque<TwistWithCovarianceStamped>> = None;
static mut IMU_QUEUE: Option<VecDeque<ImuWithCovariance>> = None;
static mut DR_POSE: Option<Pose> = None;

// Timeout checking function (matching C++ implementation)
fn check_timeout(current_timestamp: u64, last_timestamp: u64, timeout_sec: f64) -> bool {
    let dt = (current_timestamp as f64 - last_timestamp as f64) / 1_000_000_000.0; // Convert to seconds
    dt.abs() > timeout_sec
}



pub async fn run() {
    wait_microsec(1000000);

    //log::info!("Starting Autoware test application with simplified TCP networking");
    
    // 初期ネットワークインターフェース情報を表示
    //print_network_interfaces();

    let dag = create_dag();

    // ダミーデータ送信用リアクター
    dag.register_periodic_reactor::<_, (i32,i32,i32)>(
        "start_dummy_data".into(),
        || -> (i32,i32,i32) {
            
                       
            return (1, 2, 3); // 通常のデータ処理用の値
        },
        vec![Cow::from("start_imu"),Cow::from("start_vel"),Cow::from("start_pose")],
        SchedulerType::GEDF(5),
        Duration::from_secs(1),
    )
    .await;

    // IMU driver node (periodic_reactor) - Dummy data generator
    dag.register_reactor::<_, (i32,),(ImuMsg,)>(
        "imu_driver".into(),
        move |(a,):(i32,)| -> (ImuMsg,) {
            // Create parser instance
            let c = a+1;
            let mut parser = TamagawaImuParser::new("imu_link");
            
            // Generate commands
            //let version_cmd = TamagawaImuParser::generate_version_request();
            //let binary_cmd = TamagawaImuParser::generate_binary_request(30);
            //let offset_cmd = TamagawaImuParser::generate_offset_cancel_request(123);
            //let heading_cmd = TamagawaImuParser::generate_heading_reset_request();
            
            // Example 1: Generate static dummy data with awkernel uptime timestamp
            let awkernel_timestamp = reactor_helpers::get_awkernel_uptime_timestamp();
            let static_dummy_data = parser.generate_static_dummy_data(awkernel_timestamp);
            let imu_msg = parser.parse_binary_data(&static_dummy_data, awkernel_timestamp);
            if LOG_ENABLE {
                log::debug!("Generated dummy IMU data in imu_driver_node,num={c}, awkernel_timestamp={}", awkernel_timestamp);
            }

            (imu_msg.unwrap(),)
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
            // Create converter instance with default parameters
            let converter = VehicleVelocityConverter::default();
                            
            // Generate dummy velocity report data using helper function
            let velocity_report = reactor_helpers::create_dummy_velocity_report(b);
            
            // Convert velocity report to twist with covariance using helper function
            let twist_msg = reactor_helpers::convert_velocity_report_reactor(&velocity_report, &converter);
            
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
            if LOG_ENABLE {
                log::debug!("IMU corrected in imu_corrector node with covariance");
            }
            (corrected,)
        },
        vec![Cow::from("imu_data")],
        vec![Cow::from("corrected_imu_data")],
        SchedulerType::GEDF(5),
    )
    .await;

    // Gyro Odometer node - Optimized timeout handling with queue-based processing
    dag.register_reactor::<_, (ImuWithCovariance, TwistWithCovarianceStamped,), (TwistWithCovarianceStamped,)>(
        "gyro_odometer".into(),
        |(imu_with_cov, vehicle_twist): (ImuWithCovariance, TwistWithCovarianceStamped)| -> (TwistWithCovarianceStamped,) {
            // Initialize gyro odometer core and queues if not already done
            if get_gyro_odometer_core().is_none() {
                if let Err(e) = initialize_gyro_odometer_core() {
                    if LOG_ENABLE {
                        log::error!("Failed to initialize gyro odometer core: {}", e);
                    }
                    return (reactor_helpers::create_empty_twist(imu_with_cov.header.timestamp),);
                }
            }
            initialize_queues();

            let current_timestamp = imu_with_cov.header.timestamp;
            let timeout_sec = 1.0; // 1 second timeout
            
            // Update IMU state and add to queue (matching C++ callback_imu)
            IMU_ARRIVED.store(true, Ordering::Relaxed);
            LAST_IMU_TIMESTAMP.store(current_timestamp, Ordering::Relaxed);
            add_to_imu_queue(imu_with_cov);
            
            // Use the vehicle twist directly from vehicle_velocity_converter
            let vehicle_twist = vehicle_twist;
            VEHICLE_TWIST_ARRIVED.store(true, Ordering::Relaxed);
            LAST_VEHICLE_TWIST_TIMESTAMP.store(current_timestamp, Ordering::Relaxed);
            add_to_vehicle_twist_queue(vehicle_twist);

            // Check if both messages have arrived (matching C++ implementation)
            let vehicle_twist_arrived = VEHICLE_TWIST_ARRIVED.load(Ordering::Relaxed);
            let imu_arrived = IMU_ARRIVED.load(Ordering::Relaxed);
            
            if !vehicle_twist_arrived {
                if LOG_ENABLE {
                    log::warn!("Vehicle twist message not yet arrived");
                }
                clear_both_queues();
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }
            if !imu_arrived {
                if LOG_ENABLE {
                    log::warn!("IMU message not yet arrived");
                }
                clear_both_queues();
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }

            // Check timeout for both sensors (matching C++ implementation exactly)
            let last_vehicle_ts = LAST_VEHICLE_TWIST_TIMESTAMP.load(Ordering::Relaxed);
            let last_imu_ts = LAST_IMU_TIMESTAMP.load(Ordering::Relaxed);
            
            let vehicle_twist_dt = check_timeout(current_timestamp, last_vehicle_ts, timeout_sec);
            let imu_dt = check_timeout(current_timestamp, last_imu_ts, timeout_sec);
            
            // If either sensor times out, clear both queues (matching C++ implementation)
            if vehicle_twist_dt {
                if LOG_ENABLE {
                    log::warn!("Vehicle twist message timeout detected. vehicle_twist_dt: {:.3}[sec], tolerance {:.3}[sec]",
                        (current_timestamp as f64 - last_vehicle_ts as f64) / 1_000_000_000.0, timeout_sec);
                }
                clear_both_queues();
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }
            
            if imu_dt {
                if LOG_ENABLE {
                    log::warn!("IMU message timeout detected. imu_dt: {:.3}[sec], tolerance {:.3}[sec]",
                        (current_timestamp as f64 - last_imu_ts as f64) / 1_000_000_000.0, timeout_sec);
                }
                clear_both_queues();
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }

            // Check queue sizes (matching C++ implementation)
            let (vehicle_queue_size, imu_queue_size) = get_queue_sizes();
            if LOG_ENABLE {
                log::debug!("Queue sizes - vehicle_twist: {}, imu: {}", vehicle_queue_size, imu_queue_size);
            }
            
            if vehicle_queue_size == 0 || imu_queue_size == 0 {
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }

            // Get transform with error handling (matching C++ implementation)
            let transform_result = get_transform_safely("imu_link", "base_link");
            if let Err(transform_error) = transform_result {
                if LOG_ENABLE {
                    log::error!("Transform error: {}", transform_error);
                }
                clear_both_queues();
                return (reactor_helpers::create_empty_twist(current_timestamp),);
            }

            // Process queues and get result (matching C++ concat_gyro_and_odometer)
            let result = process_queues_and_get_result();
            
            // Clear queues after processing (matching C++ implementation)
            clear_both_queues();

            // Return result or empty twist if no result
            let final_result = if let Some(twist) = result {
                twist
            } else {
                reactor_helpers::create_empty_twist(current_timestamp)
            };

            if LOG_ENABLE {
                log::debug!("gyro odometer processed: linear.x={:.3}, angular.z={:.3}, timestamp={}",
                    final_result.twist.twist.linear.x,
                    final_result.twist.twist.angular.z,
                    final_result.header.timestamp
                );
            }

            (final_result,)
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
            let x = 0.86419;
            let y = 0.0;
            let z = 2.18096;
            // let yaw = angular_velocity * time;
            
            let pose = Pose {
                position: Point3D { x, y, z },
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
    dag.register_reactor::<_, (Pose, TwistWithCovarianceStamped), (Pose, EKFOdometry)>(
        "ekf_localizer".into(),
        |(pose, twist): (Pose, TwistWithCovarianceStamped)| -> (Pose, EKFOdometry) {
            // Initialize EKF Localizer if not already done
            if get_ekf_localizer().is_none() {
                if let Err(e) = initialize_ekf_localizer() {
                    if LOG_ENABLE {
                        log::error!("Failed to initialize EKF Localizer: {}", e);
                    }
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
                    DR_POSE = Some(pose.clone());
                    LAST_DR_TIMESTAMP.store(twist.header.timestamp, Ordering::Relaxed);
                    INITIALIZED = true;
                    if LOG_ENABLE {
                        log::info!("EKF Localizer initialized with initial pose");
                    }
                }
            }
            
            // Predict step using measured time gap
            let current_ts = twist.header.timestamp;
            let last_ts = LAST_DR_TIMESTAMP.swap(current_ts, Ordering::Relaxed);
            let dt = if last_ts == 0 {
                0.0
            } else {
                (current_ts.saturating_sub(last_ts)) as f64 / 1_000_000_000.0
            };

            if dt > 0.0 {
                ekf.predict(dt);
            }

            // Dead reckoning when poses are not refreshed
            let mut integrated_pose = unsafe { DR_POSE.clone().unwrap_or_else(|| pose.clone()) };
            let yaw = quaternion_to_yaw(&integrated_pose.orientation);
            let vx = twist.twist.twist.linear.x;
            let vy = twist.twist.twist.linear.y;
            let vz = twist.twist.twist.linear.z;
            let wz = twist.twist.twist.angular.z;

            if dt > 0.0 {
                let cos_yaw = cos(yaw);
                let sin_yaw = sin(yaw);
                let new_yaw = yaw + wz * dt;

                integrated_pose.position.x += (vx * cos_yaw - vy * sin_yaw) * dt;
                integrated_pose.position.y += (vx * sin_yaw + vy * cos_yaw) * dt;
                integrated_pose.position.z += vz * dt;
                integrated_pose.orientation = yaw_to_quaternion(new_yaw);
            }

            unsafe {
                DR_POSE = Some(integrated_pose.clone());
            }
            
            // Use predefined pose and twist covariance matrices instead of EKF's internal covariance
            let pose_covariance = EKF_POSE_COVARIANCE;
            let twist_covariance = EKF_TWIST_COVARIANCE;
            
            // Create odometry message using estimated pose and input twist
            let odometry = EKFOdometry {
                header: imu_driver::Header {
                    frame_id: "map",
                    timestamp: twist.header.timestamp,
                },
                child_frame_id: "base_link",
                pose: PoseWithCovariance {
                    pose: integrated_pose.clone(),
                    covariance: pose_covariance,
                },
                twist: TwistWithCovariance {
                    twist: twist.twist.twist.clone(),
                    covariance: twist_covariance,
                },
            };
            
            if LOG_ENABLE {
                log::debug!("EKF Localizer: dead_reckoned_pose=({:.3}, {:.3}, {:.3}), dt={:.3}, awkernel_timestamp={}",
                    integrated_pose.position.x, integrated_pose.position.y, integrated_pose.position.z, dt, odometry.header.timestamp);
                log::debug!("EKF Localizer: input_twist=({:.3}, {:.3}, {:.3}), angular=({:.3}, {:.3}, {:.3})",
                    twist.twist.twist.linear.x, twist.twist.twist.linear.y, twist.twist.twist.linear.z,
                    twist.twist.twist.angular.x, twist.twist.twist.angular.y, twist.twist.twist.angular.z);
            }
            
            (integrated_pose, odometry)
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
            
            let awkernel_timestamp = reactor_helpers::get_awkernel_uptime_timestamp();
            log::info!("JSONデータ作成完了: {} bytes, awkernel_timestamp={}", json_data.len(), awkernel_timestamp);
            
            // グローバル変数にJSONデータを保存
            save_json_data_to_global(json_data);
        },
        vec![Cow::from("estimated_pose"), Cow::from("ekf_odometry")],
        SchedulerType::GEDF(5),
        Duration::from_secs(1),
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

    log::info!("Autoware test application DAG completed");

    log::info!("=== ネットワークテスト開始 ===");
    log::info!("インターフェースID: {}", INTERFACE_ID);
    log::info!("インターフェースIP: {}", INTERFACE_ADDR);
    log::info!("宛先IP: {}", UDP_TCP_DST_ADDR);
    
    awkernel_lib::net::add_ipv4_addr(INTERFACE_ID, INTERFACE_ADDR, 24);
    log::info!("IPv4アドレス設定完了: {} をインターフェース {} に追加", INTERFACE_ADDR, INTERFACE_ID);

    // ネットワークスタックの初期化を待つ
    log::info!("ネットワークスタック初期化のため待機中...");
    awkernel_async_lib::sleep(Duration::from_secs(2)).await;
    
    // リアクターAPIに干渉しない周期UDP送信タスクを開始
    log::info!("周期UDP送信タスクを開始します");
    start_periodic_udp_sender().await;
    
    // または、設定可能な周期で開始する場合
    // start_configurable_udp_sender(2).await; // 2秒間隔
    
    // JSONデータが準備されるまで待機（最大3秒）
    log::info!("JSONデータの準備を待機中...");
    let mut wait_count = 0;
    const MAX_WAIT_COUNT: u32 = 3;
    
    while !JSON_DATA_READY.load(Ordering::Relaxed) && wait_count < MAX_WAIT_COUNT {
        log::info!("JSONデータ待機中... ({}/{})", wait_count + 1, MAX_WAIT_COUNT);
        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        wait_count += 1;
    }
    
    if JSON_DATA_READY.load(Ordering::Relaxed) {
        log::info!("JSONデータが準備されました。周期UDP送信タスクが動作中です");
        // 周期UDP送信タスクは既に動作中なので、ここでは何もしない
    } else {
        log::warn!("JSONデータが準備されませんでした。周期UDP送信タスクは待機中です");
    }

    log::info!("Autoware test application completed");
}

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
    
    log::info!("周期UDP送信タスクを開始しました");
}

// 周期UDP送信タスクの実装
async fn periodic_udp_sender_task() {
    log::info!("周期UDP送信タスク: 開始");
    
    // UDPソケットを作成（一度だけ）
    let socket_result = awkernel_async_lib::net::udp::UdpSocket::bind_on_interface(
        INTERFACE_ID,
        &Default::default(),
    );
    
    let mut socket = match socket_result {
        Ok(socket) => {
            log::info!("周期UDP送信タスク: UDPソケット作成成功");
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
        // ネットワーク初期化チェック
        // if !NETWORK_INITIALIZED.load(Ordering::Relaxed) {
        //     log::debug!("周期UDP送信タスク: ネットワーク未初期化、待機中...");
        //     awkernel_async_lib::sleep(Duration::from_secs(1)).await;
        //     continue;
        // }
        
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
        awkernel_async_lib::sleep(Duration::from_secs(2)).await;
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
    log::info!("JSONデータをグローバル変数に保存: {} bytes", json_data.len());
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

// Initialize gyro odometer core safely
fn initialize_gyro_odometer_core() -> Result<(), &'static str> {
    let config = GyroOdometerConfig::default();
    let core = GyroOdometerCore::new(config).map_err(|_| "Failed to create GyroOdometerCore")?;
    
    // Allocate on heap and store pointer
    let boxed_core = alloc::boxed::Box::new(core);
    let ptr = alloc::boxed::Box::into_raw(boxed_core);
    
    // Try to store the pointer atomically
    let old_ptr = GYRO_ODOMETER_CORE.compare_exchange(
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

// Get gyro odometer core safely
fn get_gyro_odometer_core() -> Option<&'static mut GyroOdometerCore> {
    let ptr = GYRO_ODOMETER_CORE.load(AtomicOrdering::Acquire);
    if ptr.is_null() {
        None
    } else {
        unsafe { Some(&mut *ptr) }
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

fn quaternion_to_yaw(q: &Quaternion) -> f64 {
    // Yaw extraction for dead reckoning heading propagation
    let siny_cosp = 2.0 * (q.w * q.z + q.x * q.y);
    let cosy_cosp = 1.0 - 2.0 * (q.y * q.y + q.z * q.z);
    atan2(siny_cosp, cosy_cosp)
}

fn yaw_to_quaternion(yaw: f64) -> Quaternion {
    let half = yaw * 0.5;
    Quaternion {
        x: 0.0,
        y: 0.0,
        z: sin(half),
        w: cos(half),
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

// Initialize queues safely
fn initialize_queues() {
    unsafe {
        if VEHICLE_TWIST_QUEUE.is_none() {
            VEHICLE_TWIST_QUEUE = Some(VecDeque::with_capacity(100));
        }
        if IMU_QUEUE.is_none() {
            IMU_QUEUE = Some(VecDeque::with_capacity(100));
        }
        if TCP_SEND_QUEUE.is_none() {
            TCP_SEND_QUEUE = Some(VecDeque::with_capacity(MAX_QUEUE_SIZE));
        }
    }
}

// Clear both queues (matching C++ implementation)
fn clear_both_queues() {
    unsafe {
        if let Some(queue) = &mut VEHICLE_TWIST_QUEUE {
            queue.clear();
        }
        if let Some(queue) = &mut IMU_QUEUE {
            queue.clear();
        }
    }
}

// Add message to vehicle twist queue
fn add_to_vehicle_twist_queue(twist: TwistWithCovarianceStamped) {
    unsafe {
        if let Some(queue) = &mut VEHICLE_TWIST_QUEUE {
            queue.push_back(twist);
        }
    }
}

// Add message to IMU queue
fn add_to_imu_queue(imu: ImuWithCovariance) {
    unsafe {
        if let Some(queue) = &mut IMU_QUEUE {
            queue.push_back(imu);
        }
    }
}

// Get queue sizes
fn get_queue_sizes() -> (usize, usize) {
    unsafe {
        let vehicle_size = VEHICLE_TWIST_QUEUE.as_ref().map_or(0, |q| q.len());
        let imu_size = IMU_QUEUE.as_ref().map_or(0, |q| q.len());
        (vehicle_size, imu_size)
    }
}

// TCP送信キュー操作
fn push_to_tcp_send_queue(json_data: String) {
    unsafe {
        if let Some(queue) = &mut TCP_SEND_QUEUE {
            if queue.len() >= MAX_QUEUE_SIZE {
                log::warn!("TCP送信キューが満杯です。古いデータを削除します。");
                queue.pop_front();
            }
            queue.push_back(json_data);
            log::debug!("TCP送信キューにデータを追加: キューサイズ = {}", queue.len());
        }
    }
}

fn get_tcp_send_queue_size() -> usize {
    unsafe {
        TCP_SEND_QUEUE.as_ref().map_or(0, |q| q.len())
    }
}

fn pop_from_tcp_send_queue() -> Option<String> {
    unsafe {
        TCP_SEND_QUEUE.as_mut().and_then(|q| q.pop_front())
    }
}

// Process queues and return result (matching C++ concat_gyro_and_odometer logic)
fn process_queues_and_get_result() -> Option<TwistWithCovarianceStamped> {
    unsafe {
        let vehicle_queue = VEHICLE_TWIST_QUEUE.as_ref()?;
        let imu_queue = IMU_QUEUE.as_ref()?;
        
        if vehicle_queue.is_empty() || imu_queue.is_empty() {
            return None;
        }
        
        // Calculate mean values (simplified version of C++ implementation)
        let mut vx_mean = 0.0;
        let mut gyro_mean = imu_driver::Vector3::new(0.0, 0.0, 0.0);
        
        // Calculate vehicle twist mean
        for twist in vehicle_queue {
            vx_mean += twist.twist.twist.linear.x;
        }
        vx_mean /= vehicle_queue.len() as f64;
        
        // Calculate gyro mean
        for imu in imu_queue {
            gyro_mean.x += imu.angular_velocity.x;
            gyro_mean.y += imu.angular_velocity.y;
            gyro_mean.z += imu.angular_velocity.z;
        }
        gyro_mean.x /= imu_queue.len() as f64;
        gyro_mean.y /= imu_queue.len() as f64;
        gyro_mean.z /= imu_queue.len() as f64;
        
        // Get latest timestamp
        let latest_vehicle_timestamp = vehicle_queue.back()?.header.timestamp;
        let latest_imu_timestamp = imu_queue.back()?.header.timestamp;
        let result_timestamp = if latest_vehicle_timestamp < latest_imu_timestamp {
            latest_imu_timestamp
        } else {
            latest_vehicle_timestamp
        };
        
        // Create result
        let result = TwistWithCovarianceStamped {
            header: imu_driver::Header {
                frame_id: "base_link",
                timestamp: result_timestamp,
            },
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: imu_driver::Vector3::new(vx_mean, 0.0, 0.0),
                    angular: gyro_mean,
                },
                covariance: [0.0; 36],
            },
        };
        
        Some(result)
    }
}