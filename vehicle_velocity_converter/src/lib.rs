// Copyright 2021 TierIV
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![no_std]

use imu_driver::{Vector3, Header};

/// 速度レポートメッセージの構造体
#[derive(Debug, Clone)]
pub struct VelocityReport {
    pub header: Header,
    pub longitudinal_velocity: f64,
    pub lateral_velocity: f64,
    pub heading_rate: f64,
}

/// TwistWithCovarianceStampedメッセージの構造体
#[derive(Debug, Clone)]
pub struct TwistWithCovarianceStamped {
    pub header: Header,
    pub twist: TwistWithCovariance,
}

/// TwistWithCovariance構造体
#[derive(Debug, Clone)]
pub struct TwistWithCovariance {
    pub twist: Twist,
    pub covariance: [f64; 36],
}

/// Twist構造体
#[derive(Debug, Clone)]
pub struct Twist {
    pub linear: Vector3,
    pub angular: Vector3,
}

#[repr(C)]
pub struct Odometry {
    pub velocity: f64,
}

/// 車両速度変換器の構造体
pub struct VehicleVelocityConverter {
    frame_id: &'static str,              // → frame_id: base_link
    stddev_vx: f64,                      // → velocity_stddev_xx: 0.2
    stddev_wz: f64,                      // → angular_velocity_stddev_zz: 0.1
    speed_scale_factor: f64,             // → speed_scale_factor: 1.0
}

impl VehicleVelocityConverter {
    /// 新しいVehicleVelocityConverterインスタンスを作成
    pub fn new(
        frame_id: &'static str,
        stddev_vx: f64,
        stddev_wz: f64,
        speed_scale_factor: f64,
    ) -> Self {
        Self {
            frame_id,
            stddev_vx,
            stddev_wz,
            speed_scale_factor,
        }
    }

    /// パラメータからVehicleVelocityConverterを作成（配列ベース版）
    pub fn from_params_array(
        velocity_stddev_xx: Option<f64>,
        angular_velocity_stddev_zz: Option<f64>,
        speed_scale_factor: Option<f64>,
        frame_id: &'static str,
    ) -> Self {
        let stddev_vx = velocity_stddev_xx.unwrap_or(0.2);
        let stddev_wz = angular_velocity_stddev_zz.unwrap_or(0.1);
        let speed_scale_factor = speed_scale_factor.unwrap_or(1.0);

        Self::new(frame_id, stddev_vx, stddev_wz, speed_scale_factor)
    }

    /// デフォルト設定でVehicleVelocityConverterを作成
    pub fn default() -> Self {
        Self::new("base_link", 0.2, 0.1, 1.0)
    }

    /// 速度レポートをTwistWithCovarianceStampedに変換
    pub fn convert_velocity_report(&self, msg: &VelocityReport) -> Result<TwistWithCovarianceStamped, &'static str> {
        // フレームIDの検証
        if msg.header.frame_id != self.frame_id {
            return Err("frame_id mismatch");
        }

        // TwistWithCovarianceStampedメッセージを生成
        let twist_with_covariance_msg = TwistWithCovarianceStamped {
            header: msg.header.clone(),
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: Vector3 {
                        x: msg.longitudinal_velocity * self.speed_scale_factor,
                        y: msg.lateral_velocity,
                        z: 0.0,
                    },
                    angular: Vector3 {
                        x: 0.0,
                        y: 0.0,
                        z: msg.heading_rate,
                    },
                },
                covariance: self.create_covariance_matrix(),
            },
        };

        Ok(twist_with_covariance_msg)
    }

    /// 共分散行列を作成
    fn create_covariance_matrix(&self) -> [f64; 36] {
        let mut covariance = [0.0; 36];
        
        // 線形速度の分散 (x方向)
        covariance[0 + 0 * 6] = self.stddev_vx * self.stddev_vx;
        
        // その他の線形速度成分は大きな値（低い信頼度）を設定
        covariance[1 + 1 * 6] = 10000.0; // y方向
        covariance[2 + 2 * 6] = 10000.0; // z方向
        
        // 角速度成分は大きな値（低い信頼度）を設定
        covariance[3 + 3 * 6] = 10000.0; // x方向
        covariance[4 + 4 * 6] = 10000.0; // y方向
        
        // 角速度の分散 (z方向)
        covariance[5 + 5 * 6] = self.stddev_wz * self.stddev_wz;
        
        covariance
    }

    /// パラメータを取得
    pub fn get_frame_id(&self) -> &'static str {
        self.frame_id
    }

    pub fn get_stddev_vx(&self) -> f64 {
        self.stddev_vx
    }

    pub fn get_stddev_wz(&self) -> f64 {
        self.stddev_wz
    }

    pub fn get_speed_scale_factor(&self) -> f64 {
        self.speed_scale_factor
    }
}

/// リアクターAPI用のヘルパー関数
pub mod reactor_helpers {
    use super::*;

    /// ダミーのVelocityReportを生成（awkernel起動時間を使用）
    pub fn create_dummy_velocity_report(counter: i32) -> VelocityReport {
        // awkernel起動時間からのタイムスタンプを取得
        let awkernel_timestamp = get_awkernel_uptime_timestamp();
        
        VelocityReport {
            header: Header {
                frame_id: "base_link",
                timestamp: awkernel_timestamp,
            },
            longitudinal_velocity: 10.0 + (counter as f64 * 0.1),
            lateral_velocity: 2.0 + (counter as f64 * 0.05),
            heading_rate: 0.0,
        }
    }

    /// awkernel起動時間からのタイムスタンプを取得する関数
    pub fn get_awkernel_uptime_timestamp() -> u64 {
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

    /// 空のTwistWithCovarianceStampedを生成
    pub fn create_empty_twist(timestamp: u64) -> TwistWithCovarianceStamped {
        TwistWithCovarianceStamped {
            header: Header {
                frame_id: "base_link",
                timestamp,
            },
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: Vector3 { x: 0.0, y: 0.0, z: 0.0 },
                    angular: Vector3 { x: 0.0, y: 0.0, z: 0.0 },
                },
                covariance: [0.0; 36],
            },
        }
    }

    /// リアクター関数: VelocityReportをTwistWithCovarianceStampedに変換
    pub fn convert_velocity_report_reactor(
        velocity_report: &VelocityReport,
        converter: &VehicleVelocityConverter,
    ) -> TwistWithCovarianceStamped {
        match converter.convert_velocity_report(velocity_report) {
            Ok(twist_msg) => twist_msg,
            Err(_) => create_empty_twist(velocity_report.header.timestamp),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vehicle_velocity_converter_creation() {
        let converter = VehicleVelocityConverter::new(
            "base_link",
            0.1,
            0.1,
            1.0,
        );

        assert_eq!(converter.get_frame_id(), "base_link");
        assert_eq!(converter.get_stddev_vx(), 0.1);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn test_vehicle_velocity_converter_default() {
        let converter = VehicleVelocityConverter::default();
        assert_eq!(converter.get_frame_id(), "base_link");
        assert_eq!(converter.get_stddev_vx(), 0.1);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn test_convert_velocity_report_success() {
        let converter = VehicleVelocityConverter::new(
            "base_link",
            0.1,
            0.1,
            1.0,
        );

        let velocity_report = VelocityReport {
            header: Header {
                frame_id: "base_link",
                timestamp: 1234567890,
            },
            longitudinal_velocity: 10.0,
            lateral_velocity: 2.0,
            heading_rate: 0.5,
        };

        let result = converter.convert_velocity_report(&velocity_report);
        assert!(result.is_ok());

        let twist_msg = result.unwrap();
        assert_eq!(twist_msg.twist.twist.linear.x, 10.0);
        assert_eq!(twist_msg.twist.twist.linear.y, 2.0);
        assert_eq!(twist_msg.twist.twist.angular.z, 0.5);
        assert_eq!(twist_msg.twist.covariance[0], 0.01); // 0.1^2
        assert_eq!(twist_msg.twist.covariance[35], 0.01); // 0.1^2
    }

    #[test]
    fn test_convert_velocity_report_wrong_frame_id() {
        let converter = VehicleVelocityConverter::new(
            "base_link",
            0.1,
            0.1,
            1.0,
        );

        let velocity_report = VelocityReport {
            header: Header {
                frame_id: "wrong_frame",
                timestamp: 1234567890,
            },
            longitudinal_velocity: 10.0,
            lateral_velocity: 2.0,
            heading_rate: 0.5,
        };

        let result = converter.convert_velocity_report(&velocity_report);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "frame_id mismatch");
    }

    #[test]
    fn test_from_params_array() {
        let converter = VehicleVelocityConverter::from_params_array(
            Some(0.2),
            Some(0.3),
            Some(1.5),
            "base_link",
        );

        assert_eq!(converter.get_stddev_vx(), 0.2);
        assert_eq!(converter.get_stddev_wz(), 0.3);
        assert_eq!(converter.get_speed_scale_factor(), 1.5);
    }

    #[test]
    fn test_from_params_array_with_defaults() {
        let converter = VehicleVelocityConverter::from_params_array(
            None,
            None,
            None,
            "base_link",
        );

        assert_eq!(converter.get_stddev_vx(), 0.1);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn test_reactor_helpers() {
        let dummy_report = reactor_helpers::create_dummy_velocity_report(1);
        assert_eq!(dummy_report.header.frame_id, "base_link");
        assert_eq!(dummy_report.longitudinal_velocity, 10.1);

        let empty_twist = reactor_helpers::create_empty_twist(1234567890);
        assert_eq!(empty_twist.header.frame_id, "base_link");
        assert_eq!(empty_twist.twist.twist.linear.x, 0.0);
    }
}
