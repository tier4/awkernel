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

use imu_driver::{Header, Vector3};

#[derive(Debug, Clone)]
pub struct VelocityReport {
    pub header: Header,
    pub longitudinal_velocity: f64,
    pub lateral_velocity: f64,
    pub heading_rate: f64,
}

#[derive(Debug, Clone)]
pub struct VelocityCsvRow {
    pub timestamp: u64,
    pub longitudinal_velocity: f64,
    pub lateral_velocity: f64,
    pub heading_rate: f64,
}

pub fn build_velocity_report_from_csv_row(
    row: &VelocityCsvRow,
    frame_id: &'static str,
    timestamp: u64,
) -> VelocityReport {
    VelocityReport {
        header: Header {
            frame_id,
            timestamp,
        },
        longitudinal_velocity: row.longitudinal_velocity,
        lateral_velocity: row.lateral_velocity,
        heading_rate: row.heading_rate,
    }
}

#[derive(Debug, Clone)]
pub struct TwistWithCovarianceStamped {
    pub header: Header,
    pub twist: TwistWithCovariance,
}

#[derive(Debug, Clone)]
pub struct TwistWithCovariance {
    pub twist: Twist,
    pub covariance: [f64; 36],
}

#[derive(Debug, Clone)]
pub struct Twist {
    pub linear: Vector3,
    pub angular: Vector3,
}

#[repr(C)]
pub struct Odometry {
    pub velocity: f64,
}

pub struct VehicleVelocityConverter {
    frame_id: &'static str,
    stddev_vx: f64,
    stddev_wz: f64,
    speed_scale_factor: f64,
}

impl VehicleVelocityConverter {
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

    pub fn default() -> Self {
        Self::new("base_link", 0.2, 0.1, 1.0)
    }

    pub fn convert_velocity_report(&self, msg: &VelocityReport) -> TwistWithCovarianceStamped {
        let _frame_id_mismatch = msg.header.frame_id != self.frame_id;

        TwistWithCovarianceStamped {
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
        }
    }

    fn create_covariance_matrix(&self) -> [f64; 36] {
        let mut covariance = [0.0; 36];
        covariance[0 + 0 * 6] = self.stddev_vx * self.stddev_vx;
        covariance[1 + 1 * 6] = 10000.0;
        covariance[2 + 2 * 6] = 10000.0;
        covariance[3 + 3 * 6] = 10000.0;
        covariance[4 + 4 * 6] = 10000.0;
        covariance[5 + 5 * 6] = self.stddev_wz * self.stddev_wz;

        covariance
    }

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

pub mod reactor_helpers {
    use super::*;

    pub fn create_empty_twist(timestamp: u64) -> TwistWithCovarianceStamped {
        TwistWithCovarianceStamped {
            header: Header {
                frame_id: "base_link",
                timestamp,
            },
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: Vector3 {
                        x: 0.0,
                        y: 0.0,
                        z: 0.0,
                    },
                    angular: Vector3 {
                        x: 0.0,
                        y: 0.0,
                        z: 0.0,
                    },
                },
                covariance: [0.0; 36],
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vehicle_velocity_converter_creation() {
        let converter = VehicleVelocityConverter::new("base_link", 0.1, 0.1, 1.0);

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
        let converter = VehicleVelocityConverter::new("base_link", 0.1, 0.1, 1.0);

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
        assert_eq!(twist_msg.twist.covariance[0], 0.01);
        assert_eq!(twist_msg.twist.covariance[35], 0.01);
    }

    #[test]
    fn test_convert_velocity_report_wrong_frame_id() {
        let converter = VehicleVelocityConverter::new("base_link", 0.1, 0.1, 1.0);

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
        let converter = VehicleVelocityConverter::from_params_array(None, None, None, "base_link");

        assert_eq!(converter.get_stddev_vx(), 0.1);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn test_reactor_helpers() {
        let empty_twist = reactor_helpers::create_empty_twist(1234567890);
        assert_eq!(empty_twist.header.frame_id, "base_link");
        assert_eq!(empty_twist.twist.twist.linear.x, 0.0);
    }
}
