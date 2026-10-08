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
//
// Ported from the following versions of the original C++ code:
// core/autoware_core:
// type: git
// url: https://github.com/autowarefoundation/autoware_core.git
// original file path: sensing/autoware_vehicle_velocity_converter/src/vehicle_velocity_converter.cpp
// test code: sensing/autoware_vehicle_velocity_converter/test/test_vehicle_velocity_converter.cpp
// version: 1.8.0

#![no_std]

pub use common_types::{Header, Vector3};

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

    pub fn convert_velocity_report(&self, msg: &VelocityReport) -> TwistWithCovarianceStamped {
        if msg.header.frame_id != self.frame_id {
            log::warn!(
                "frame_id mismatch: expected '{}', got '{}'",
                self.frame_id,
                msg.header.frame_id
            );
        }
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
        covariance[0] = self.stddev_vx * self.stddev_vx;
        covariance[7] = 10000.0;
        covariance[14] = 10000.0;
        covariance[21] = 10000.0;
        covariance[28] = 10000.0;
        covariance[35] = self.stddev_wz * self.stddev_wz;

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

impl Default for VehicleVelocityConverter {
    fn default() -> Self {
        Self::new("base_link", 0.2, 0.1, 1.0)
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

    fn assert_approx_eq(actual: f64, expected: f64, eps: f64) {
        assert!(
            (actual - expected).abs() <= eps,
            "left: {actual}, right: {expected}"
        );
    }

    #[test]
    fn node_instantiation() {
        let converter = VehicleVelocityConverter::from_params_array(
            Some(0.2),
            Some(0.1),
            Some(1.0),
            "base_link",
        );

        assert_eq!(converter.get_frame_id(), "base_link");
        assert_eq!(converter.get_stddev_vx(), 0.2);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn message_conversion() {
        let converter = VehicleVelocityConverter::from_params_array(
            Some(0.2),
            Some(0.1),
            Some(1.5),
            "base_link",
        );
        let velocity_report = VelocityReport {
            header: Header {
                frame_id: "base_link",
                timestamp: 1234567890,
            },
            longitudinal_velocity: 2.0,
            lateral_velocity: 0.1,
            heading_rate: 0.3,
        };

        let twist_msg = converter.convert_velocity_report(&velocity_report);

        assert_eq!(twist_msg.header.frame_id, velocity_report.header.frame_id);
        assert_eq!(
            twist_msg.twist.twist.linear.x,
            velocity_report.longitudinal_velocity * 1.5
        );
        assert_eq!(
            twist_msg.twist.twist.linear.y,
            velocity_report.lateral_velocity
        );
        assert_eq!(
            twist_msg.twist.twist.angular.z,
            velocity_report.heading_rate
        );
        assert_approx_eq(twist_msg.twist.covariance[0], 0.2 * 0.2, 1e-12);
        assert_eq!(twist_msg.twist.covariance[7], 10000.0);
        assert_eq!(twist_msg.twist.covariance[14], 10000.0);
        assert_eq!(twist_msg.twist.covariance[21], 10000.0);
        assert_eq!(twist_msg.twist.covariance[28], 10000.0);
        assert_approx_eq(twist_msg.twist.covariance[35], 0.1 * 0.1, 1e-12);
    }

    #[test]
    fn different_frame_id() {
        let converter = VehicleVelocityConverter::from_params_array(
            Some(0.2),
            Some(0.1),
            Some(1.0),
            "base_link",
        );

        let velocity_report = VelocityReport {
            header: Header {
                frame_id: "different_frame",
                timestamp: 1234567890,
            },
            longitudinal_velocity: 2.0,
            lateral_velocity: 0.1,
            heading_rate: 0.3,
        };

        // As in the original C++ code: frame_id mismatch logs a warning but continues
        let twist_msg = converter.convert_velocity_report(&velocity_report);
        assert_eq!(twist_msg.header.frame_id, velocity_report.header.frame_id);
        assert_eq!(
            twist_msg.twist.twist.linear.x,
            velocity_report.longitudinal_velocity
        );
    }

    #[test]
    fn from_params_array_with_defaults() {
        let converter = VehicleVelocityConverter::from_params_array(None, None, None, "base_link");

        assert_eq!(converter.get_stddev_vx(), 0.2);
        assert_eq!(converter.get_stddev_wz(), 0.1);
        assert_eq!(converter.get_speed_scale_factor(), 1.0);
    }

    #[test]
    fn reactor_helpers() {
        let empty_twist = reactor_helpers::create_empty_twist(1234567890);
        assert_eq!(empty_twist.header.frame_id, "base_link");
        assert_eq!(empty_twist.twist.twist.linear.x, 0.0);
    }
}
