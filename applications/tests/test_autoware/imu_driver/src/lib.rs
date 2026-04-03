#![no_std]
extern crate alloc;

use alloc::{format, string::String, vec, vec::Vec};
use core::f64::consts::PI;

#[derive(Clone, Debug)]
pub struct ImuMsg {
    pub header: Header,
    pub orientation: Quaternion,
    pub angular_velocity: Vector3,
    pub linear_acceleration: Vector3,
}

#[derive(Clone, Debug)]
pub struct ImuCsvRow {
    pub timestamp: u64,
    pub orientation: Quaternion,
    pub angular_velocity: Vector3,
    pub linear_acceleration: Vector3,
}

#[derive(Clone, Debug)]
pub struct Header {
    pub frame_id: &'static str,
    pub timestamp: u64,
}

#[derive(Debug, Clone)]
pub struct Quaternion {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

#[derive(Clone, Debug)]
pub struct Vector3 {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl Vector3 {
    pub fn new(x: f64, y: f64, z: f64) -> Self {
        Self { x, y, z }
    }
}

impl Default for ImuMsg {
    fn default() -> Self {
        Self {
            header: Header {
                frame_id: "imu",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 1.0,
                y: 0.0,
                z: 0.0,
                w: 0.0,
            },
            angular_velocity: Vector3::new(0.0, 0.0, 0.0),
            linear_acceleration: Vector3::new(0.0, 0.0, 0.0),
        }
    }
}

pub fn build_imu_msg_from_csv_row(
    row: &ImuCsvRow,
    frame_id: &'static str,
    timestamp: u64,
) -> ImuMsg {
    ImuMsg {
        header: Header {
            frame_id,
            timestamp,
        },
        orientation: row.orientation.clone(),
        angular_velocity: row.angular_velocity.clone(),
        linear_acceleration: row.linear_acceleration.clone(),
    }
}

pub struct TamagawaImuParser {
    frame_id: &'static str,
    dummy_counter: u16,
}

impl TamagawaImuParser {
    pub fn new(frame_id: &'static str) -> Self {
        Self {
            frame_id,
            dummy_counter: 0,
        }
    }

    pub fn parse_binary_data(&self, data: &[u8], timestamp: u64) -> Option<ImuMsg> {
        if data.len() != 58
            || data[5] != b'B'
            || data[6] != b'I'
            || data[7] != b'N'
            || data[8] != b','
        {
            return None;
        }

        let mut imu_msg = ImuMsg::default();
        imu_msg.header.frame_id = self.frame_id;
        imu_msg.header.timestamp = timestamp;

        let _counter = ((data[11] as u16) << 8) | (data[12] as u16);
        let raw_data = self.parse_signed_16bit(&data[15..17]);
        imu_msg.angular_velocity.x = self.convert_angular_velocity(raw_data);
        let raw_data = self.parse_signed_16bit(&data[17..19]);
        imu_msg.angular_velocity.y = self.convert_angular_velocity(raw_data);
        let raw_data = self.parse_signed_16bit(&data[19..21]);
        imu_msg.angular_velocity.z = self.convert_angular_velocity(raw_data);
        let raw_data = self.parse_signed_16bit(&data[21..23]);
        imu_msg.linear_acceleration.x = self.convert_acceleration(raw_data);
        let raw_data = self.parse_signed_16bit(&data[23..25]);
        imu_msg.linear_acceleration.y = self.convert_acceleration(raw_data);
        let raw_data = self.parse_signed_16bit(&data[25..27]);
        imu_msg.linear_acceleration.z = self.convert_acceleration(raw_data);

        Some(imu_msg)
    }

    pub fn generate_dummy_binary_data(
        &mut self,
        _timestamp: u64,
        angular_velocity: Vector3,
        linear_acceleration: Vector3,
    ) -> Vec<u8> {
        let mut data = vec![0u8; 58];

        data[0..5].copy_from_slice(b"$TSC,");
        data[5] = b'B';
        data[6] = b'I';
        data[7] = b'N';
        data[8] = b',';
        data[11] = (self.dummy_counter >> 8) as u8;
        data[12] = (self.dummy_counter & 0xFF) as u8;
        self.dummy_counter = self.dummy_counter.wrapping_add(1);

        let angular_vel_x_lsb = self.convert_angular_velocity_to_lsb(angular_velocity.x);
        let angular_vel_y_lsb = self.convert_angular_velocity_to_lsb(angular_velocity.y);
        let angular_vel_z_lsb = self.convert_angular_velocity_to_lsb(angular_velocity.z);
        let accel_x_lsb = self.convert_acceleration_to_lsb(linear_acceleration.x);
        let accel_y_lsb = self.convert_acceleration_to_lsb(linear_acceleration.y);
        let accel_z_lsb = self.convert_acceleration_to_lsb(linear_acceleration.z);

        data[15] = (angular_vel_x_lsb >> 8) as u8;
        data[16] = (angular_vel_x_lsb & 0xFF) as u8;
        data[17] = (angular_vel_y_lsb >> 8) as u8;
        data[18] = (angular_vel_y_lsb & 0xFF) as u8;
        data[19] = (angular_vel_z_lsb >> 8) as u8;
        data[20] = (angular_vel_z_lsb & 0xFF) as u8;
        data[21] = (accel_x_lsb >> 8) as u8;
        data[22] = (accel_x_lsb & 0xFF) as u8;
        data[23] = (accel_y_lsb >> 8) as u8;
        data[24] = (accel_y_lsb & 0xFF) as u8;
        data[25] = (accel_z_lsb >> 8) as u8;
        data[26] = (accel_z_lsb & 0xFF) as u8;

        data
    }

    pub fn generate_static_dummy_data(&mut self, timestamp: u64) -> Vec<u8> {
        let angular_velocity = Vector3::new(0.1, 0.2, 0.01);
        let linear_acceleration = Vector3::new(0.0, 0.0, 9.80665);

        self.generate_dummy_binary_data(timestamp, angular_velocity, linear_acceleration)
    }

    fn convert_angular_velocity_to_lsb(&self, rad_per_sec: f64) -> i16 {
        let deg_per_sec = rad_per_sec * 180.0 / PI;
        let lsb = deg_per_sec / (200.0 / (1 << 15) as f64);
        lsb as i16
    }

    fn convert_acceleration_to_lsb(&self, m_per_sec_squared: f64) -> i16 {
        let lsb = m_per_sec_squared / (100.0 / (1 << 15) as f64);
        lsb as i16
    }

    fn parse_signed_16bit(&self, data: &[u8]) -> i16 {
        if data.len() != 2 {
            return 0;
        }
        let high_byte = (data[0] as i32) << 8;
        let low_byte = data[1] as i32;
        let result = (high_byte & 0xFFFFFF00u32 as i32) | (low_byte & 0x000000FF);
        result as i16
    }

    fn convert_angular_velocity(&self, raw_data: i16) -> f64 {
        let lsb_to_deg_per_sec = 200.0 / (1 << 15) as f64;
        let deg_to_rad = PI / 180.0;
        (raw_data as f64) * lsb_to_deg_per_sec * deg_to_rad
    }

    fn convert_acceleration(&self, raw_data: i16) -> f64 {
        let lsb_to_m_per_sec_squared = 100.0 / (1 << 15) as f64;
        (raw_data as f64) * lsb_to_m_per_sec_squared
    }

    pub fn generate_version_request() -> &'static [u8] {
        b"$TSC,VER*29\r\n"
    }

    pub fn generate_offset_cancel_request(offset_value: i32) -> String {
        format!("$TSC,OFC,{}\r\n", offset_value)
    }

    pub fn generate_heading_reset_request() -> &'static [u8] {
        b"$TSC,HRST*29\r\n"
    }

    pub fn generate_binary_request(rate_hz: u32) -> String {
        format!("$TSC,BIN,{}\r\n", rate_hz)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example_usage() {
        let mut parser = TamagawaImuParser::new("imu_link");
        let version_cmd = TamagawaImuParser::generate_version_request();
        let binary_cmd = TamagawaImuParser::generate_binary_request(30);
        let offset_cmd = TamagawaImuParser::generate_offset_cancel_request(123);
        let heading_cmd = TamagawaImuParser::generate_heading_reset_request();
        let static_dummy_data = parser.generate_static_dummy_data(123456789);
        if let Some(imu_msg) = parser.parse_binary_data(&static_dummy_data, 123456789) {
            let _angular_vel = imu_msg.angular_velocity;
            let _acceleration = imu_msg.linear_acceleration;
        }

        let sinusoidal_dummy_data = parser.generate_sinusoidal_dummy_data(123456789, 0.0);
        if let Some(imu_msg) = parser.parse_binary_data(&sinusoidal_dummy_data, 123456789) {
            let _angular_vel = imu_msg.angular_velocity;
            let _acceleration = imu_msg.linear_acceleration;
        }

        let custom_angular_velocity = Vector3::new(0.5, -0.3, 1.2);
        let custom_acceleration = Vector3::new(8.5, 2.1, 10.2);
        let custom_dummy_data = parser.generate_dummy_binary_data(
            123456789,
            custom_angular_velocity,
            custom_acceleration,
        );
        if let Some(imu_msg) = parser.parse_binary_data(&custom_dummy_data, 123456789) {
            let _angular_vel = imu_msg.angular_velocity;
            let _acceleration = imu_msg.linear_acceleration;
        }
    }
}
