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
    use core::f64::consts::PI;

    fn assert_approx_eq(actual: f64, expected: f64, eps: f64) {
        assert!(
            (actual - expected).abs() <= eps,
            "left: {actual}, right: {expected}"
        );
    }

    fn expected_ang_vel(raw: i16) -> f64 {
        let lsb_to_deg_per_sec = 200.0 / (1 << 15) as f64;
        let deg_to_rad = PI / 180.0;
        (raw as f64) * lsb_to_deg_per_sec * deg_to_rad
    }

    fn expected_acc(raw: i16) -> f64 {
        let lsb_to_m_per_sec_squared = 100.0 / (1 << 15) as f64;
        (raw as f64) * lsb_to_m_per_sec_squared
    }

    fn put_i16_be(buf: &mut [u8], value: i16) {
        let raw = value as u16;
        buf[0] = (raw >> 8) as u8;
        buf[1] = (raw & 0xFF) as u8;
    }

    #[test]
    fn parse_rejects_invalid_length() {
        let parser = TamagawaImuParser::new("imu_link");
        let data = [0u8; 57];

        assert!(parser.parse_binary_data(&data, 1).is_none());
    }

    #[test]
    fn parse_rejects_non_bin_header() {
        let parser = TamagawaImuParser::new("imu_link");
        let mut data = [0u8; 58];
        data[0..5].copy_from_slice(b"$TSC,");
        data[5..9].copy_from_slice(b"XIN,");

        assert!(parser.parse_binary_data(&data, 1).is_none());
    }

    #[test]
    fn parse_extracts_fields_and_converts_units() {
        let parser = TamagawaImuParser::new("imu_link");
        let timestamp = 123456789u64;

        let mut data = [0u8; 58];
        data[0..5].copy_from_slice(b"$TSC,");
        data[5..9].copy_from_slice(b"BIN,");

        let gx: i16 = 1;
        let gy: i16 = -2;
        let gz: i16 = 1234;
        let ax: i16 = -300;
        let ay: i16 = 0;
        let az: i16 = 32767;

        put_i16_be(&mut data[15..17], gx);
        put_i16_be(&mut data[17..19], gy);
        put_i16_be(&mut data[19..21], gz);
        put_i16_be(&mut data[21..23], ax);
        put_i16_be(&mut data[23..25], ay);
        put_i16_be(&mut data[25..27], az);

        let imu = parser
            .parse_binary_data(&data, timestamp)
            .expect("should parse");

        assert_eq!(imu.header.frame_id, "imu_link");
        assert_eq!(imu.header.timestamp, timestamp);

        let eps = 1e-12;
        assert_approx_eq(imu.angular_velocity.x, expected_ang_vel(gx), eps);
        assert_approx_eq(imu.angular_velocity.y, expected_ang_vel(gy), eps);
        assert_approx_eq(imu.angular_velocity.z, expected_ang_vel(gz), eps);

        assert_approx_eq(imu.linear_acceleration.x, expected_acc(ax), eps);
        assert_approx_eq(imu.linear_acceleration.y, expected_acc(ay), eps);
        assert_approx_eq(imu.linear_acceleration.z, expected_acc(az), eps);
    }

    #[test]
    fn generate_dummy_data_roundtrip_is_close() {
        let mut parser = TamagawaImuParser::new("imu_link");
        let timestamp = 42u64;

        let input_angular_velocity = Vector3::new(0.5, -0.3, 1.2);
        let input_linear_acceleration = Vector3::new(8.5, 2.1, 10.2);

        let data = parser.generate_dummy_binary_data(
            timestamp,
            input_angular_velocity.clone(),
            input_linear_acceleration.clone(),
        );
        let imu = parser
            .parse_binary_data(&data, timestamp)
            .expect("should parse");

        let ang_eps = (200.0 / (1 << 15) as f64) * (PI / 180.0);
        let acc_eps = 100.0 / (1 << 15) as f64;

        assert_approx_eq(imu.angular_velocity.x, input_angular_velocity.x, ang_eps);
        assert_approx_eq(imu.angular_velocity.y, input_angular_velocity.y, ang_eps);
        assert_approx_eq(imu.angular_velocity.z, input_angular_velocity.z, ang_eps);

        assert_approx_eq(
            imu.linear_acceleration.x,
            input_linear_acceleration.x,
            acc_eps,
        );
        assert_approx_eq(
            imu.linear_acceleration.y,
            input_linear_acceleration.y,
            acc_eps,
        );
        assert_approx_eq(
            imu.linear_acceleration.z,
            input_linear_acceleration.z,
            acc_eps,
        );
    }
}
