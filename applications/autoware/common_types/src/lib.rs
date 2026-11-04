#![no_std]
extern crate alloc;

#[derive(Debug, Clone)]
pub struct Header {
    pub frame_id: &'static str,
    pub timestamp: u64,
}

pub use nalgebra::{Quaternion, UnitQuaternion, Vector3};
