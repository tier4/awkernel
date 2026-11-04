#![no_std]
extern crate alloc;

#[derive(Debug, Clone)]
pub struct Header {
    pub frame_id: &'static str,
    pub timestamp: u64,
}

#[derive(Debug, Clone)]
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
