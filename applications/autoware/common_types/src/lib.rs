//! This crate defines data types that are common to the Autoware project.
//!
//! For algebraic operations and transformations, this crate relies on nalgebra.
//! This implies some differences from the conventions used in ROS.
//!
//! For example, quaternions are represented using nalgebra's convention rather than ROS's.
//! `nalgebra`'s quaternion convention is `Quaternion::new(w, i, j, k)`.
//! On the other hand, ROS uses the `(x, y, z, w)` convention for quaternions.
//!
//! We will use nalgebra's convention throughout this crate,
//! and only convert to/from ROS's convention at I/O boundaries.
//! ROS compatibility functions are marked as deprecated, and should only be used for interfacing with ROS
//! or for maintaining compatibility with existing ROS-based code.

#![no_std]

extern crate alloc;

pub mod geometry;
pub mod transform;

#[derive(Debug, Clone)]
pub struct Header {
    pub frame_id: &'static str,
    pub timestamp: u64,
}

pub use nalgebra::{Quaternion, UnitQuaternion, Vector3};
