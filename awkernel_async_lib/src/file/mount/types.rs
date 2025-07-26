//! Types for the async mount system
//!
//! This module re-exports common types from the sync mount system.

// Re-export all types from sync lib including MountError
pub use awkernel_lib::file::mount_types::{
    MountFlags, MountOptions, MountInfo, MountError,
};

/// Result type for mount operations
pub type MountResult<T> = Result<T, MountError>;