//! Unified async mount system for AWKernel
//!
//! This module provides all mount-related functionality including:
//! - Mount registry that tracks both mount points and filesystem instances
//! - Filesystem factory pattern for creating filesystem instances
//! - High-level mount management API
//! - Mount-aware path resolution

pub mod filesystem_creator;
pub mod registry;

// Re-export commonly used types and functions
pub use filesystem_creator::{
    create_filesystem, 
    is_filesystem_supported,
    create_memory_block_device,
    DEFAULT_BLOCK_SIZE,
    FS_TYPE_FATFS,
};
pub use registry::{
    mount, unmount, list_mounts, get_mount_info,
    resolve_filesystem_for_path,
};

// Re-export mount types from sync lib
pub use awkernel_lib::file::mount_types::{
    MountFlags, MountOptions, MountInfo, MountError,
};

/// Result type for mount operations
pub type MountResult<T> = Result<T, MountError>;