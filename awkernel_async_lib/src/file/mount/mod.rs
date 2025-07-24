//! Unified async mount system for AWKernel
//!
//! This module provides all mount-related functionality including:
//! - Mount registry that tracks both mount points and filesystem instances
//! - Filesystem factory pattern for creating filesystem instances
//! - High-level mount management API
//! - Mount-aware path resolution

pub mod factory;
pub mod manager;
pub mod registry;
pub mod types;

// Re-export commonly used types and functions
pub use factory::{AsyncFileSystemFactory, FatFsFactory};
pub use manager::{MountManager, mount_memory_fatfs};
pub use registry::{
    init_mount_registry, 
    register_mount, 
    unregister_mount,
    resolve_filesystem_for_path,
    list_mounts,
};
pub use types::{MountInfo, MountOptions, MountError, MountResult};

// Re-export mount flags from sync types
pub use awkernel_lib::file::mount_types::MountFlags;