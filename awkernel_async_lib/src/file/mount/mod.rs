//! Unified async mount system for AWKernel
//!
//! This module provides all mount-related functionality including:
//! - Mount registry that tracks both mount points and filesystem instances
//! - Filesystem factory pattern for creating filesystem instances
//! - High-level mount management API
//! - Mount-aware path resolution

pub mod block_device_factory;
pub mod filesystem_creator;
pub mod manager;
pub mod registry;
pub mod types;

// Re-export commonly used types and functions
pub use block_device_factory::{create_memory_block_device, DEFAULT_BLOCK_SIZE};
pub use filesystem_creator::{create_filesystem, is_filesystem_supported};
pub use manager::{init, mount, unmount, list_mounts, get_mount_info};
pub use registry::{
    init_mount_registry, 
    resolve_filesystem_for_path,
};
pub use types::{MountError, MountResult};

// Re-export mount types from sync lib
pub use awkernel_lib::file::mount_types::{MountFlags, MountOptions, MountInfo};

// Compatibility re-export
pub struct MountManager;
impl MountManager {
    pub fn init() -> types::MountResult<()> { init() }
    pub async fn mount(
        path: impl Into<alloc::string::String>,
        source: impl Into<alloc::string::String>,
        fs_type: impl Into<alloc::string::String>,
        device: Option<alloc::sync::Arc<dyn awkernel_lib::file::block_device::BlockDevice>>,
        options: MountOptions,
    ) -> types::MountResult<()> {
        mount(path, source, fs_type, device, options).await
    }
    pub fn unmount(path: impl AsRef<str>) -> types::MountResult<()> { unmount(path) }
    pub fn list_mounts() -> alloc::vec::Vec<MountInfo> { list_mounts() }
    pub fn get_mount_info(path: impl AsRef<str>) -> types::MountResult<MountInfo> { get_mount_info(path) }
}