//! High-level mount management API
//!
//! This module provides the main API for mounting and unmounting filesystems.

use super::{
    filesystem_creator::create_filesystem,
    registry::{init_mount_registry, get_registry, list_mounts as list_mounts_internal, get_mount_info as get_mount_info_internal},
    types::{MountError, MountResult},
};
use alloc::{
    string::String,
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::file::{
    block_device::BlockDevice,
    mount_types::{MountInfo, MountOptions},
};

/// Initialize the mount system
pub fn init() -> MountResult<()> {
    init_mount_registry();
    Ok(())
}

/// Mount a filesystem
pub async fn mount(
    path: impl Into<String>,
    source: impl Into<String>,
    fs_type: impl Into<String>,
    device: Option<Arc<dyn BlockDevice>>,
    options: MountOptions,
) -> MountResult<()> {
    let path = path.into();
    let source = source.into();
    let fs_type = fs_type.into();
    
    // Validate path
    if !path.starts_with('/') {
        return Err(MountError::InvalidPath(path));
    }
    
    // Device is required
    let device = device.ok_or_else(|| 
        MountError::FilesystemError("Block device required".into())
    )?;
    
    // Create the filesystem instance
    let filesystem = create_filesystem(&fs_type, device, &options).await?;
    
    // Get the registry and register the mount
    let registry = get_registry()?;
    registry.register_mount(path, source, fs_type, options, filesystem)?;
    
    Ok(())
}

/// Unmount a filesystem
pub fn unmount(path: impl AsRef<str>) -> MountResult<()> {
    let registry = get_registry()?;
    registry.unregister_mount(path.as_ref())
}

/// List all mount points
pub fn list_mounts() -> Vec<MountInfo> {
    list_mounts_internal()
}

/// Get mount information for a path
pub fn get_mount_info(path: impl AsRef<str>) -> MountResult<MountInfo> {
    get_mount_info_internal(path.as_ref())
}

