//! Simple filesystem creator without factory pattern
//!
//! This module provides direct filesystem creation based on type.

use super::types::{MountError, MountOptions, MountResult};
use crate::file::{
    filesystem::AsyncFileSystem,
    fatfs::AsyncFatFs,
};
use alloc::{boxed::Box, string::ToString, sync::Arc};
use awkernel_lib::file::{
    block_device::BlockDevice,
    fatfs::create_fatfs_from_block_device,
    memfs::MemoryBlockDevice,
};

/// Create a filesystem based on type
pub async fn create_filesystem(
    fs_type: &str,
    device: Arc<dyn BlockDevice>,
    options: &MountOptions,
) -> MountResult<Box<dyn AsyncFileSystem>> {
    match fs_type {
        "memory-fatfs" => {
            // Check if it's a memory block device
            let memory_device = device.as_any()
                .downcast_ref::<MemoryBlockDevice>()
                .ok_or_else(|| MountError::FilesystemError(
                    "memory-fatfs requires a MemoryBlockDevice".into()
                ))?;
            
            let device_arc = Arc::new(memory_device.clone());
            let format = options.fs_options.get("format")
                .map(|v| v == "true")
                .unwrap_or(false);
            
            let fs = create_fatfs_from_block_device(device_arc, format)
                .map_err(MountError::FilesystemError)?;
            
            Ok(Box::new(AsyncFatFs { fs: Arc::new(fs) }))
        }
        
        // Future filesystems can be added here
        // "ext4" => create_ext4_filesystem(device, options),
        // "btrfs" => create_btrfs_filesystem(device, options),
        
        _ => Err(MountError::UnsupportedFilesystem(fs_type.to_string()))
    }
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, "memory-fatfs")
}