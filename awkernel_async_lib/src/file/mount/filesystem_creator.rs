//! Simple filesystem creator without factory pattern
//!
//! This module provides direct filesystem creation based on type and
//! helper functions for creating block devices.

use super::{MountError, MountOptions, MountResult};
use crate::file::{
    filesystem::AsyncFileSystem,
    fatfs::AsyncFatFs,
};
use alloc::{boxed::Box, string::ToString, sync::Arc, vec};
use awkernel_lib::file::{
    block_device::BlockDevice,
    fatfs::create_fatfs_from_block_device,
    memfs::MemoryBlockDevice,
};

/// Filesystem type for FAT filesystem
pub const FS_TYPE_FATFS: &str = "fatfs";

/// Create a filesystem based on type
pub async fn create_filesystem(
    fs_type: &str,
    device: Arc<dyn BlockDevice>,
    options: &MountOptions,
) -> MountResult<Box<dyn AsyncFileSystem>> {
    match fs_type {
        FS_TYPE_FATFS => {
            // Try to downcast to concrete types that FatFS supports
            if let Some(memory_device) = device.as_any().downcast_ref::<MemoryBlockDevice>() {
                // Memory block device
                let device_arc = Arc::new(memory_device.clone());
                let format = options.fs_options.get("format")
                    .map(|v| v == "true")
                    .unwrap_or(false);
                
                let fs = create_fatfs_from_block_device(device_arc, format)
                    .map_err(MountError::FilesystemError)?;
                
                Ok(Box::new(AsyncFatFs { fs: Arc::new(fs) }))
            } else {
                // Future: Add support for other block device types here
                // e.g., if let Some(disk_device) = device.as_any().downcast_ref::<DiskBlockDevice>() { ... }
                Err(MountError::FilesystemError(
                    "FatFS currently only supports MemoryBlockDevice".to_string()
                ))
            }
        }
        
        // Future filesystems can be added here
        // "ext4" => create_ext4_filesystem(device, options),
        // "btrfs" => create_btrfs_filesystem(device, options),
        
        _ => Err(MountError::UnsupportedFilesystem(fs_type.to_string()))
    }
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, FS_TYPE_FATFS)
}

/// Default block size for block devices
pub const DEFAULT_BLOCK_SIZE: usize = 512;

/// Create a memory block device with the specified size
pub fn create_memory_block_device(size: usize, block_size: usize) -> MountResult<Arc<dyn BlockDevice>> {
    // Validate parameters
    if size == 0 {
        return Err(MountError::FilesystemError("Size must be greater than 0".to_string()));
    }
    
    if block_size == 0 || !block_size.is_power_of_two() {
        return Err(MountError::FilesystemError("Block size must be a power of 2".to_string()));
    }
    
    // Create a zero-initialized Vec for the disk data
    let disk_data = vec![0u8; size];
    
    // Create a MemoryBlockDevice
    let memory_device = Arc::new(MemoryBlockDevice::from_vec(disk_data, block_size));
    
    Ok(memory_device as Arc<dyn BlockDevice>)
}