//! Block device factory for creating different types of block devices
//!
//! This module provides functions to create various block devices 
//! that can be used with filesystems.

use alloc::{sync::Arc, vec};
use awkernel_lib::file::{
    block_device::BlockDevice,
    memfs::MemoryBlockDevice,
};
use super::types::{MountError, MountResult};

/// Default block size for block devices
pub const DEFAULT_BLOCK_SIZE: usize = 512;

/// Create a memory block device with the specified size
pub fn create_memory_block_device(size: usize, block_size: usize) -> MountResult<Arc<dyn BlockDevice>> {
    // Validate parameters
    if size == 0 {
        return Err(MountError::FilesystemError("Size must be greater than 0".into()));
    }
    
    if block_size == 0 || !block_size.is_power_of_two() {
        return Err(MountError::FilesystemError("Block size must be a power of 2".into()));
    }
    
    // Create a zero-initialized Vec for the disk data
    let disk_data = vec![0u8; size];
    
    // Create a MemoryBlockDevice
    let memory_device = Arc::new(MemoryBlockDevice::from_vec(disk_data, block_size));
    
    Ok(memory_device as Arc<dyn BlockDevice>)
}