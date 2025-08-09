//! Memory-based filesystem implementations

use super::block_device::{BlockDeviceError, BlockResult};
use crate::storage::{transfer_get_info, transfer_mark_completed, StorageDevice, StorageDevError, StorageDeviceType};
use crate::sync::{mcs::MCSNode, mutex::Mutex};
use alloc::{borrow::Cow, sync::Arc, vec, vec::Vec};
use core::any::Any;

/// Default block size for block devices
pub const DEFAULT_BLOCK_SIZE: usize = 512;

/// A memory-backed block device for testing and in-memory filesystems
pub struct MemoryBlockDevice {
    data: Mutex<Vec<u8>>,
    block_size: usize,
    num_blocks: u64,
}

impl core::fmt::Debug for MemoryBlockDevice {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MemoryBlockDevice")
            .field("block_size", &self.block_size)
            .field("num_blocks", &self.num_blocks)
            .field("total_size", &(self.block_size * self.num_blocks as usize))
            .finish()
    }
}

impl MemoryBlockDevice {
    /// Create a new memory block device
    pub fn new(block_size: usize, num_blocks: u64) -> Self {
        let total_size = block_size * num_blocks as usize;
        Self {
            data: Mutex::new(vec![0; total_size]),
            block_size,
            num_blocks,
        }
    }
    
    /// Create a memory block device from pre-allocated memory
    pub fn from_vec(data: Vec<u8>, block_size: usize) -> Self {
        let num_blocks = (data.len() / block_size) as u64;
        Self {
            data: Mutex::new(data),
            block_size,
            num_blocks,
        }
    }
    
    /// Get the offset for a block number
    fn block_offset(&self, block_num: u64) -> Option<usize> {
        if block_num >= self.num_blocks {
            None
        } else {
            Some((block_num as usize) * self.block_size)
        }
    }
}

impl StorageDevice for MemoryBlockDevice {
    // Storage device specific methods
    
    fn device_id(&self) -> u64 {
        // Use a fixed ID for memory device
        0xFFFFFFFF_FFFFFFFF
    }
    
    fn device_name(&self) -> Cow<'static, str> {
        "Memory Block Device".into()
    }
    
    fn device_short_name(&self) -> Cow<'static, str> {
        "memory".into()
    }
    
    fn device_type(&self) -> StorageDeviceType {
        StorageDeviceType::Memory
    }
    
    fn irqs(&self) -> Vec<u16> {
        // Memory device has no IRQs
        vec![]
    }
    
    fn interrupt(&self, _irq: u16) -> Result<(), StorageDevError> {
        // Memory device doesn't handle interrupts
        Ok(())
    }
    
    // Block device methods
    fn block_size(&self) -> usize {
        self.block_size
    }
    
    fn as_any(&self) -> &dyn Any {
        self
    }
    
    fn num_blocks(&self) -> u64 {
        self.num_blocks
    }
    
    fn read_blocks(&self, buf: &mut [u8], transfer_id: u16) -> BlockResult<()> {
        // Get transfer parameters
        let (start_lba, num_blocks, _nsid, _is_read) = transfer_get_info(transfer_id)
            .map_err(|_| BlockDeviceError::IoError)?;
        
        // Validate buffer size
        let total_size = self.block_size * num_blocks as usize;
        if buf.len() < total_size {
            return Err(BlockDeviceError::InvalidBlock);
        }
        
        // Lock data once for all blocks
        let mut node = MCSNode::new();
        let data = self.data.lock(&mut node);
        
        // Read all blocks
        for i in 0..num_blocks {
            let lba = start_lba + i as u64;
            let offset = self.block_offset(lba).ok_or(BlockDeviceError::InvalidBlock)?;
            let buf_offset = (i as usize) * self.block_size;
            buf[buf_offset..buf_offset + self.block_size]
                .copy_from_slice(&data[offset..offset + self.block_size]);
        }
        
        // Mark transfer as completed successfully
        let _ = transfer_mark_completed(transfer_id, 0); // 0 = success
        
        Ok(())
    }
    
    fn write_blocks(&self, buf: &[u8], transfer_id: u16) -> BlockResult<()> {
        // Get transfer parameters
        let (start_lba, num_blocks, _nsid, _is_read) = transfer_get_info(transfer_id)
            .map_err(|_| BlockDeviceError::IoError)?;
        
        // Validate buffer size
        let total_size = self.block_size * num_blocks as usize;
        if buf.len() < total_size {
            return Err(BlockDeviceError::InvalidBlock);
        }
        
        // Lock data once for all blocks
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        
        // Write all blocks
        for i in 0..num_blocks {
            let lba = start_lba + i as u64;
            let offset = self.block_offset(lba).ok_or(BlockDeviceError::InvalidBlock)?;
            let buf_offset = (i as usize) * self.block_size;
            data[offset..offset + self.block_size]
                .copy_from_slice(&buf[buf_offset..buf_offset + self.block_size]);
        }
        
        // Mark transfer as completed successfully
        let _ = transfer_mark_completed(transfer_id, 0); // 0 = success
        
        Ok(())
    }
}

/// Create a memory block device with the specified size
pub fn create_memory_block_device(size: usize, block_size: usize) -> Result<Arc<dyn StorageDevice>, &'static str> {
    // Validate parameters
    if size == 0 {
        return Err("Size must be greater than 0");
    }
    
    if block_size == 0 || !block_size.is_power_of_two() {
        return Err("Block size must be a power of 2");
    }
    
    // Create a zero-initialized Vec for the disk data
    let disk_data = vec![0u8; size];
    
    // Create a MemoryBlockDevice
    let memory_device = Arc::new(MemoryBlockDevice::from_vec(disk_data, block_size));
    
    Ok(memory_device as Arc<dyn StorageDevice>)
}