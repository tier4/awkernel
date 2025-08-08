//! Memory-based filesystem implementations

use super::block_device::{BlockDeviceError, BlockResult};
use crate::storage::{StorageDevice, StorageDevError, StorageDeviceType};
use alloc::{borrow::Cow, sync::Arc, vec, vec::Vec};
use core::any::Any;

/// Default block size for block devices
pub const DEFAULT_BLOCK_SIZE: usize = 512;

/// A memory-backed block device for testing and in-memory filesystems
#[derive(Debug, Clone)]
pub struct MemoryBlockDevice {
    data: Vec<u8>,
    block_size: usize,
    num_blocks: u64,
}

impl MemoryBlockDevice {
    /// Create a new memory block device
    pub fn new(block_size: usize, num_blocks: u64) -> Self {
        let total_size = block_size * num_blocks as usize;
        Self {
            data: vec![0; total_size],
            block_size,
            num_blocks,
        }
    }
    
    /// Create a memory block device from pre-allocated memory
    pub fn from_vec(data: Vec<u8>, block_size: usize) -> Self {
        let num_blocks = (data.len() / block_size) as u64;
        Self {
            data,
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
    
    fn read_block(&self, block_num: u64, buf: &mut [u8], _transfer_id: u16) -> BlockResult<()> {
        let offset = self.block_offset(block_num).ok_or(BlockDeviceError::InvalidBlock)?;
        buf[..self.block_size].copy_from_slice(&self.data[offset..offset + self.block_size]);
        Ok(())
    }
    
    fn write_block(&mut self, block_num: u64, buf: &[u8], _transfer_id: u16) -> BlockResult<()> {
        let offset = self.block_offset(block_num).ok_or(BlockDeviceError::InvalidBlock)?;
        self.data[offset..offset + self.block_size].copy_from_slice(&buf[..self.block_size]);
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