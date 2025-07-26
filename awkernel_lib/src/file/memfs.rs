//! Memory-based filesystem implementations

use super::block_device::{BlockDevice, BlockDeviceError, BlockResult};
use alloc::{vec, vec::Vec};
use core::any::Any;

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

impl BlockDevice for MemoryBlockDevice {
    fn block_size(&self) -> usize {
        self.block_size
    }
    
    fn as_any(&self) -> &dyn Any {
        self
    }
    
    fn num_blocks(&self) -> u64 {
        self.num_blocks
    }
    
    fn read_block(&self, block_num: u64, buf: &mut [u8]) -> BlockResult<()> {
        let offset = self.block_offset(block_num).ok_or(BlockDeviceError::InvalidBlock)?;
        buf[..self.block_size].copy_from_slice(&self.data[offset..offset + self.block_size]);
        Ok(())
    }
    
    fn write_block(&mut self, block_num: u64, buf: &[u8]) -> BlockResult<()> {
        let offset = self.block_offset(block_num).ok_or(BlockDeviceError::InvalidBlock)?;
        self.data[offset..offset + self.block_size].copy_from_slice(&buf[..self.block_size]);
        Ok(())
    }
}