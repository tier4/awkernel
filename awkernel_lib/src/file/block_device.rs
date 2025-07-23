//! Block device abstraction for AWKernel
//!
//! This module provides traits and types for block device operations
//! that will be used by filesystems like ext4.

use alloc::{vec, vec::Vec};
use core::fmt::Debug;

/// Errors that can occur during block device operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockDeviceError {
    /// Invalid block number
    InvalidBlock,
    /// I/O error occurred
    IoError,
    /// Device is read-only
    ReadOnly,
    /// Operation not supported
    NotSupported,
}

/// Result type for block device operations
pub type BlockResult<T> = Result<T, BlockDeviceError>;

/// Trait for block devices
///
/// This trait defines the interface that block devices must implement
/// to be used by filesystems.
pub trait BlockDevice: Send + Sync {
    /// Get the block size in bytes
    fn block_size(&self) -> usize;
    
    /// Get the total number of blocks
    fn num_blocks(&self) -> u64;
    
    /// Read a single block into the provided buffer
    ///
    /// The buffer must be at least `block_size()` bytes.
    fn read_block(&self, block_num: u64, buf: &mut [u8]) -> BlockResult<()>;
    
    /// Write a single block from the provided buffer
    ///
    /// The buffer must be exactly `block_size()` bytes.
    fn write_block(&mut self, block_num: u64, buf: &[u8]) -> BlockResult<()>;
    
    /// Read multiple blocks into the provided buffer
    ///
    /// Default implementation calls `read_block` multiple times.
    fn read_blocks(&self, start_block: u64, num_blocks: u32, buf: &mut [u8]) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.read_block(start_block + i, &mut buf[offset..offset + block_size])?;
        }
        Ok(())
    }
    
    /// Write multiple blocks from the provided buffer
    ///
    /// Default implementation calls `write_block` multiple times.
    fn write_blocks(&mut self, start_block: u64, num_blocks: u32, buf: &[u8]) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.write_block(start_block + i, &buf[offset..offset + block_size])?;
        }
        Ok(())
    }
    
    /// Flush any cached writes to the device
    fn flush(&mut self) -> BlockResult<()> {
        Ok(())
    }
}

/// A memory-backed block device for testing
#[derive(Debug)]
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

/// Information about a block device
#[derive(Debug, Clone)]
pub struct BlockDeviceInfo {
    /// Device identifier
    pub device_id: alloc::string::String,
    /// Block size in bytes
    pub block_size: usize,
    /// Total number of blocks
    pub num_blocks: u64,
    /// Whether the device is read-only
    pub read_only: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_memory_block_device() {
        let mut device = MemoryBlockDevice::new(512, 100);
        let mut buf = vec![0u8; 512];
        
        // Write some data
        buf[0] = 0xDE;
        buf[1] = 0xAD;
        buf[2] = 0xBE;
        buf[3] = 0xEF;
        
        assert!(device.write_block(0, &buf).is_ok());
        
        // Read it back
        let mut read_buf = vec![0u8; 512];
        assert!(device.read_block(0, &mut read_buf).is_ok());
        
        assert_eq!(read_buf[0], 0xDE);
        assert_eq!(read_buf[1], 0xAD);
        assert_eq!(read_buf[2], 0xBE);
        assert_eq!(read_buf[3], 0xEF);
    }
}