//! Adapter to use block devices with file I/O interfaces
//!
//! This module provides an adapter that wraps a BlockDevice and implements
//! the file I/O traits (Read, Write, Seek) to allow block devices to be used
//! with filesystems that expect file-like interfaces.

use super::block_device::BlockDevice;
use super::error::IoError;
use super::io::{IoBase, Read, Seek, SeekFrom, Write};
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cmp::min;
use core::fmt::{self, Debug, Display};

/// Adapter that provides file I/O interface for block devices
#[derive(Debug)]
pub struct BlockDeviceAdapter<D: BlockDevice> {
    /// The underlying block device
    device: Arc<D>,
    /// Current position in the virtual file
    position: u64,
    /// Whether the adapter is in read-only mode
    read_only: bool,
    /// Cache for the current block being accessed
    block_cache: Option<BlockCache>,
}

/// Cache for a single block to optimize sequential access
#[derive(Debug)]
struct BlockCache {
    /// The block number currently cached
    block_num: u64,
    /// The cached block data
    data: Vec<u8>,
    /// Whether the cached data has been modified
    dirty: bool,
}

impl<D: BlockDevice> BlockDeviceAdapter<D> {
    /// Create a new block device adapter
    pub fn new(device: Arc<D>) -> Self {
        Self {
            device,
            position: 0,
            read_only: false,
            block_cache: None,
        }
    }

    /// Create a new read-only block device adapter
    pub fn new_read_only(device: Arc<D>) -> Self {
        Self {
            device,
            position: 0,
            read_only: true,
            block_cache: None,
        }
    }

    /// Get the total size in bytes
    pub fn size(&self) -> u64 {
        self.device.num_blocks() * self.device.block_size() as u64
    }

    /// Load a block into the cache if not already cached
    fn ensure_block_cached(&mut self, block_num: u64) -> Result<(), BlockDeviceAdapterError> {
        match &self.block_cache {
            Some(cache) if cache.block_num == block_num => Ok(()),
            _ => {
                // Flush any dirty block before loading new one
                self.flush_cache()?;
                
                let block_size = self.device.block_size();
                let mut data = alloc::vec![0u8; block_size];
                
                self.device
                    .read_block(block_num, &mut data)
                    .map_err(|_| BlockDeviceAdapterError::IoError)?;
                
                self.block_cache = Some(BlockCache {
                    block_num,
                    data,
                    dirty: false,
                });
                
                Ok(())
            }
        }
    }

    /// Flush the cached block if it's dirty
    fn flush_cache(&mut self) -> Result<(), BlockDeviceAdapterError> {
        if let Some(cache) = &self.block_cache {
            if cache.dirty && !self.read_only {
                // We need to get mutable access to the device through Arc
                // This is safe because we're the only one with access to this adapter
                let device = Arc::get_mut(&mut self.device)
                    .ok_or(BlockDeviceAdapterError::DeviceBusy)?;
                
                device
                    .write_block(cache.block_num, &cache.data)
                    .map_err(|_| BlockDeviceAdapterError::IoError)?;
            }
        }
        Ok(())
    }

    /// Mark the cached block as dirty
    fn mark_cache_dirty(&mut self) {
        if let Some(cache) = &mut self.block_cache {
            cache.dirty = true;
        }
    }
}

impl<D: BlockDevice> IoBase for BlockDeviceAdapter<D> {
    type Error = BlockDeviceAdapterError;
}

impl<D: BlockDevice> Read for BlockDeviceAdapter<D> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            return Ok(0);
        }

        let size = self.size();
        if self.position >= size {
            return Ok(0); // EOF
        }

        let block_size = self.device.block_size();
        let mut bytes_read = 0;

        while bytes_read < buf.len() && self.position < size {
            let block_num = self.position / block_size as u64;
            let offset_in_block = (self.position % block_size as u64) as usize;
            
            self.ensure_block_cached(block_num)?;
            
            let cache = self.block_cache.as_ref().unwrap();
            let available_in_block = block_size - offset_in_block;
            let remaining_in_buf = buf.len() - bytes_read;
            let remaining_in_file = (size - self.position) as usize;
            let to_read = min(available_in_block, min(remaining_in_buf, remaining_in_file));
            
            buf[bytes_read..bytes_read + to_read]
                .copy_from_slice(&cache.data[offset_in_block..offset_in_block + to_read]);
            
            bytes_read += to_read;
            self.position += to_read as u64;
        }

        Ok(bytes_read)
    }
}

impl<D: BlockDevice> Write for BlockDeviceAdapter<D> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if self.read_only {
            return Err(BlockDeviceAdapterError::ReadOnly);
        }

        if buf.is_empty() {
            return Ok(0);
        }

        let size = self.size();
        if self.position >= size {
            return Ok(0); // Can't write past end
        }

        let block_size = self.device.block_size();
        let mut bytes_written = 0;

        while bytes_written < buf.len() && self.position < size {
            let block_num = self.position / block_size as u64;
            let offset_in_block = (self.position % block_size as u64) as usize;
            
            self.ensure_block_cached(block_num)?;
            
            let available_in_block = block_size - offset_in_block;
            let remaining_in_buf = buf.len() - bytes_written;
            let remaining_in_file = (size - self.position) as usize;
            let to_write = min(available_in_block, min(remaining_in_buf, remaining_in_file));
            
            // Modify the cached block
            if let Some(cache) = &mut self.block_cache {
                cache.data[offset_in_block..offset_in_block + to_write]
                    .copy_from_slice(&buf[bytes_written..bytes_written + to_write]);
            }
            self.mark_cache_dirty();
            
            bytes_written += to_write;
            self.position += to_write as u64;
        }

        Ok(bytes_written)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.flush_cache()?;
        
        // Also flush the underlying device
        if !self.read_only {
            let device = Arc::get_mut(&mut self.device)
                .ok_or(BlockDeviceAdapterError::DeviceBusy)?;
            device.flush().map_err(|_| BlockDeviceAdapterError::IoError)?;
        }
        
        Ok(())
    }
}

impl<D: BlockDevice> Seek for BlockDeviceAdapter<D> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let size = self.size() as i64;
        let new_position = match pos {
            SeekFrom::Start(offset) => offset as i64,
            SeekFrom::Current(offset) => self.position as i64 + offset,
            SeekFrom::End(offset) => size + offset,
        };

        if new_position < 0 || new_position > size {
            return Err(BlockDeviceAdapterError::OutOfBounds);
        }

        self.position = new_position as u64;
        Ok(self.position)
    }
}

/// Errors that can occur in the block device adapter
#[derive(Debug, Clone)]
pub enum BlockDeviceAdapterError {
    /// Out of bounds access
    OutOfBounds,
    /// I/O error from the block device
    IoError,
    /// Device is read-only
    ReadOnly,
    /// Failed to write whole buffer
    WriteZero,
    /// Failed to fill whole buffer
    UnexpectedEof,
    /// Operation interrupted
    Interrupted,
    /// Device is busy (multiple references)
    DeviceBusy,
    /// Other error
    Other(alloc::string::String),
}

impl Display for BlockDeviceAdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfBounds => write!(f, "Out of bounds access"),
            Self::IoError => write!(f, "Block device I/O error"),
            Self::ReadOnly => write!(f, "Device is read-only"),
            Self::WriteZero => write!(f, "Failed to write whole buffer"),
            Self::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            Self::Interrupted => write!(f, "Operation interrupted"),
            Self::DeviceBusy => write!(f, "Device is busy"),
            Self::Other(msg) => write!(f, "Error: {}", msg),
        }
    }
}

impl IoError for BlockDeviceAdapterError {
    fn is_interrupted(&self) -> bool {
        matches!(self, Self::Interrupted)
    }

    fn new_unexpected_eof_error() -> Self {
        Self::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        Self::WriteZero
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::block_device::MemoryBlockDevice;

    #[test]
    fn test_read_write() {
        let device = Arc::new(MemoryBlockDevice::new(512, 10));
        let mut adapter = BlockDeviceAdapter::new(device);

        // Write some data
        let data = b"Hello, World!";
        assert_eq!(adapter.write(data).unwrap(), data.len());

        // Seek back to start
        assert_eq!(adapter.seek(SeekFrom::Start(0)).unwrap(), 0);

        // Read it back
        let mut buf = vec![0u8; data.len()];
        assert_eq!(adapter.read(&mut buf).unwrap(), data.len());
        assert_eq!(&buf, data);
    }

    #[test]
    fn test_seek() {
        let device = Arc::new(MemoryBlockDevice::new(512, 10));
        let mut adapter = BlockDeviceAdapter::new(device);

        // Test various seek operations
        assert_eq!(adapter.seek(SeekFrom::Start(100)).unwrap(), 100);
        assert_eq!(adapter.seek(SeekFrom::Current(50)).unwrap(), 150);
        assert_eq!(adapter.seek(SeekFrom::End(-100)).unwrap(), 5120 - 100);

        // Test out of bounds
        assert!(adapter.seek(SeekFrom::Start(10000)).is_err());
        assert!(adapter.seek(SeekFrom::End(100)).is_err());
    }

    #[test]
    fn test_cross_block_access() {
        let device = Arc::new(MemoryBlockDevice::new(512, 10));
        let mut adapter = BlockDeviceAdapter::new(device);

        // Write data that spans multiple blocks
        let mut data = vec![0x42u8; 1024];
        assert_eq!(adapter.seek(SeekFrom::Start(256)).unwrap(), 256);
        assert_eq!(adapter.write(&data).unwrap(), 1024);

        // Read it back
        assert_eq!(adapter.seek(SeekFrom::Start(256)).unwrap(), 256);
        let mut buf = vec![0u8; 1024];
        assert_eq!(adapter.read(&mut buf).unwrap(), 1024);
        assert_eq!(buf, data);
    }
}