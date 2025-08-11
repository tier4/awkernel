//! Block device adapter that works with any StorageDevice implementation
//! This allows mounting of any device type without knowing the concrete type at compile time

use crate::{
    storage::{
        allocate_transfer_sync, free_transfer, get_device_namespace, transfer_set_params,
        transfer_set_poll_mode, StorageDevice, transfer_is_completed,
    },
};
use alloc::{string::String, sync::Arc, vec, vec::Vec};
use core::cmp::min;

use super::{
    error::IoError,
    io::{IoBase, Read, Seek, SeekFrom, Write},
};

/// Default timeout for I/O operations in milliseconds
const DEFAULT_IO_TIMEOUT_MS: u64 = 5000;

/// A block device adapter that provides file-like I/O operations
/// for any storage device implementing the StorageDevice trait.
/// 
/// This adapter uses the unified transfer API for all device types:
/// - MemoryBlockDevice: Completes transfers synchronously
/// - Hardware devices (NVMe, etc.): May complete transfers asynchronously
pub struct BlockDeviceAdapter {
    /// The underlying block device as a trait object
    device: Arc<dyn StorageDevice>,
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

impl core::fmt::Debug for BlockDeviceAdapter {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BlockDeviceAdapter")
            .field("device_id", &self.device.device_id())
            .field("device_name", &self.device.device_name())
            .field("position", &self.position)
            .field("read_only", &self.read_only)
            .field("block_cache", &self.block_cache.as_ref().map(|c| c.block_num))
            .finish()
    }
}

impl BlockDeviceAdapter {
    /// Create a new block device adapter
    pub fn new(device: Arc<dyn StorageDevice>) -> Self {
        Self {
            device,
            position: 0,
            read_only: false,
            block_cache: None,
        }
    }

    /// Create a new read-only block device adapter
    pub fn new_read_only(device: Arc<dyn StorageDevice>) -> Self {
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

    /// Helper function to wait for transfer completion
    fn wait_for_transfer_completion(transfer_id: u16) -> Result<(), BlockDeviceAdapterError> {
        // Wait for completion if device didn't mark it complete
        if let Ok(completed) = transfer_is_completed(transfer_id) {
            if !completed {
                // Poll for completion with timeout
                for _ in 0..50000 {  // ~5 second timeout with 100us delays
                    if let Ok(true) = transfer_is_completed(transfer_id) {
                        break;
                    }
                    core::hint::spin_loop();
                }
            }
        }
        Ok(())
    }

    /// Load a block into the cache if not already cached
    fn ensure_block_cached(&mut self, block_num: u64) -> Result<(), BlockDeviceAdapterError> {
        match &self.block_cache {
            Some(cache) if cache.block_num == block_num => Ok(()),
            _ => {
                // Flush any dirty block before loading new one
                self.flush_cache()?;
                
                let block_size = self.device.block_size();
                let mut data = vec![0u8; block_size];
                
                // All devices now use transfers uniformly
                let transfer_id = allocate_transfer_sync(self.device.device_id())
                    .map_err(|_| BlockDeviceAdapterError::IoError)?;
                
                // Set up transfer parameters
                let nsid = get_device_namespace(self.device.device_id()).unwrap_or(1);
                let _ = transfer_set_params(transfer_id, block_num, 1, true, nsid);
                let _ = transfer_set_poll_mode(transfer_id, true, DEFAULT_IO_TIMEOUT_MS as u32);
                
                // Perform the read (read_blocks works for single blocks too)
                let result = self.device
                    .read_blocks(&mut data, transfer_id)
                    .map_err(|_| BlockDeviceAdapterError::IoError);
                
                // Wait for completion
                Self::wait_for_transfer_completion(transfer_id)?;
                
                // Always free the transfer
                free_transfer(transfer_id);
                
                result?;
                
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
                // No need for mutable access - StorageDevice methods take &self
                let device_id = self.device.device_id();
                let transfer_id = allocate_transfer_sync(device_id)
                    .map_err(|_| BlockDeviceAdapterError::IoError)?;
                
                // Set up transfer parameters
                let nsid = get_device_namespace(self.device.device_id()).unwrap_or(1);
                let _ = transfer_set_params(transfer_id, cache.block_num, 1, false, nsid);
                let _ = transfer_set_poll_mode(transfer_id, true, DEFAULT_IO_TIMEOUT_MS as u32);
                
                // Perform the write (write_blocks works for single blocks too)
                let result = self.device
                    .write_blocks(&cache.data, transfer_id)
                    .map_err(|_| BlockDeviceAdapterError::IoError);
                
                // Wait for completion
                Self::wait_for_transfer_completion(transfer_id)?;
                
                // Always free the transfer
                free_transfer(transfer_id);
                
                result?;
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

impl IoBase for BlockDeviceAdapter {
    type Error = BlockDeviceAdapterError;
}

impl Read for BlockDeviceAdapter {
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

impl Write for BlockDeviceAdapter {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if self.read_only {
            return Err(BlockDeviceAdapterError::ReadOnly);
        }

        if buf.is_empty() {
            return Ok(0);
        }

        let size = self.size();
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
        
        // Flush the underlying device
        if !self.read_only {
            // Allocate transfer for flush operation
            let transfer_id = allocate_transfer_sync(self.device.device_id())
                .map_err(|_| BlockDeviceAdapterError::IoError)?;
            
            // Perform flush
            let result = self.device.flush(transfer_id)
                .map_err(|_| BlockDeviceAdapterError::IoError);
            
            // Wait for completion (memory devices complete immediately)
            Self::wait_for_transfer_completion(transfer_id)?;
            
            // Always free the transfer
            free_transfer(transfer_id);
            
            result?;
        }
        
        Ok(())
    }
}

impl Seek for BlockDeviceAdapter {
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

/// Error types for block device operations
#[derive(Debug)]
pub enum BlockDeviceAdapterError {
    /// Generic I/O error
    IoError,
    /// Attempt to write to a read-only device
    ReadOnly,
    /// Seek position out of bounds
    OutOfBounds,
    /// Failed to write whole buffer
    WriteZero,
    /// Failed to fill whole buffer
    UnexpectedEof,
    /// Operation interrupted
    Interrupted,
    /// Device is busy (multiple references)
    DeviceBusy,
    /// Other error
    Other(String),
}

impl core::fmt::Display for BlockDeviceAdapterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::IoError => write!(f, "I/O error"),
            Self::ReadOnly => write!(f, "Device is read-only"),
            Self::OutOfBounds => write!(f, "Seek position out of bounds"),
            Self::WriteZero => write!(f, "Failed to write whole buffer"),
            Self::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            Self::Interrupted => write!(f, "Operation interrupted"),
            Self::DeviceBusy => write!(f, "Device is busy"),
            Self::Other(msg) => write!(f, "Error: {msg}"),
        }
    }
}

impl IoError for BlockDeviceAdapterError {
    fn is_interrupted(&self) -> bool {
        matches!(self, BlockDeviceAdapterError::Interrupted)
    }

    fn new_unexpected_eof_error() -> Self {
        BlockDeviceAdapterError::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        BlockDeviceAdapterError::WriteZero
    }
}

impl From<BlockDeviceAdapterError> for super::vfs::error::VfsIoError {
    fn from(e: BlockDeviceAdapterError) -> Self {
        use super::vfs::error::VfsIoError;
        match e {
            BlockDeviceAdapterError::IoError => VfsIoError::Other("I/O error".into()),
            BlockDeviceAdapterError::ReadOnly => VfsIoError::Other("Device is read-only".into()),
            BlockDeviceAdapterError::OutOfBounds => VfsIoError::Other("Seek position out of bounds".into()),
            BlockDeviceAdapterError::WriteZero => VfsIoError::WriteZero,
            BlockDeviceAdapterError::UnexpectedEof => VfsIoError::UnexpectedEof,
            BlockDeviceAdapterError::Interrupted => VfsIoError::Interrupted,
            BlockDeviceAdapterError::DeviceBusy => VfsIoError::Other("Device is busy".into()),
            BlockDeviceAdapterError::Other(msg) => VfsIoError::Other(msg),
        }
    }
}

// Legacy error types for compatibility
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