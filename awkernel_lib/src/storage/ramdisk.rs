use alloc::{borrow::Cow, sync::Arc, vec, vec::Vec};
use crate::sync::rwlock::RwLock;
use core::sync::atomic::{AtomicU64, Ordering};

use super::storage_device::{StorageDevError, StorageDevice, StorageDeviceType};

/// A simple in-memory block device backed by a `Vec<u8>`.
///
/// The underlying bytes are shared via `Arc<RwLock<Vec<u8>>>` so that
/// `StorageDeviceDisk` (the Read/Write/Seek adapter for the FAT layer) can
/// access the same memory without copying.
pub struct RamDisk {
    /// Shared byte buffer.  All blocks live here contiguously.
    data: Arc<RwLock<Vec<u8>>>,
    block_size: usize,
    num_blocks: u64,
    /// Sequential position used by `read_blocks` / `write_blocks` (non-LBA API).
    seq_pos: AtomicU64,
}

impl RamDisk {
    /// Create a new RAM disk.
    ///
    /// `num_blocks * block_size` bytes are zero-allocated immediately.
    /// `block_size` should be 512 (the standard sector size).
    pub fn new(num_blocks: u64, block_size: usize) -> Self {
        let total = num_blocks as usize * block_size;
        RamDisk {
            data: Arc::new(RwLock::new(vec![0u8; total])),
            block_size,
            num_blocks,
            seq_pos: AtomicU64::new(0),
        }
    }


}

impl StorageDevice for RamDisk {
    fn device_id(&self) -> u64 {
        0
    }

    fn device_name(&self) -> Cow<'static, str> {
        "RAM Disk".into()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "ramdisk".into()
    }

    fn device_type(&self) -> StorageDeviceType {
        StorageDeviceType::Memory
    }

    fn irqs(&self) -> Vec<u16> {
        Vec::new()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), StorageDevError> {
        Ok(())
    }

    fn block_size(&self) -> usize {
        self.block_size
    }

    fn num_blocks(&self) -> u64 {
        self.num_blocks
    }

    /// Sequential read: reads `buf.len()` bytes from the current position and advances it.
    fn read_blocks(&self, buf: &mut [u8], _transfer_id: u16) -> Result<(), StorageDevError> {
        if buf.len() % self.block_size != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        let pos = self.seq_pos.load(Ordering::Relaxed) as usize;
        let data = self.data.read();
        if pos + buf.len() > data.len() {
            return Err(StorageDevError::InvalidBlock);
        }
        buf.copy_from_slice(&data[pos..pos + buf.len()]);
        self.seq_pos.fetch_add(buf.len() as u64, Ordering::Relaxed);
        Ok(())
    }

    /// Sequential write: writes `buf.len()` bytes at the current position and advances it.
    fn write_blocks(&self, buf: &[u8], _transfer_id: u16) -> Result<(), StorageDevError> {
        if buf.len() % self.block_size != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        let pos = self.seq_pos.load(Ordering::Relaxed) as usize;
        let mut data = self.data.write();
        if pos + buf.len() > data.len() {
            return Err(StorageDevError::InvalidBlock);
        }
        data[pos..pos + buf.len()].copy_from_slice(buf);
        self.seq_pos.fetch_add(buf.len() as u64, Ordering::Relaxed);
        Ok(())
    }

    /// Random-access read: reads `buf.len()` bytes starting at block `lba`.
    fn read_blocks_at(&self, lba: u64, buf: &mut [u8]) -> Result<(), StorageDevError> {
        if buf.len() % self.block_size != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        let start = lba as usize * self.block_size;
        let data = self.data.read();
        if start + buf.len() > data.len() {
            return Err(StorageDevError::InvalidBlock);
        }
        buf.copy_from_slice(&data[start..start + buf.len()]);
        Ok(())
    }

    /// Random-access write: writes `buf.len()` bytes starting at block `lba`.
    fn write_blocks_at(&self, lba: u64, buf: &[u8]) -> Result<(), StorageDevError> {
        if buf.len() % self.block_size != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        let start = lba as usize * self.block_size;
        let mut data = self.data.write();
        if start + buf.len() > data.len() {
            return Err(StorageDevError::InvalidBlock);
        }
        data[start..start + buf.len()].copy_from_slice(buf);
        Ok(())
    }
}
