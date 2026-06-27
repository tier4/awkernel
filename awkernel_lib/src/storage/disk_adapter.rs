//! Adapter that exposes any `StorageDevice` as a byte-level Read/Write/Seek
//! interface compatible with the FAT filesystem layer.
//!
//! # Background (block vs. byte I/O)
//!
//! Storage devices speak in fixed-size "blocks" (usually 512 bytes), like a
//! shelf of numbered boxes.  The FAT library expects a cursor-based "notebook"
//! where you can read/write any number of bytes at any position.
//!
//! `BlockDeviceDisk` bridges the two: it tracks a byte-level cursor and handles
//! the translation (including read-modify-write for partial block writes).

use crate::{
    file::{
        error::IoError,
        io::{IoBase, Read, Seek, SeekFrom, Write},
        vfs::error::VfsIoError,
    },
    storage::storage_device::{StorageDevError, StorageDevice},
};
use alloc::{string::String, sync::Arc, vec};
use core::fmt;

// ── Main type ─────────────────────────────────────────────────────────────────

/// A byte-level cursor over any `StorageDevice`.
///
/// Implements `Read + Write + Seek` so it can be passed directly to the FAT
/// filesystem implementation.  Partial-block writes use a read-modify-write
/// cycle to preserve surrounding data.
pub struct BlockDeviceDisk {
    device: Arc<dyn StorageDevice + Sync + Send>,
    /// Current byte offset into the virtual "flat" address space of the device.
    position: u64,
    /// Total byte size of the device (cached for Seek::End calculations).
    total_bytes: u64,
}

impl BlockDeviceDisk {
    pub fn new(device: Arc<dyn StorageDevice + Sync + Send>) -> Self {
        let total_bytes = device.num_blocks() * device.block_size() as u64;
        BlockDeviceDisk {
            device,
            position: 0,
            total_bytes,
        }
    }
}

impl fmt::Debug for BlockDeviceDisk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlockDeviceDisk")
            .field("position", &self.position)
            .field("total_bytes", &self.total_bytes)
            .finish()
    }
}

// ── Error type ────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum BlockDeviceDiskError {
    OutOfBounds,
    WriteZero,
    UnexpectedEof,
    Interrupted,
    Device(StorageDevError),
    Other(String),
}

impl fmt::Display for BlockDeviceDiskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockDeviceDiskError::OutOfBounds => write!(f, "Out of bounds access"),
            BlockDeviceDiskError::WriteZero => write!(f, "Failed to write whole buffer"),
            BlockDeviceDiskError::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            BlockDeviceDiskError::Interrupted => write!(f, "Operation interrupted"),
            BlockDeviceDiskError::Device(e) => write!(f, "Device error: {e}"),
            BlockDeviceDiskError::Other(msg) => write!(f, "An error occurred: {msg}"),
        }
    }
}

impl IoError for BlockDeviceDiskError {
    fn is_interrupted(&self) -> bool {
        matches!(self, BlockDeviceDiskError::Interrupted)
    }

    fn new_unexpected_eof_error() -> Self {
        BlockDeviceDiskError::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        BlockDeviceDiskError::WriteZero
    }
}

impl From<BlockDeviceDiskError> for VfsIoError {
    fn from(err: BlockDeviceDiskError) -> Self {
        match err {
            BlockDeviceDiskError::OutOfBounds => VfsIoError::OutOfBounds,
            BlockDeviceDiskError::WriteZero => VfsIoError::WriteZero,
            BlockDeviceDiskError::UnexpectedEof => VfsIoError::UnexpectedEof,
            BlockDeviceDiskError::Interrupted => VfsIoError::Interrupted,
            BlockDeviceDiskError::Device(e) => VfsIoError::Other(alloc::format!("{e}")),
            BlockDeviceDiskError::Other(msg) => VfsIoError::Other(msg),
        }
    }
}

// ── Read / Write / Seek impls ─────────────────────────────────────────────────

impl IoBase for BlockDeviceDisk {
    type Error = BlockDeviceDiskError;
}

impl Read for BlockDeviceDisk {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if self.position >= self.total_bytes {
            return Ok(0);
        }
        let bsz = self.device.block_size() as u64;
        let available = (self.total_bytes - self.position) as usize;
        let to_read = core::cmp::min(buf.len(), available);

        let start_lba = self.position / bsz;
        let start_off = (self.position % bsz) as usize;
        let end_byte = self.position + to_read as u64;
        let end_lba = (end_byte + bsz - 1) / bsz;
        let blocks = (end_lba - start_lba) as usize;

        let mut tmp = vec![0u8; blocks * bsz as usize];
        self.device
            .read_blocks_at(start_lba, &mut tmp)
            .map_err(BlockDeviceDiskError::Device)?;

        buf[..to_read].copy_from_slice(&tmp[start_off..start_off + to_read]);
        self.position += to_read as u64;
        Ok(to_read)
    }
}

impl Write for BlockDeviceDisk {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if self.position >= self.total_bytes {
            return Ok(0);
        }
        let bsz = self.device.block_size() as u64;
        let available = (self.total_bytes - self.position) as usize;
        let to_write = core::cmp::min(buf.len(), available);

        let start_lba = self.position / bsz;
        let start_off = (self.position % bsz) as usize;
        let end_byte = self.position + to_write as u64;
        let end_lba = (end_byte + bsz - 1) / bsz;
        let blocks = (end_lba - start_lba) as usize;

        // Read-modify-write: preserve bytes outside the write range within
        // the first and last blocks.
        let mut tmp = vec![0u8; blocks * bsz as usize];
        self.device
            .read_blocks_at(start_lba, &mut tmp)
            .map_err(BlockDeviceDiskError::Device)?;

        tmp[start_off..start_off + to_write].copy_from_slice(&buf[..to_write]);

        self.device
            .write_blocks_at(start_lba, &tmp)
            .map_err(BlockDeviceDiskError::Device)?;

        self.position += to_write as u64;
        Ok(to_write)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl Seek for BlockDeviceDisk {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let total = self.total_bytes as i64;
        let new_pos = match pos {
            SeekFrom::Start(offset) => offset as i64,
            SeekFrom::Current(offset) => self.position as i64 + offset,
            SeekFrom::End(offset) => total + offset,
        };
        if new_pos < 0 || new_pos > total {
            return Err(BlockDeviceDiskError::OutOfBounds);
        }
        self.position = new_pos as u64;
        Ok(self.position)
    }
}
