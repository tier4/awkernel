extern crate alloc;

use super::error::IoError;
use super::io::{IoBase, Read, Seek, SeekFrom, Write};
use alloc::{string::String, vec::Vec};
use core::fmt::{self, Debug};

pub struct InMemoryDisk {
    data: Vec<u8>,
    position: u64,
}

impl InMemoryDisk {
    pub fn new(data: Vec<u8>, position: u64) -> Self {
        InMemoryDisk { data, position }
    }
}

impl IoBase for InMemoryDisk {
    type Error = InMemoryDiskError;
}

impl Read for InMemoryDisk {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let len = (self.data.len() as u64 - self.position) as usize;
        let bytes_to_read = core::cmp::min(buf.len(), len);
        if bytes_to_read == 0 {
            return Ok(0);
        }
        buf[..bytes_to_read].copy_from_slice(
            &self.data[self.position as usize..self.position as usize + bytes_to_read],
        );
        self.position += bytes_to_read as u64;
        Ok(bytes_to_read)
    }
}

impl Write for InMemoryDisk {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let len = (self.data.len() as u64 - self.position) as usize;
        let bytes_to_write = core::cmp::min(buf.len(), len);
        if bytes_to_write == 0 {
            return Ok(0);
        }
        self.data[self.position as usize..self.position as usize + bytes_to_write]
            .copy_from_slice(&buf[..bytes_to_write]);
        self.position += bytes_to_write as u64;
        Ok(bytes_to_write)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(()) // In-memory, nothing to flush
    }
}

impl Seek for InMemoryDisk {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let new_position = match pos {
            SeekFrom::Start(offset) => offset as i64,
            SeekFrom::Current(offset) => self.position as i64 + offset,
            SeekFrom::End(offset) => self.data.len() as i64 + offset,
        };

        if new_position < 0 || new_position > self.data.len() as i64 {
            return Err(InMemoryDiskError::OutOfBounds);
        }

        self.position = new_position as u64;
        Ok(self.position)
    }
}

#[derive(Debug)]
pub enum InMemoryDiskError {
    OutOfBounds,
    WriteZero,
    UnexpectedEof,
    Interrupted,
    Other(String),
}

impl fmt::Display for InMemoryDiskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InMemoryDiskError::OutOfBounds => write!(f, "Out of bounds access"),
            InMemoryDiskError::WriteZero => write!(f, "Failed to write whole buffer"),
            InMemoryDiskError::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            InMemoryDiskError::Interrupted => write!(f, "Operation interrupted"),
            InMemoryDiskError::Other(msg) => write!(f, "An error occurred: {msg}"),
        }
    }
}

impl IoError for InMemoryDiskError {
    fn is_interrupted(&self) -> bool {
        matches!(self, InMemoryDiskError::Interrupted)
    }

    fn new_unexpected_eof_error() -> Self {
        InMemoryDiskError::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        InMemoryDiskError::WriteZero
    }
}
