#![no_std]

extern crate alloc;

use alloc::{string::String, vec::Vec};
use core::fmt;
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read, Seek, SeekFrom, Write,
};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test fatfs".into(),
        fatfs_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn fatfs_test() {
    let mut disk = InMemoryDisk::new(DISK_SIZE);
    let options = FormatVolumeOptions::new();

    match format_volume(&mut disk, options) {
        Ok(_) => log::info!("FAT filesystem formatted successfully in memory!"),
        Err(e) => log::info!("Error formatting: {:?}", e),
    }

    let fs = match FileSystem::new(disk, FsOptions::new()) {
        Ok(fs) => fs,
        Err(e) => panic!("Error new file system: {:?}", e),
    };
    let root_dir = fs.root_dir();
    let mut file = match root_dir.create_file("file.txt") {
        Ok(file) => file,
        Err(e) => panic!("Error create file: {:?}", e),
    };

    let data_to_write = b"Hello World!";
    let w_bytes = match file.write(data_to_write) {
        Ok(w_bytes) => w_bytes,
        Err(e) => panic!("Erro write file: {:?}", e),
    };

    let mut buf = Vec::new();
    buf.resize(w_bytes, 0);
    let _ = match file.read(&mut buf) {
        Ok(r_bytes) => r_bytes,
        Err(e) => panic!("Erro read file: {:?}", e),
    };

    match core::str::from_utf8(&buf) {
        Ok(s) => log::info!("Vec<u8> 内容 (UTF-8): {}", s),
        Err(_) => log::info!("Vec<u8> 内容 (UTF-8): [不正な UTF-8 シーケンス]",),
    }
}

const DISK_SIZE: usize = 1024 * 1024; // 1MB

struct InMemoryDisk {
    data: Vec<u8>,
    position: u64,
}

impl InMemoryDisk {
    fn new(size: usize) -> Self {
        let mut data = Vec::new();
        data.resize(size, 0);
        InMemoryDisk { data, position: 0 }
    }
}

impl IoBase for InMemoryDisk {
    type Error = InMemoryDiskError;
}

impl Read for InMemoryDisk {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let len = core::cmp::min(buf.len(), (self.data.len() as u64 - self.position) as usize);
        if len == 0 {
            return Ok(0);
        }
        buf[..len]
            .copy_from_slice(&self.data[self.position as usize..self.position as usize + len]);
        self.position += len as u64;
        Ok(len)
    }
}

impl Write for InMemoryDisk {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let len = core::cmp::min(buf.len(), (self.data.len() as u64 - self.position) as usize);
        if len == 0 {
            return Ok(0);
        }
        self.data[self.position as usize..self.position as usize + len]
            .copy_from_slice(&buf[..len]);
        self.position += len as u64;
        Ok(len)
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
            InMemoryDiskError::Other(msg) => write!(f, "An error occurred: {}", msg),
        }
    }
}

impl fatfs::IoError for InMemoryDiskError {
    fn is_interrupted(&self) -> bool {
        match self {
            InMemoryDiskError::Interrupted => true,
            _ => false,
        }
    }

    fn new_unexpected_eof_error() -> Self {
        InMemoryDiskError::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        InMemoryDiskError::WriteZero
    }
}
