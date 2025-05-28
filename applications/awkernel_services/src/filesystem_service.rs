#![no_std]

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use awkernel_async_lib::{
    channel::unbounded,
    file::{FileSystemReq, FileSystemRes, SeekFrom as KernelSeekFrom},
};
use awkernel_lib::{heap::TALLOC, paging::PAGESIZE};

use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
    fmt::Debug,
    future::Future,
    task::Poll,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read, Seek,
    SeekFrom as ExternalFatFsSeekFrom, Write,
};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB
pub async fn run() {
    let (tx, rx) = unbounded::new();

    awkernel_async_lib::file::add_filesystem(tx);
    let interface_id = 0;
    let Ok(layout) = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE) else {
        panic!("Invalid layout")
    };

    let result = unsafe { TALLOC.alloc(layout) };
    if result.is_null() {
        panic!("NULL pointer");
    }

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let mut disk = InMemoryDisk { data, position: 0 };

    let options = FormatVolumeOptions::new();
    if format_volume(&mut disk, options).is_err() {
        log::info!("Error formatting the disk");
    }
    let fs = FileSystem::new(disk, FsOptions::new());
    let Ok(fs) = fs else {
        panic!("Error creating file system");
    };

    let root_dir = fs.root_dir();

    let mut fd_to_file = BTreeMap::new();

    log::info!("fatfs service recv wait");
    loop {
        let req = rx.recv().await.unwrap(); // TODO

        log::info!("fatfs service wake");

        match req {
            FileSystemReq::Create { fd, path, tx } => {
                let file = root_dir.create_file(path.as_str()).unwrap(); //TODO
                tx.send(FileSystemRes::Success).await.unwrap(); // TODO
                fd_to_file.insert(fd, (file, tx));
            }
            FileSystemReq::Open { fd, path, tx } => {
                let file = root_dir.create_file(path.as_str()).unwrap(); //TODO
                tx.send(FileSystemRes::Success).await.unwrap(); // TODO
                fd_to_file.insert(fd, (file, tx));
            }
            FileSystemReq::Read { fd, bufsize } => {
                let Some((file, tx)) = fd_to_file.get_mut(&fd) else {
                    panic!("Read failed");
                };
            }
            FileSystemReq::Write { fd, buf } => {}
            FileSystemReq::Seek { fd, from } => {}
        }
    }
}

struct InMemoryDisk {
    data: Vec<u8>,
    position: u64,
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
        //log::info!("write InMemoryDisk");
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
    fn seek(&mut self, pos: ExternalFatFsSeekFrom) -> Result<u64, Self::Error> {
        let new_position = match pos {
            ExternalFatFsSeekFrom::Start(offset) => offset as i64,
            ExternalFatFsSeekFrom::Current(offset) => self.position as i64 + offset,
            ExternalFatFsSeekFrom::End(offset) => self.data.len() as i64 + offset,
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

#[derive(Debug)]
pub struct FatFsSeekFromWrapper(ExternalFatFsSeekFrom);

impl From<KernelSeekFrom> for FatFsSeekFromWrapper {
    fn from(item: KernelSeekFrom) -> Self {
        match item {
            KernelSeekFrom::Start(offset) => {
                FatFsSeekFromWrapper(ExternalFatFsSeekFrom::Start(offset))
            }
            KernelSeekFrom::End(offset) => FatFsSeekFromWrapper(ExternalFatFsSeekFrom::End(offset)),
            KernelSeekFrom::Current(offset) => {
                FatFsSeekFromWrapper(ExternalFatFsSeekFrom::Current(offset))
            }
        }
    }
}

impl From<FatFsSeekFromWrapper> for ExternalFatFsSeekFrom {
    fn from(item: FatFsSeekFromWrapper) -> Self {
        item.0
    }
}
