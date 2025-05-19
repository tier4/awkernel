#![no_std]

extern crate alloc;

use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec::Vec};
use awkernel_lib::{
    delay::wait_millisec,
    file::{
        fatfs::{FatFileSystemCmd, FatFileSystemResult, Fatfs},
        FileManagerError,
    },
    heap::TALLOC,
    paging::PAGESIZE,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
    future::Future,
    task::Poll,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read, Seek, SeekFrom, Write,
};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

pub async fn run() {
    let filesystem = Fatfs {};
    awkernel_lib::file::add_interface(Arc::new(filesystem));
    let interface_id = 0;
    //let Ok(layout) = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE) else {
    //panic!("Invalid layout")
    //};

    //let result = unsafe { TALLOC.alloc(layout) };
    //if result.is_null() {
    //panic!("NULL pointer");
    //}

    //let data =
    //unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    ////let mut disk = InMemoryDisk { data, position: 0 };
    let mut vecc = Vec::new();
    vecc.resize(MEMORY_FILESYSTEM_SIZE, 0);

    let mut disk = InMemoryDisk {
        data: vecc,
        position: 0,
    };
    let options = FormatVolumeOptions::new();
    if format_volume(&mut disk, options).is_ok() {
        log::info!("FAT filesystem formatted successfully in memory!");
    } else {
        log::info!("Error formatting!");
    }
    let fs = FileSystem::new(disk, FsOptions::new());
    let Ok(fs) = fs else {
        panic!("Error creating file system");
    };

    let root_dir = fs.root_dir();

    let mut fd_to_file = BTreeMap::new();
    loop {
        let _ = FileSystemPolling {
            // TODO: error handling?
            interface_id,
            wait: true,
        }
        .await;

        log::info!("fatfs service woke");

        wait_millisec(2000);

        loop {
            let cmdinfo = awkernel_lib::file::fatfs::cmd_queue_pop();
            let Some(cmdinfo) = cmdinfo else {
                break;
            };

            log::info!("cmdinfo.cmd {:?}", cmdinfo.cmd);

            match cmdinfo.cmd {
                FatFileSystemCmd::OpenCmd => {
                    log::info!("open cmd");
                    let ret;
                    match root_dir.create_file(cmdinfo.path.as_str()) {
                        Ok(file) => {
                            ret = Ok(FatFileSystemResult::Success);
                            fd_to_file.insert(cmdinfo.fd, file);
                        }
                        Err(e) => {
                            ret = Err(awkernel_lib::file::fatfs::FatFsError::OpenError);
                        }
                    };

                    log::info!("create_file called ret:{:?}", ret);
                    awkernel_lib::file::fatfs::complete_file_operation(
                        interface_id,
                        cmdinfo.fd,
                        ret,
                    );
                    log::info!("create_file called");
                }
                FatFileSystemCmd::CreateCmd => {}
                FatFileSystemCmd::ReadCmd => {}
                FatFileSystemCmd::WriteCmd => {}
                FatFileSystemCmd::SeekCmd => {}
            }
        }
    }
}

struct FileSystemPolling {
    interface_id: u64,
    wait: bool,
}

impl Future for FileSystemPolling {
    type Output = Result<(), FileManagerError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let m = self.get_mut();

        if !m.wait {
            return Poll::Ready(Ok(()));
        }

        m.wait = false;

        match awkernel_lib::file::register_waker_for_fs(m.interface_id, cx.waker().clone()) {
            Ok(true) => Poll::Pending,
            Ok(false) => Poll::Ready(Ok(())),
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

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
