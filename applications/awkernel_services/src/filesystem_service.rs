#![no_std]

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use awkernel_lib::{
    file::{
        fatfs::{
            complete_file_operation, FatFileSystemReq, FatFileSystemResult, FatFsError, Fatfs,
        },
        if_file::SeekFrom as KernelSeekFrom,
        FileManagerError,
    },
    heap::TALLOC,
    paging::PAGESIZE,
};

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
fn handle_file_operation<T, E: Debug>(
    interface_id: u64,
    fd: i64,
    result: Result<T, E>,
    success_mapper: impl FnOnce(T) -> FatFileSystemResult,
    error_kind: FatFsError,
) {
    let ret = match result {
        Ok(val) => Ok(success_mapper(val)),
        Err(e) => {
            log::info!("File operation error: {:?}", e);
            Err(error_kind)
        }
    };
    complete_file_operation(interface_id, fd, ret);
}

pub async fn run() {
    let filesystem = Fatfs {};
    awkernel_lib::file::add_interface(Arc::new(filesystem));
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
    loop {
        let _ = FileSystemPolling {
            // TODO: error handling?
            interface_id,
            wait: true,
        }
        .await;

        loop {
            let cmd = awkernel_lib::file::fatfs::cmd_queue_pop();
            let Some(cmd) = cmd else {
                break;
            };

            match cmd {
                FatFileSystemReq::Create { fd, path } => {
                    let result = root_dir.create_file(path.as_str()).map(|file| {
                        fd_to_file.insert(fd, file);
                    });
                    handle_file_operation(
                        interface_id,
                        fd,
                        result,
                        |_| FatFileSystemResult::Success,
                        FatFsError::CreateError,
                    );
                }
                FatFileSystemReq::Open { fd, path } => {
                    let result = root_dir.open_file(path.as_str()).map(|file| {
                        fd_to_file.insert(fd, file);
                    });
                    handle_file_operation(
                        interface_id,
                        fd,
                        result,
                        |_| FatFileSystemResult::Success,
                        FatFsError::OpenError,
                    );
                }
                FatFileSystemReq::Read { fd, bufsize } => {
                    if let Some(file) = fd_to_file.get_mut(&fd) {
                        let mut buf = Vec::new();
                        buf.resize(bufsize, 0);
                        let result = file.read(&mut buf).map(|_| buf);
                        handle_file_operation(
                            interface_id,
                            fd,
                            result,
                            FatFileSystemResult::ReadResult,
                            FatFsError::ReadError,
                        );
                    } else {
                        complete_file_operation(interface_id, fd, Err(FatFsError::InvalidFd));
                    }
                }
                FatFileSystemReq::Write { fd, buf } => {
                    if let Some(file) = fd_to_file.get_mut(&fd) {
                        let result = file.write(&buf);
                        handle_file_operation(
                            interface_id,
                            fd,
                            result,
                            FatFileSystemResult::WriteBytes,
                            FatFsError::WriteError,
                        );
                    } else {
                        complete_file_operation(interface_id, fd, Err(FatFsError::InvalidFd));
                    }
                }
                FatFileSystemReq::Seek { fd, from } => {
                    if let Some(file) = fd_to_file.get_mut(&fd) {
                        let fatfs_seek_from: ExternalFatFsSeekFrom =
                            FatFsSeekFromWrapper::from(from).into();
                        let result = file.seek(fatfs_seek_from).map(|s_bytes| s_bytes as usize);
                        handle_file_operation(
                            interface_id,
                            fd,
                            result,
                            FatFileSystemResult::SeekBytes,
                            FatFsError::SeekError,
                        );
                    } else {
                        complete_file_operation(interface_id, fd, Err(FatFsError::InvalidFd));
                    }
                }
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
