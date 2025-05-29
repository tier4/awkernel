extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    file::{FileSystemError, FileSystemReq, FileSystemRes, SeekFrom as KernelSeekFrom},
};
use awkernel_lib::{heap::TALLOC, paging::PAGESIZE};

use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
    fmt::Debug,
};
use fatfs::{
    format_volume, Error as FatFsError, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read,
    Seek, SeekFrom as ExternalFatFsSeekFrom, Write,
};

fn map_fatfs_error<E: Debug>(fatfs_err: FatFsError<E>) -> FileSystemError {
    log::error!("fatfs error: {:?}", fatfs_err);
    match fatfs_err {
        FatFsError::NotFound => FileSystemError::NotFound,
        FatFsError::AlreadyExists => FileSystemError::AlreadyExists,
        FatFsError::InvalidInput => FileSystemError::InvalidInput,
        FatFsError::NotEnoughSpace => FileSystemError::NotEnoughSpace,
        FatFsError::CorruptedFileSystem => FileSystemError::CorruptedFileSystem,
        FatFsError::Io(_) => FileSystemError::IoError,
        FatFsError::UnexpectedEof => FileSystemError::UnexpectedEof,
        FatFsError::WriteZero => FileSystemError::WriteZero,
        FatFsError::InvalidFileNameLength => FileSystemError::InvalidFileNameLength,
        FatFsError::UnsupportedFileNameCharacter => FileSystemError::UnsupportedFileNameCharacter,
        FatFsError::DirectoryIsNotEmpty => FileSystemError::DirectoryIsNotEmpty,
        _ => FileSystemError::UnknownError,
    }
}

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB
pub async fn run() {
    let (tx, rx) = bounded::new(Default::default());

    awkernel_async_lib::file::add_filesystem(tx);
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
        let req = match rx.recv().await {
            Ok(r) => r,
            Err(e) => {
                log::error!(
                    "Failed to receive from service_rx: {:?}. Shutting down service.",
                    e
                );
                break;
            }
        };

        match req {
            FileSystemReq::Create {
                fd,
                path,
                tx: tx_fd,
            } => match root_dir.create_file(path.as_str()) {
                Ok(file) => {
                    if let Err(e) = tx_fd.send(Ok(FileSystemRes::Success)).await {
                        panic!(
                            "[Create] Failed to send response to client for fd {}: {:?}",
                            fd, e
                        )
                    }
                    fd_to_file.insert(fd, (file, tx_fd));
                }
                Err(fatfs_err) => {
                    let fs_error = map_fatfs_error(fatfs_err);
                    if let Err(e) = tx_fd.send(Err(fs_error)).await {
                        panic!(
                            "[Create] Failed to send response to client for fd {}: {:?}",
                            fd, e
                        )
                    }
                }
            },
            FileSystemReq::Open {
                fd,
                path,
                tx: tx_fd,
            } => match root_dir.create_file(path.as_str()) {
                Ok(file) => {
                    if let Err(e) = tx_fd.send(Ok(FileSystemRes::Success)).await {
                        panic!(
                            "[Create] Failed to send response to client for fd {}: {:?}",
                            fd, e
                        )
                    }
                    fd_to_file.insert(fd, (file, tx_fd));
                }
                Err(fatfs_err) => {
                    let fs_error = map_fatfs_error(fatfs_err);
                    if let Err(e) = tx_fd.send(Err(fs_error)).await {
                        panic!(
                            "[Create] Failed to send response to client for fd {}: {:?}",
                            fd, e
                        )
                    }
                }
            },
            FileSystemReq::Read { fd, bufsize } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let mut buf = Vec::new();
                    buf.resize(bufsize, 0);
                    match file.read(&mut buf) {
                        Ok(bytes_read) => {
                            buf.truncate(bytes_read);
                            if let Err(e) = client_tx.send(Ok(FileSystemRes::ReadResult(buf))).await
                            {
                                log::error!(
                                    "[Read] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                        Err(fatfs_err) => {
                            log::error!("[Read] Error reading from fd {}: {:?}", fd, fatfs_err);
                            let fs_error = map_fatfs_error(fatfs_err);
                            if let Err(e) = client_tx.send(Err(fs_error)).await {
                                log::error!(
                                    "[Read] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                    }
                } else {
                    panic!("Read failed");
                };
            }
            FileSystemReq::Write { fd, buf } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    match file.write(&buf) {
                        Ok(w_bytes) => {
                            if let Err(e) =
                                client_tx.send(Ok(FileSystemRes::WriteBytes(w_bytes))).await
                            {
                                log::error!(
                                    "[Write] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                        Err(fatfs_err) => {
                            log::error!("[Write] Error writing to fd {}: {:?}", fd, fatfs_err);
                            let fs_error = map_fatfs_error(fatfs_err);
                            if let Err(e) = client_tx.send(Err(fs_error)).await {
                                log::error!(
                                    "[Write] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                    }
                } else {
                    panic!("Write failed");
                };
            }
            FileSystemReq::Seek { fd, from } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let fatfs_seek_from: ExternalFatFsSeekFrom =
                        FatFsSeekFromWrapper::from(from).into();
                    match file.seek(fatfs_seek_from) {
                        Ok(s_bytes) => {
                            if let Err(e) =
                                client_tx.send(Ok(FileSystemRes::SeekBytes(s_bytes))).await
                            {
                                log::error!(
                                    "[Seek] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                        Err(fatfs_err) => {
                            log::error!("[Seek] Error seeking in fd {}: {:?}", fd, fatfs_err);
                            let fs_error = map_fatfs_error(fatfs_err);
                            if let Err(e) = client_tx.send(Err(fs_error)).await {
                                log::error!(
                                    "[Seek] Failed to send response to client for fd {}: {:?}",
                                    fd,
                                    e
                                );
                            }
                        }
                    }
                } else {
                    panic!("Seek failed");
                };
            }
            FileSystemReq::Close { fd } => {
                if let Some((_file, tx_fd)) = fd_to_file.remove(&fd) {
                    let _ = tx_fd.send(Ok(FileSystemRes::Success)).await;
                } else {
                    panic!("Close failed");
                };
            }
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
    _Interrupted,
    _Other(String),
}

impl fmt::Display for InMemoryDiskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InMemoryDiskError::OutOfBounds => write!(f, "Out of bounds access"),
            InMemoryDiskError::WriteZero => write!(f, "Failed to write whole buffer"),
            InMemoryDiskError::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            InMemoryDiskError::_Interrupted => write!(f, "Operation interrupted"),
            InMemoryDiskError::_Other(msg) => write!(f, "An error occurred: {}", msg),
        }
    }
}

impl fatfs::IoError for InMemoryDiskError {
    fn is_interrupted(&self) -> bool {
        match self {
            InMemoryDiskError::_Interrupted => true,
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
