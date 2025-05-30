extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    file::{FileSystemError, FileSystemReq, FileSystemRes, SeekFrom as KernelSeekFrom},
};
use awkernel_lib::{heap::TALLOC, paging::PAGESIZE};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt::{self, Debug},
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

    let layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
        .expect("Invalid layout for memory filesystem");
    let result = unsafe { TALLOC.alloc(layout) };
    assert!(
        !result.is_null(),
        "NULL pointer allocated for memory filesystem"
    );

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let mut disk = InMemoryDisk { data, position: 0 };

    if format_volume(&mut disk, FormatVolumeOptions::new()).is_err() {
        log::info!("Error formatting the disk");
    }

    let fs = FileSystem::new(disk, FsOptions::new()).expect("Error creating file system");
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
                tx: client_tx,
            } => match root_dir.create_file(path.as_str()) {
                Ok(file) => {
                    send_response(fd, &client_tx, Ok(FileSystemRes::Success), "[Create]").await;
                    fd_to_file.insert(fd, (file, client_tx));
                }
                Err(fatfs_err) => {
                    let fs_error = map_fatfs_error(fatfs_err);
                    send_response(fd, &client_tx, Err(fs_error), "[Create]").await;
                }
            },
            FileSystemReq::Open {
                fd,
                path,
                tx: client_tx,
            } => match root_dir.open_file(path.as_str()) {
                Ok(file) => {
                    send_response(fd, &client_tx, Ok(FileSystemRes::Success), "[Open]").await;
                    fd_to_file.insert(fd, (file, client_tx));
                }
                Err(fatfs_err) => {
                    let fs_error = map_fatfs_error(fatfs_err);
                    send_response(fd, &client_tx, Err(fs_error), "[Open]").await;
                }
            },
            FileSystemReq::Read { fd, bufsize } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let mut buf = Vec::new();
                    buf.resize(bufsize, 0);
                    let res = file
                        .read(&mut buf)
                        .map(|bytes_read| {
                            buf.truncate(bytes_read);
                            FileSystemRes::ReadResult(buf)
                        })
                        .map_err(|fatfs_err| {
                            log::error!("[Read] Error reading from fd {}: {:?}", fd, fatfs_err);
                            map_fatfs_error(fatfs_err)
                        });
                    send_response(fd, client_tx, res, "[Read]").await;
                } else {
                    panic!("Read failed: File descriptor {} not found", fd);
                }
            }
            FileSystemReq::Write { fd, buf } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let res =
                        file.write(&buf)
                            .map(FileSystemRes::WriteBytes)
                            .map_err(|fatfs_err| {
                                log::error!("[Write] Error writing to fd {}: {:?}", fd, fatfs_err);
                                map_fatfs_error(fatfs_err)
                            });
                    send_response(fd, client_tx, res, "[Write]").await;
                } else {
                    panic!("Write failed: File descriptor {} not found", fd);
                }
            }
            FileSystemReq::Seek { fd, from } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let fatfs_seek_from: ExternalFatFsSeekFrom =
                        FatFsSeekFromWrapper::from(from).into();
                    let res = file
                        .seek(fatfs_seek_from)
                        .map(FileSystemRes::SeekBytes)
                        .map_err(|fatfs_err| {
                            log::error!("[Seek] Error seeking in fd {}: {:?}", fd, fatfs_err);
                            map_fatfs_error(fatfs_err)
                        });
                    send_response(fd, client_tx, res, "[Seek]").await;
                } else {
                    panic!("Seek failed: File descriptor {} not found", fd);
                }
            }
            FileSystemReq::Close { fd } => {
                if let Some((_file, client_tx)) = fd_to_file.remove(&fd) {
                    let _ = client_tx.send(Ok(FileSystemRes::Success)).await;
                } else {
                    panic!("Close failed: File descriptor {} not found", fd);
                }
            }
        }
    }
}

async fn send_response(
    fd: i64,
    client_tx: &awkernel_async_lib::channel::bounded::Sender<
        Result<FileSystemRes, FileSystemError>,
    >,
    res: Result<FileSystemRes, FileSystemError>,
    operation_name: &str,
) {
    if let Err(e) = client_tx.send(res).await {
        panic!(
            "{}] Failed to send response to client for fd {}: {:?}",
            operation_name, fd, e
        );
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
        matches!(self, InMemoryDiskError::_Interrupted)
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
