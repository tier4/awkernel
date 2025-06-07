extern crate alloc;

use alloc::{collections::BTreeMap, vec, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    file::{FileSystemError, FileSystemReq, FileSystemRes, SeekFrom as KernelSeekFrom},
};
use awkernel_lib::{allocator::System, file::memfs::InMemoryDisk, paging::PAGESIZE};

use core::{
    alloc::{GlobalAlloc, Layout},
    fmt::Debug,
};
use fatfs::{
    format_volume, Error as FatFsError, FileSystem, FormatVolumeOptions, FsOptions, Read, Seek,
    SeekFrom as ExternalFatFsSeekFrom, Write,
};

fn map_fatfs_error<E: Debug>(fatfs_err: FatFsError<E>) -> FileSystemError {
    log::error!("fatfs error: {fatfs_err:?}");
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

    let result = {
        let layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
            .expect("Invalid layout for memory filesystem");
        unsafe { System.alloc(layout) }
    };

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let mut disk = InMemoryDisk::new(data, 0);

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
                log::error!("Failed to receive from service_rx: {e:?}. Shutting down service.");
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
                    let mut buf = vec![0; bufsize];
                    let res = file
                        .read(&mut buf)
                        .map(|bytes_read| {
                            buf.truncate(bytes_read);
                            FileSystemRes::ReadResult(buf)
                        })
                        .map_err(|fatfs_err| {
                            log::error!("[Read] Error reading from fd {fd}: {fatfs_err:?}");
                            map_fatfs_error(fatfs_err)
                        });
                    send_response(fd, client_tx, res, "[Read]").await;
                } else {
                    unreachable!();
                }
            }
            FileSystemReq::Write { fd, buf } => {
                if let Some((file, client_tx)) = fd_to_file.get_mut(&fd) {
                    let res =
                        file.write(&buf)
                            .map(FileSystemRes::WriteBytes)
                            .map_err(|fatfs_err| {
                                log::error!("[Write] Error writing to fd {fd}: {fatfs_err:?}");
                                map_fatfs_error(fatfs_err)
                            });
                    send_response(fd, client_tx, res, "[Write]").await;
                } else {
                    unreachable!();
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
                            log::error!("[Seek] Error seeking in fd {fd}: {fatfs_err:?}");
                            map_fatfs_error(fatfs_err)
                        });
                    send_response(fd, client_tx, res, "[Seek]").await;
                } else {
                    unreachable!();
                }
            }
            FileSystemReq::Close { fd } => {
                if let Some((_file, client_tx)) = fd_to_file.remove(&fd) {
                    let _ = client_tx.send(Ok(FileSystemRes::Success)).await;
                } else {
                    unreachable!();
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
            "[{}] Failed to send response to client for fd {}: {:?}",
            operation_name, fd, e
        );
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
