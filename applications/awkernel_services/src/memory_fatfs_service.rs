extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    file::{FileSystemError, FileSystemReq, FileSystemRes},
};
use awkernel_lib::{
    allocator::System,
    file::{
        error::Error as FatFsError,
        fatfs::{
            dir::Dir,
            file::File,
            fs::{format_volume, FileSystem, FormatVolumeOptions, FsOptions, LossyOemCpConverter},
            time::NullTimeProvider,
        },
        io::{Read, Seek, Write},
        memfs::InMemoryDisk,
    },
    paging::PAGESIZE,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt::Debug,
};
type ResponseSender =
    awkernel_async_lib::channel::bounded::Sender<Result<FileSystemRes, FileSystemError>>;
type FatFile<'a> = File<'a, InMemoryDisk, NullTimeProvider, LossyOemCpConverter>;
type FatDir<'a> = Dir<'a, InMemoryDisk, NullTimeProvider, LossyOemCpConverter>;
type FileDescriptorMap<'a> = BTreeMap<i64, (FatFile<'a>, ResponseSender)>;

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

// TODO: Later implement TimeProvider. NullTimeProvider is a dummy provider that slways returns DOS minimal date-time (1980-01-01 00:00:00).
struct MemoryFileSystemServer<'a> {
    root_dir: FatDir<'a>,
    fd_to_file: FileDescriptorMap<'a>,
}

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

    let mut server = MemoryFileSystemServer {
        root_dir: fs.root_dir(),
        fd_to_file: BTreeMap::new(),
    };

    loop {
        let req = match rx.recv().await {
            Ok(r) => r,
            Err(e) => {
                log::error!("Failed to receive from service_rx: {e:?}. Shutting down service.");
                break;
            }
        };
        server.handle_request(req).await;
    }
}

impl<'a> MemoryFileSystemServer<'a> {
    async fn handle_request(&mut self, req: FileSystemReq) {
        match req {
            FileSystemReq::Create { fd, path, tx } => self.handle_create(fd, path, tx).await,
            FileSystemReq::Open { fd, path, tx } => self.handle_open(fd, path, tx).await,
            FileSystemReq::Read { fd, bufsize } => self.handle_read(fd, bufsize).await,
            FileSystemReq::Write { fd, buf } => self.handle_write(fd, buf).await,
            FileSystemReq::Seek { fd, from } => self.handle_seek(fd, from).await,
            FileSystemReq::Close { fd } => self.handle_close(fd).await,
        }
    }

    async fn handle_create(
        &mut self,
        fd: i64,
        path: String,
        client_tx: awkernel_async_lib::channel::bounded::Sender<
            Result<FileSystemRes, FileSystemError>,
        >,
    ) {
        let (res, file_to_insert) = match self.root_dir.create_file(path.as_str()) {
            Ok(file) => (Ok(FileSystemRes::Success), Some(file)),
            Err(e) => (Err(map_fatfs_error(e)), None),
        };

        if send_response(fd, &client_tx, res, "[Create]")
            .await
            .is_err()
        {
            log::warn!("Client for fd {fd} disconnected. Not adding to map.");
            return;
        }

        if let Some(file) = file_to_insert {
            self.fd_to_file.insert(fd, (file, client_tx));
        }
    }

    async fn handle_open(
        &mut self,
        fd: i64,
        path: String,
        client_tx: awkernel_async_lib::channel::bounded::Sender<
            Result<FileSystemRes, FileSystemError>,
        >,
    ) {
        let (res, file_to_insert) = match self.root_dir.open_file(path.as_str()) {
            Ok(file) => (Ok(FileSystemRes::Success), Some(file)),
            Err(e) => (Err(map_fatfs_error(e)), None),
        };

        if send_response(fd, &client_tx, res, "[Open]").await.is_err() {
            log::warn!("Client for fd {fd} disconnected. Not adding to map.");
            return;
        }

        if let Some(file) = file_to_insert {
            self.fd_to_file.insert(fd, (file, client_tx));
        }
    }

    async fn handle_read(&mut self, fd: i64, bufsize: usize) {
        if let Some((file, client_tx)) = self.fd_to_file.get_mut(&fd) {
            let mut buf = vec![0; bufsize];
            let res = file
                .read(&mut buf)
                .map(|bytes_read| {
                    buf.truncate(bytes_read);
                    FileSystemRes::ReadResult(buf)
                })
                .map_err(map_fatfs_error);

            if send_response(fd, client_tx, res, "[Read]").await.is_err() {
                log::warn!("Client for fd {fd} disconnected. Cleaning up.");
                self.fd_to_file.remove(&fd);
            }
        } else {
            unreachable!();
        }
    }

    async fn handle_write(&mut self, fd: i64, buf: Vec<u8>) {
        if let Some((file, client_tx)) = self.fd_to_file.get_mut(&fd) {
            let res = file
                .write(&buf)
                .map(FileSystemRes::WriteBytes)
                .map_err(map_fatfs_error);

            if send_response(fd, client_tx, res, "[Write]").await.is_err() {
                log::warn!("Client for fd {fd} disconnected. Cleaning up.");
                self.fd_to_file.remove(&fd);
            }
        } else {
            unreachable!();
        }
    }

    async fn handle_seek(&mut self, fd: i64, from: awkernel_lib::file::io::SeekFrom) {
        if let Some((file, client_tx)) = self.fd_to_file.get_mut(&fd) {
            let res = file
                .seek(from)
                .map(FileSystemRes::SeekBytes)
                .map_err(map_fatfs_error);

            if send_response(fd, client_tx, res, "[Seek]").await.is_err() {
                log::warn!("Client for fd {fd} disconnected. Cleaning up.");
                self.fd_to_file.remove(&fd);
            }
        } else {
            unreachable!();
        }
    }

    async fn handle_close(&mut self, fd: i64) {
        if let Some((_file, client_tx)) = self.fd_to_file.remove(&fd) {
            let _ = send_response(fd, &client_tx, Ok(FileSystemRes::Success), "[Close]").await;
        } else {
            unreachable!();
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
) -> Result<(), ()> {
    if let Err(e) = client_tx.send(res).await {
        log::error!("{operation_name} Failed to send response to client for fd {fd}: {e:?}");
        Err(())
    } else {
        Ok(())
    }
}

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
