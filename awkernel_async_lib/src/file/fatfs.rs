use super::filesystem::{AsyncFileSystem, AsyncSeekAndRead, AsyncSeekAndWrite};
use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use async_trait::async_trait;
use awkernel_lib::{
    file::{
        fatfs::{
            error::Error,
            file::File,
            fs::{FileSystem, LossyOemCpConverter, OemCpConverter, ReadWriteSeek},
            get_memory_fatfs,
            time::{Date, DateTime, NullTimeProvider, TimeProvider},
        },
        io::{Read, Seek, SeekFrom, Write},
        memfs::InMemoryDisk,
        vfs::{
            error::{VfsError, VfsErrorKind, VfsResult},
            path::{VfsFileType, VfsMetadata},
        },
    },
    sync::{mcs::MCSNode, mutex::Mutex},
    time::Time,
};
use core::{fmt, task::Poll};
use futures::stream::{self, Stream};

struct AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    file: Mutex<File<IO, TP, OCC>>,
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndRead<IO::Error> for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + 'static,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize, VfsError<IO::Error>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            let result = (*file_guard)
                .read(buf)
                .map_err(|e| VfsError::from(VfsErrorKind::from(e)));
            Poll::Ready(result)
        })
        .await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError<IO::Error>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            let result = (*file_guard)
                .seek(pos)
                .map_err(|e| VfsError::from(VfsErrorKind::from(e)));
            Poll::Ready(result)
        })
        .await
    }
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndWrite<IO::Error> for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + 'static,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    async fn write(&mut self, buf: &[u8]) -> Result<usize, VfsError<IO::Error>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready(
                (*file_guard)
                    .write(buf)
                    .map_err(|e| VfsError::from(VfsErrorKind::from(e))),
            )
        })
        .await
    }

    async fn write_all(&mut self, buf: &[u8]) -> Result<(), VfsError<IO::Error>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready(
                (*file_guard)
                    .write_all(buf)
                    .map_err(|e| VfsError::from(VfsErrorKind::from(e))),
            )
        })
        .await
    }

    async fn flush(&mut self) -> Result<(), VfsError<IO::Error>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready(
                (*file_guard)
                    .flush()
                    .map_err(|e| VfsError::from(VfsErrorKind::from(e))),
            )
        })
        .await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError<IO::Error>> {
        <Self as AsyncSeekAndRead<IO::Error>>::seek(self, pos).await
    }
}

pub struct AsyncFatFs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    fs: Arc<FileSystem<IO, TP, OCC>>,
}

impl AsyncFatFs<InMemoryDisk, NullTimeProvider, LossyOemCpConverter> {
    pub fn new_in_memory() -> Self {
        Self {
            fs: get_memory_fatfs(),
        }
    }
}

#[async_trait]
impl<IO, TP, OCC> AsyncFileSystem for AsyncFatFs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + 'static,
    IO::Error: fmt::Debug + Send + Sync + Clone,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    type IOError = IO::Error;

    async fn read_dir(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn Unpin + Stream<Item = String> + Send>, Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();

        let dir = FileSystem::root_dir(&fs_clone)
            .open_dir(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;
        let entries: Result<Vec<String>, _> = dir
            .iter()
            .map(|entry_res| {
                entry_res
                    .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
                    .and_then(|entry| Ok(entry.file_name()))
            })
            .collect();
        entries.map(|names| {
            Box::new(stream::iter(names)) as Box<dyn Unpin + Stream<Item = String> + Send>
        })
    }

    async fn create_dir(&self, path: &str) -> VfsResult<(), Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        FileSystem::root_dir(&fs_clone)
            .create_dir(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;
        Ok(())
    }

    async fn open_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndRead<Self::IOError> + Send + Unpin>, Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();

        let file = FileSystem::root_dir(&fs_clone)
            .open_file(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn create_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::IOError> + Send + Unpin>, Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        let file = FileSystem::root_dir(&fs_clone)
            .create_file(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn append_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::IOError> + Send + Unpin>, Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        let file = {
            let result: Result<File<IO, TP, OCC>, Error<IO::Error>> = (|| {
                let mut file = FileSystem::root_dir(&fs_clone).open_file(&path)?;
                file.seek(SeekFrom::End(0))?;
                Ok(file)
            })();
            result
        }
        .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn metadata(&self, path: &str) -> VfsResult<VfsMetadata, Self::IOError> {
        if path.is_empty() {
            return Ok(VfsMetadata {
                file_type: VfsFileType::Directory,
                len: 0,
                created: None,
                modified: None,
                accessed: None,
            });
        }
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        let entry = FileSystem::root_dir(&fs_clone)
            .find_entry(&path, None, None)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;
        let metadata = VfsMetadata {
            file_type: if entry.is_dir() {
                VfsFileType::Directory
            } else {
                VfsFileType::File
            },
            len: entry.len(),
            created: to_vfs_datetime(entry.created()),
            modified: to_vfs_datetime(entry.modified()),
            accessed: to_vfs_date(entry.accessed()),
        };
        Ok(metadata)
    }

    async fn exists(&self, path: &str) -> VfsResult<bool, Self::IOError> {
        if path.is_empty() {
            return Ok(true);
        }
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        Ok(FileSystem::root_dir(&fs_clone)
            .find_entry(&path, None, None)
            .is_ok())
    }

    async fn remove_file(&self, path: &str) -> VfsResult<(), Self::IOError> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        FileSystem::root_dir(&fs_clone)
            .remove(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;

        Ok(())
    }

    async fn remove_dir(&self, path: &str) -> VfsResult<(), Self::IOError> {
        self.remove_file(path).await
    }
}

fn to_vfs_datetime(_date_time: DateTime) -> Option<Time> {
    // This conversion might be lossy or incorrect depending on the Time struct definition.
    // Assuming Time can be created from a unix timestamp.
    // fatfs DateTime doesn't directly provide a unix timestamp.
    // This part needs a proper implementation based on your Time struct.
    // For now, returning None.
    todo!()
}

fn to_vfs_date(_date: Date) -> Option<Time> {
    // TODO - Define the conversion between DateTime/Date in fatfs/time.rs
    None
}
