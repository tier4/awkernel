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
        error::Error,
        fatfs::{
            file::File,
            fs::{FileSystem, OemCpConverter, ReadWriteSeek},
            time::{Date, DateTime, TimeProvider},
        },
        io::{Read, Seek, SeekFrom, Write},
        vfs::{
            error::{VfsError, VfsResult},
            path::{VfsFileType, VfsMetadata},
        },
    },
    sync::{mcs::MCSNode, mutex::Mutex},
    time::Time,
};
use core::{fmt, task::Poll};
use futures::stream::{self, BoxStream};

pub struct AsyncFatFs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    fs: Arc<FileSystem<IO, TP, OCC>>,
}

impl<IO, TP, OCC> AsyncFatFs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    pub fn new(fs: FileSystem<IO, TP, OCC>) -> Self {
        Self { fs: Arc::new(fs) }
    }
}

struct AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    file: Mutex<File<IO, TP, OCC>>,
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndRead<Error<IO::Error>> for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + 'static,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize, VfsError<Error<IO::Error>>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            let result = (*file_guard).read(buf).map_err(VfsError::from);
            Poll::Ready(result)
        })
        .await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError<Error<IO::Error>>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            let result = (*file_guard).seek(pos).map_err(VfsError::from);
            Poll::Ready(result)
        })
        .await
    }
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndWrite<Error<IO::Error>> for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + 'static,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    async fn write(&mut self, buf: &[u8]) -> Result<usize, VfsError<Error<IO::Error>>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready((*file_guard).write(buf).map_err(VfsError::from))
        })
        .await
    }

    async fn write_all(&mut self, buf: &[u8]) -> Result<(), VfsError<Error<IO::Error>>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready((*file_guard).write_all(buf).map_err(VfsError::from))
        })
        .await
    }

    async fn flush(&mut self) -> Result<(), VfsError<Error<IO::Error>>> {
        core::future::poll_fn(|_cx| {
            let mut node = MCSNode::new();
            let mut file_guard = self.file.lock(&mut node);
            Poll::Ready((*file_guard).flush().map_err(VfsError::from))
        })
        .await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError<Error<IO::Error>>> {
        <Self as AsyncSeekAndRead<Error<IO::Error>>>::seek(self, pos).await
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
    type Error = Error<IO::Error>;

    async fn read_dir(&self, path: &str) -> VfsResult<BoxStream<'static, String>, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();

        core::future::poll_fn(move |_cx| {
            let dir = FileSystem::root_dir(&fs_clone).open_dir(&path)?;
            let entries: Result<Vec<String>, _> = dir
                .iter()
                .map(|entry_res| Ok(entry_res?.file_name()))
                .collect();
            Poll::Ready(
                entries.map(|names| Box::pin(stream::iter(names)) as BoxStream<'static, String>),
            )
        })
        .await
    }

    async fn create_dir(&self, path: &str) -> VfsResult<(), Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        core::future::poll_fn(move |_cx| {
            Poll::Ready(FileSystem::root_dir(&fs_clone).create_dir(&path))
        })
        .await?;
        Ok(())
    }

    async fn open_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndRead<Self::Error> + Send>, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();

        let file = core::future::poll_fn(move |_cx| {
            Poll::Ready(FileSystem::root_dir(&fs_clone).open_file(&path))
        })
        .await?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn create_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::Error> + Send>, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        let file = core::future::poll_fn(move |_cx| {
            Poll::Ready(FileSystem::root_dir(&fs_clone).create_file(&path))
        })
        .await?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn append_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::Error> + Send>, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        let file = core::future::poll_fn(move |_cx| {
            let result: Result<File<IO, TP, OCC>, Error<IO::Error>> = (|| {
                let mut file = FileSystem::root_dir(&fs_clone).open_file(&path)?;
                file.seek(SeekFrom::End(0))?;
                Ok(file)
            })();
            Poll::Ready(result)
        })
        .await?;

        Ok(Box::new(AsyncFile {
            file: Mutex::new(file),
        }))
    }

    async fn metadata(&self, path: &str) -> VfsResult<VfsMetadata, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        core::future::poll_fn(move |_cx| {
            let entry = FileSystem::root_dir(&fs_clone).find_entry(&path, None, None)?;
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
            Poll::Ready(Ok(metadata))
        })
        .await
    }

    async fn exists(&self, path: &str) -> VfsResult<bool, Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        core::future::poll_fn(move |_cx| {
            Poll::Ready(Ok(FileSystem::root_dir(&fs_clone)
                .find_entry(&path, None, None)
                .is_ok()))
        })
        .await
    }

    async fn remove_file(&self, path: &str) -> VfsResult<(), Self::Error> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        core::future::poll_fn(move |_cx| {
            Poll::Ready(FileSystem::root_dir(&fs_clone).remove(&path))
        })
        .await?;
        Ok(())
    }

    async fn remove_dir(&self, path: &str) -> VfsResult<(), Self::Error> {
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
