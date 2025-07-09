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
            error::{VfsError, VfsErrorKind, VfsIoError, VfsResult},
            path::{VfsFileType, VfsMetadata},
        },
    },
    sync::{mcs::MCSNode, mutex::Mutex},
    time::Time,
};
use core::fmt::Debug;
use futures::stream::{self, Stream};

struct AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + Sync,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    file: Mutex<File<IO, TP, OCC>>,
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndRead for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + Debug,
    IO::Error: Into<VfsIoError>,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize, VfsError> {
        let mut node = MCSNode::new();
        let mut file_guard = self.file.lock(&mut node);
        (*file_guard)
            .read(buf)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError> {
        let mut node = MCSNode::new();
        let mut file_guard = self.file.lock(&mut node);
        (*file_guard)
            .seek(pos)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }
}

#[async_trait]
impl<IO, TP, OCC> AsyncSeekAndWrite for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + Sync,
    IO::Error: Into<VfsIoError>,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    async fn write(&mut self, buf: &[u8]) -> Result<usize, VfsError> {
        let mut node = MCSNode::new();
        let mut file_guard = self.file.lock(&mut node);
        (*file_guard)
            .write(buf)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    async fn write_all(&mut self, buf: &[u8]) -> Result<(), VfsError> {
        let mut node = MCSNode::new();
        let mut file_guard = self.file.lock(&mut node);
        (*file_guard)
            .write_all(buf)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    async fn flush(&mut self) -> Result<(), VfsError> {
        let mut node = MCSNode::new();
        let mut file_guard = self.file.lock(&mut node);
        (*file_guard)
            .flush()
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError> {
        <Self as AsyncSeekAndRead>::seek(self, pos).await
    }
}

#[derive(Debug)]
pub struct AsyncFatFs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Sync + Debug,
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
    IO: ReadWriteSeek + Send + Sync + Debug + 'static,
    IO::Error: Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    async fn read_dir(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn Unpin + Stream<Item = String> + Send>> {
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
                    .map(|entry| entry.file_name())
            })
            .collect();
        entries.map(|names| {
            Box::new(stream::iter(names)) as Box<dyn Unpin + Stream<Item = String> + Send>
        })
    }

    async fn create_dir(&self, path: &str) -> VfsResult<()> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        FileSystem::root_dir(&fs_clone)
            .create_dir(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;
        Ok(())
    }

    async fn open_file(&self, path: &str) -> VfsResult<Box<dyn AsyncSeekAndRead + Send + Unpin>> {
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
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
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
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
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

    async fn metadata(&self, path: &str) -> VfsResult<VfsMetadata> {
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

    async fn exists(&self, path: &str) -> VfsResult<bool> {
        if path.is_empty() {
            return Ok(true);
        }
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        Ok(FileSystem::root_dir(&fs_clone)
            .find_entry(&path, None, None)
            .is_ok())
    }

    async fn remove_file(&self, path: &str) -> VfsResult<()> {
        let path = path.to_string();
        let fs_clone = self.fs.clone();
        FileSystem::root_dir(&fs_clone)
            .remove(&path)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))?;

        Ok(())
    }

    async fn remove_dir(&self, path: &str) -> VfsResult<()> {
        self.remove_file(path).await
    }
}

fn to_vfs_datetime(_date_time: DateTime) -> Option<Time> {
    // TODO - Currently, we use NullTimeProvider which does not provide actual time.
    // Once we implement a proper time provider, we can convert DateTime to Time.
    // For now, we return None to indicate that the conversion is not implemented.
    // This is a placeholder for the actual implementation.
    todo!()
}

fn to_vfs_date(_date: Date) -> Option<Time> {
    // TODO - Currently, we use NullTimeProvider which does not provide actual time.
    // Once we implement a proper time provider, we can convert DateTime to Time.
    // For now, we return None to indicate that the conversion is not implemented.
    // This is a placeholder for the actual implementation.
    None
}
