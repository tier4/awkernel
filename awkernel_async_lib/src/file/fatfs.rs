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
            time::{AwkernelTimeProvider, Date, DateTime, TimeProvider},
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
use core::{fmt::Debug, task::Poll};
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

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64, VfsError> {
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
impl<IO, TP, OCC> AsyncSeekAndWrite for AsyncFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + Sync,
    IO::Error: Into<VfsIoError>,
    TP: TimeProvider + Send + Sync,
    OCC: OemCpConverter + Send + Sync,
{
    async fn write(&mut self, buf: &[u8]) -> Result<usize, VfsError> {
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

    async fn write_all(&mut self, buf: &[u8]) -> Result<(), VfsError> {
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

    async fn flush(&mut self) -> Result<(), VfsError> {
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

impl AsyncFatFs<InMemoryDisk, AwkernelTimeProvider, LossyOemCpConverter> {
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

fn to_vfs_datetime(date_time: DateTime) -> Option<Time> {
    // Calculate the number of nanoseconds since the AWKernel base epoch (2024-01-01)
    // First, calculate days since base epoch
    let mut total_days: u32 = 0;
    
    // Add days for complete years
    for year in 2024..date_time.date.year {
        if (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0) {
            total_days += 366; // Leap year
        } else {
            total_days += 365;
        }
    }
    
    // Add days for complete months in the current year
    for month in 1..date_time.date.month {
        total_days += match month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
            4 | 6 | 9 | 11 => 30,
            2 => {
                if (date_time.date.year % 4 == 0 && date_time.date.year % 100 != 0) 
                    || (date_time.date.year % 400 == 0) {
                    29
                } else {
                    28
                }
            }
            _ => 0,
        } as u32;
    }
    
    // Add remaining days
    total_days += (date_time.date.day - 1) as u32;
    
    // Convert to nanoseconds
    let nanos_from_days = total_days as u128 * 24 * 60 * 60 * 1_000_000_000;
    let nanos_from_time = date_time.time.hour as u128 * 60 * 60 * 1_000_000_000
        + date_time.time.min as u128 * 60 * 1_000_000_000
        + date_time.time.sec as u128 * 1_000_000_000
        + date_time.time.millis as u128 * 1_000_000;
    
    let total_nanos = nanos_from_days + nanos_from_time;
    
    // Create a Time struct representing this absolute time
    // Since AWKernel Time represents uptime, we return a Time with the calculated uptime
    Some(Time::zero() + core::time::Duration::from_nanos(total_nanos as u64))
}

fn to_vfs_date(date: Date) -> Option<Time> {
    // Convert Date to DateTime with time 00:00:00.000
    let date_time = DateTime::new(
        date,
        awkernel_lib::file::fatfs::time::Time::new(0, 0, 0, 0),
    );
    to_vfs_datetime(date_time)
}
