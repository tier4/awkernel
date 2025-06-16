pub mod boot_sector;
pub mod dir;
pub mod dir_entry;
pub mod file;
pub mod fs;
pub mod table;
pub mod time;

use super::super::{
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

use alloc::sync::Arc;

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
