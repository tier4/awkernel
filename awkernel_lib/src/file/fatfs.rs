use alloc::{
    borrow::Cow,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_async_lib_verified::ringq::RingQ;

use crate::{
    heap::TALLOC,
    paging::{self, PAGESIZE},
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

use super::{
    add_interface,
    if_file::{FileSystemWrapper, FileSystemWrapperError},
    FileManagerError, FileSystemResult, FILE_MANAGER,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
    future::Future,
    task::Poll,
    time::Duration,
};
use fatfs::{
    format_volume, DirEntryEditor, File as FatfsFile, FileSystem, FormatVolumeOptions, FsOptions,
    IoBase, LossyOemCpConverter, NullTimeProvider, OemCpConverter, Read, ReadWriteSeek, Seek,
    SeekFrom, TimeProvider, Write,
};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

type FatFileSystem = FileSystem<InMemoryDisk, NullTimeProvider, LossyOemCpConverter>;
type FatFile = FatfsFile<'static, InMemoryDisk, NullTimeProvider, LossyOemCpConverter>;

static FAT_FILESYSTEM: RwLock<Option<FatFileSystem>> = RwLock::new(None);
pub static FILES: RwLock<BTreeMap<i64, FatFile>> = RwLock::new(BTreeMap::new());

const FATFS_CMD_QUEUE_SIZE: usize = 256;
pub struct FatfsInMemory {}

//pub fn init_filesystem() {
//let filesystem = FatfsInMemory {};
//add_interface(Arc::new(filesystem));

//let Ok(layout) = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE) else {
//panic!("Invalid layout")
//};

//let result = unsafe { TALLOC.alloc(layout) };
//if result.is_null() {
//panic!("NULL pointer");
//}

//let data =
//unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
//let mut disk = InMemoryDisk { data, position: 0 };
//let options = FormatVolumeOptions::new();
//if format_volume(&mut disk, options).is_ok() {
//log::info!("FAT filesystem formatted successfully in memory!");
//} else {
//log::info!("Error formatting!");
//}
//let fs = FileSystem::new(disk, FsOptions::new()).expect("Error creating file system");
//let mut fs_guard = FAT_FILESYSTEM.write();
//if fs_guard.is_none() {
//*fs_guard = Some(fs);
//log::info!("FAT_FILESYSTEM initialized successfully.");
//} else {
//panic!("FAT_FILESYSTEM already initialized!");
//}
//}
pub enum FatFileSystemCmd {
    OpenCmd,
    CreateCmd,
    ReadCmd,
    WriteCmd,
    SeekCmd,
}

pub struct FatFileSystemCmdInfo {
    pub cmd: FatFileSystemCmd,
    pub fd: i64,
    pub path: String,
    pub size: usize,
}

#[derive(Eq, PartialEq)]
pub enum FatFileSystemResult {
    None,
    Success,
    Failure,
    ReadResult(Vec<u8>),
}

static CMD_QUEUE: RwLock<Option<RingQ<FatFileSystemCmdInfo>>> = RwLock::new(None);
static RET_RESULT: RwLock<FatFileSystemResult> = RwLock::new(FatFileSystemResult::None);

impl FileSystemWrapper for FatfsInMemory {
    fn open(
        &self,
        interface_id: u64,
        fd: i64,
        path: &String,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError> {
        {
            let mut cmd_queue_guard = CMD_QUEUE.write();
            let queue: &mut RingQ<FatFileSystemCmdInfo> =
                cmd_queue_guard.get_or_insert_with(|| {
                    log::info!("Initializing command queue.");
                    RingQ::new(FATFS_CMD_QUEUE_SIZE)
                });

            let cmd_info = FatFileSystemCmdInfo {
                cmd: FatFileSystemCmd::OpenCmd,
                fd,
                path: path.to_string(),
                size: 0,
            };

            match queue.push(cmd_info) {
                Ok(_) => {
                    super::wake_fs(interface_id);
                    return Ok(true);
                }
                Err(_) => {
                    let _ = super::register_waker_for_fd(interface_id, fd, waker.clone());
                    return Ok(false);
                }
            }
        }
    }
}

struct InMemoryDisk {
    data: Vec<u8>,
    position: u64,
}

impl InMemoryDisk {
    fn new(size: usize) -> Self {
        let mut data = Vec::new();
        data.resize(size, 0);
        InMemoryDisk { data, position: 0 }
    }
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
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let new_position = match pos {
            SeekFrom::Start(offset) => offset as i64,
            SeekFrom::Current(offset) => self.position as i64 + offset,
            SeekFrom::End(offset) => self.data.len() as i64 + offset,
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
