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

#[derive(Eq, PartialEq, Debug)]
pub enum FatFileSystemResult {
    Success,
    ReadResult(Vec<u8>),
}
pub enum FatFsError {
    OpenError,
}

pub struct PendingOperation {
    waker: Option<core::task::Waker>,
    result: Option<Result<FatFileSystemResult, FatFsError>>,
}

pub static PENDING_OPS: RwLock<BTreeMap<(u64, i64), PendingOperation>> =
    RwLock::new(BTreeMap::new());
static CMD_QUEUE: RwLock<Vec<FatFileSystemCmdInfo>> = RwLock::new(Vec::new()); // TODO: change this to RingQ

impl FileSystemWrapper for FatfsInMemory {
    fn open(
        &self,
        interface_id: u64,
        fd: i64,
        path: &String,
    ) -> Result<bool, FileSystemWrapperError> {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();

        let cmd_info = FatFileSystemCmdInfo {
            cmd: FatFileSystemCmd::OpenCmd,
            fd,
            path: path.to_string(),
            size: 0,
        };

        cmd_queue_guard.push(cmd_info);
        let mut pending_ops = PENDING_OPS.write();
        if pending_ops
            .insert(
                id,
                PendingOperation {
                    waker: None,
                    result: None,
                },
            )
            .is_some()
        {
            panic!(
                "PENDING_OPS entry for ({}, {}) already existed on open push success.",
                id.0, id.1
            );
        }
        drop(pending_ops);
        super::wake_fs(interface_id);

        Ok(true)
    }

    fn open_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError> {
        let id = (interface_id, fd);
        log::trace!("FatfsInMemory::open_wait called for ({}, {})", id.0, id.1);

        let mut pending_ops = PENDING_OPS.write();

        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                log::trace!("Open operation completed for ({}, {})", id.0, id.1,);
                match result {
                    Ok(_) => Ok(true),
                    Err(_) => {
                        log::error!("Remote open operation failed for ({}, {})", id.0, id.1,);
                        Err(FileSystemWrapperError::OpenError) // TODO: Consider if it is okay to lose the information of error in fatfs.
                    }
                }
            } else {
                drop(pending_ops);
                Ok(false)
            }
        } else {
            panic!("PENDING_OPS entry not found for ({}, {}) in open_wait. This indicates a logic error.", id.0, id.1);
        }
    }
}

fn complete_file_operation(
    interface_id: u64,
    fd: i64,
    ret: Result<FatFileSystemResult, FatFsError>,
) {
    let mut pending_ops = PENDING_OPS.write();

    let id = (interface_id, fd);

    if let Some(op) = pending_ops.get_mut(&id) {
        op.result = Some(ret);
        if let Some(_) = op.waker {
            op.waker.clone().unwrap().wake();
        }
        // If op.waker is None, it means the file operation has completed before open_wait is called. It works fine since open_wait will soon be called.
    } else {
        panic!(
            "Received completion for unknown/cancelled open operation: ({}, {})",
            interface_id, fd
        );
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
