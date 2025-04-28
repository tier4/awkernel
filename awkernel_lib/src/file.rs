use crate::{
    addr::{virt_addr, Addr},
    dma_pool::DMAPool,
    heap::TALLOC,
    paging::PAGESIZE,
    sync::rwlock::RwLock,
    sync::{mcs::MCSNode, mutex::Mutex},
};
use alloc::{collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, LossyOemCpConverter,
    NullTimeProvider, Read, Seek, SeekFrom, Write,
};

use self::if_file::{FileSystemCmd, FileSystemCmdInfo, IfFile};

pub mod if_file;

pub struct FileDescriptor {
    // Note first_cluster is None if file is empty
    first_cluster: Option<u32>,
    // Note: if offset points between clusters current_cluster is the previous cluster
    current_cluster: Option<u32>,
    // current position in this file
    offset: u32,
    // file dir entry editor - None for root dir
    entry: Option<fatfs::dir_entry::DirEntryEditor>,
}

#[derive(Debug)]
pub enum FileManagerError {
    InvalidFilePath,
    InvalidInterfaceID,
    CannotFindInterface,
    WriteError,
    ReadError,
    NotYetImplemented,
    InterfaceIsNotReady,

    DeviceError,
}

static FILE_MANAGER: RwLock<FileManager> = RwLock::new(FileManager {
    fd_to_file: BTreeMap::new(),
    interface_id: 0,
});

struct FileInfo {
    pub if_file: Arc<IfFile>,
    write_buf: Vec<u8>,
    read_buf: Vec<u8>,
}

pub struct FileManager {
    fd_to_file: BTreeMap<u64, Arc<FileInfo>>,
    interface_id: u64,
}

impl FileDescriptor {
    pub fn open_file(path: &str) -> Result<Self, FileManagerError> {
        let len = path.len();
        if len == 0 {
            return Err(FileManagerError::InvalidFilePath);
        }
        // TODO:Insert mount directory check and choose which interface to use
        let interface_id = 0;

        let mut file_manager = FILE_MANAGER.write();

        let file = file_manager
            .fd_to_file
            .get(&interface_id)
            .ok_or(FileManagerError::CannotFindInterface)?;

        let mut path_vec = Vec::with_capacity(len);

        unsafe {
            core::ptr::copy_nonoverlapping(path.as_ptr(), path_vec.as_mut_ptr(), len);
            path_vec.set_len(len);
        }

        file.if_file.cmd_queue.push(FileSystemCmdInfo {
            cmd: FileSystemCmd::OPEN_CMD,
            fd: -1,
            path: path_vec,
            size: 0,
        });

        Err(FileManagerError::NotYetImplemented)
    }

    pub fn create_file(path: &str) -> Result<Self, FileManagerError> {
        Err(FileManagerError::NotYetImplemented)
    }

    pub fn read_file(self, buf: &mut [u8]) -> Result<usize, FileManagerError> {
        Err(FileManagerError::NotYetImplemented)
    }

    pub fn write_file(self, buf: &[u8]) -> Result<usize, FileManagerError> {
        Err(FileManagerError::NotYetImplemented)
    }
}

/// The old waker will be replaced.
/// The waker will be called when calling `wake_reader()`
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if it is already notified.
pub fn register_waker_for_read(
    interface_id: u64,
    que_id: usize,
    waker: core::task::Waker,
) -> Result<bool, FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return Err(FileManagerError::InvalidInterfaceID);
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.register_waker_for_reader(que_id, waker)
}

pub fn wake_reader(interface_id: u64) {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return;
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.wake_reader();
}

#[inline(always)]
pub fn read(interface_id: u64) {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return;
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.poll_read();
}
