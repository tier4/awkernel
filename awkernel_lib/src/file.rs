use crate::{
    sync::rwlock::RwLock,
    sync::{mcs::MCSNode, mutex::Mutex},
};
use alloc::{borrow::Cow, collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use if_file::FileSystemWrapper;

use self::if_file::{FileSystemCmd, FileSystemCmdInfo, IfFile};

pub mod if_file;

#[derive(Debug)]
pub enum FileManagerError {
    InvalidFilePath,
    InvalidInterfaceID,
    InvalidFileDescriptor,
    CannotFindInterface,
    OpenError,
    WriteError,
    ReadError,
    NotYetImplemented,
    InterfaceIsNotReady,
    OutOfFds,
    DeviceError,
}

pub static FILE_MANAGER: RwLock<FileManager> = RwLock::new(FileManager {
    interfaces: BTreeMap::new(),
    interface_id: 0,
    fd_to_file: BTreeMap::new(),
    fd: 0,
});

#[derive(Eq, PartialEq)]
pub enum FileSystemResult {
    None,
    Success,
    Failure,
    ReadResult(Vec<u8>),
}

struct FileInfo {
    ret: Mutex<FileSystemResult>,
}

pub struct FileManager {
    interfaces: BTreeMap<u64, Arc<IfFile>>,
    interface_id: u64,
    fd_to_file: BTreeMap<i64, Arc<FileInfo>>,
    fd: i64,
}

impl FileManager {
    fn get_new_fd(&self) -> Option<i64> {
        let mut current_fd = self.fd;
        let max_fd = i64::MAX;

        while current_fd <= max_fd {
            if !self.fd_to_file.contains_key(&current_fd) {
                return Some(current_fd);
            }
            current_fd += 1;
        }
        None
    }

    fn new_fileinfo(&mut self) -> Option<i64> {
        let fd = self.get_new_fd();
        if let Some(fd) = fd {
            self.fd_to_file.insert(
                fd,
                Arc::new(FileInfo {
                    ret: Mutex::new(FileSystemResult::None),
                }),
            );
        }
        fd
    }
}

#[derive(Clone)]
pub struct FileDescriptor {
    pub fd: i64,
    pub interface_id: u64,
    pub filesystem: Arc<dyn FileSystemWrapper + Sync + Send>,
}

impl FileDescriptor {
    pub fn open_file(path: &str) -> Result<Self, FileManagerError> {
        let len = path.len();
        if len == 0 {
            return Err(FileManagerError::InvalidFilePath);
        }
        // TODO:Insert mount directory check and choose which interface to use.
        let interface_id = 0;

        let mut file_manager = FILE_MANAGER.write();

        let fd = file_manager
            .new_fileinfo()
            .ok_or(FileManagerError::OutOfFds)?;

        let if_file = file_manager
            .interfaces
            .get(&interface_id)
            .ok_or(FileManagerError::CannotFindInterface)?;

        let path_string = String::from(path);
        {
            let mut node = MCSNode::new();
            let mut cmd_queue_guard = if_file.cmd_queue.lock(&mut node);
            let _ = cmd_queue_guard.push(FileSystemCmdInfo {
                cmd: FileSystemCmd::OpenCmd,
                fd,
                path: path_string,
                size: 0,
            }); // TODO: Error handling
        }

        if_file.wake_fs();

        Ok(FileDescriptor {
            fd,
            interface_id,
            filesystem: if_file.filesystem.clone(),
        })
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

#[derive(Debug)]
pub struct IfFileStatus {
    pub interface_id: u64,
    //pub filesystem_name: Cow<'static, str>,
    //pub device_name: Cow<'static, str>,
}

//pub fn get_interface(interface_id: u64) -> Result<IfFileStatus, FileManagerError> {
//let file_manager = FILE_MANAGER.read();

//let if_file = file_manager
//.interfaces
//.get(&interface_id)
//.ok_or(FileManagerError::InvalidInterfaceID)?;

//let if_status = IfFileStatus {
//interface_id,
////filesystem_name: inner.filesystem_short_name(),
////device_name: inner.device_short_name(),
//};

//Ok(if_status)
//}

//pub fn get_all_interface() -> Vec<IfFileStatus> {
//let file_manager = FILE_MANAGER.read();

//let mut result = Vec::new();

//for id in file_manager.interfaces.keys() {
//if let Ok(if_status) = get_interface(*id) {
//result.push(if_status);
//}
//}

//result
//}

pub fn add_interface(file_system: Arc<dyn FileSystemWrapper + Sync + Send>) {
    let mut file_manager = FILE_MANAGER.write();

    if file_manager.interface_id == u64::MAX {
        panic!("filesystem interface id overflow");
    }

    let id = file_manager.interface_id;
    file_manager.interface_id += 1;

    let if_file = Arc::new(IfFile::new(file_system));

    file_manager.interfaces.insert(id, if_file);
}

pub fn register_waker_for_fd(
    interface_id: u64,
    fd: i64,
    waker: core::task::Waker,
) -> Result<(), FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return Err(FileManagerError::InvalidInterfaceID);
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.register_waker_for_fd(fd, waker);

    Ok(())
}

/// The old waker will be replaced.
/// The waker will be called when calling `wake_reader()`
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if it is already notified.
pub fn register_waker_for_fs(
    interface_id: u64,
    waker: core::task::Waker,
) -> Result<bool, FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return Err(FileManagerError::InvalidInterfaceID);
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.register_waker_for_fs(waker)
}

pub fn wake_fs(interface_id: u64) {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return;
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    if_file.wake_fs();
}

#[inline(always)]
pub fn cmd_queue_pop(interface_id: u64) -> Result<Option<FileSystemCmdInfo>, FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let Some(if_file) = file_manager.interfaces.get(&interface_id) else {
        return Err(FileManagerError::CannotFindInterface);
    };

    let if_file = Arc::clone(if_file);
    drop(file_manager);

    Ok(if_file.cmd_queue_pop())
}

pub fn ret_push(fd: i64, ret: FileSystemResult) -> Result<(), FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let file = file_manager.fd_to_file.get(&fd);
    if let Some(file) = file {
        let mut node = MCSNode::new();
        let mut ret_guard = file.ret.lock(&mut node);
        *ret_guard = ret;
        Ok(())
    } else {
        return Err(FileManagerError::InvalidFileDescriptor);
    }
}

pub fn ret_pop(fd: i64) -> Result<FileSystemResult, FileManagerError> {
    let file_manager = FILE_MANAGER.read();

    let file = file_manager.fd_to_file.get(&fd);
    if let Some(file) = file {
        let mut node = MCSNode::new();
        let mut ret_guard = file.ret.lock(&mut node);
        match *ret_guard {
            FileSystemResult::ReadResult(_) => panic!("Unexpected return"),
            FileSystemResult::Failure => {
                *ret_guard = FileSystemResult::None;
                Ok(FileSystemResult::Failure)
            }
            FileSystemResult::Success => {
                *ret_guard = FileSystemResult::None;
                Ok(FileSystemResult::Success)
            }
            FileSystemResult::None => {
                *ret_guard = FileSystemResult::None;
                Ok(FileSystemResult::None)
            }
        }
    } else {
        Err(FileManagerError::InvalidFileDescriptor)
    }
}
