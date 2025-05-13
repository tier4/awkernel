use crate::{
    sync::rwlock::RwLock,
    sync::{mcs::MCSNode, mutex::Mutex},
};
use alloc::{borrow::Cow, collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use if_file::FileSystemWrapper;

use self::if_file::{FileSystemCmd, FileSystemCmdInfo, IfFile};

pub mod fatfs;
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
    fd: 0,
});

pub struct FileManager {
    interfaces: BTreeMap<u64, Arc<IfFile>>,
    interface_id: u64,
    fd: i64, // TODO: We will need a vacant fd BTreeMap.
}

impl FileManager {
    fn get_new_fd(&mut self) -> Option<i64> {
        let mut current_fd = self.fd;
        let max_fd = i64::MAX;

        current_fd += 1;

        if current_fd == max_fd {
            None
        } else {
            self.fd = current_fd;
            Some(current_fd)
        }
    }
}

#[derive(Clone)]
pub struct FileDescriptor {
    pub fd: i64,
    pub interface_id: u64,
    pub path: String,
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
            .get_new_fd()
            .ok_or(FileManagerError::OutOfFds)?;

        let if_file = file_manager
            .interfaces
            .get(&interface_id)
            .ok_or(FileManagerError::CannotFindInterface)?;

        let path_string = String::from(path);

        Ok(FileDescriptor {
            fd,
            interface_id,
            path: path_string,
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
