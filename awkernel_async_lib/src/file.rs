use crate::channel::unbounded;
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::rwlock::RwLock;

#[derive(Clone)]
pub enum FileSystemReq {
    Open {
        fd: i64,
        path: String,
        tx: unbounded::Sender<Result<FileSystemRes, FileSystemError>>,
    },
    Create {
        fd: i64,
        path: String,
        tx: unbounded::Sender<Result<FileSystemRes, FileSystemError>>,
    },
    Read {
        fd: i64,
        bufsize: usize,
    },
    Write {
        fd: i64,
        buf: Vec<u8>,
    },
    Seek {
        fd: i64,
        from: SeekFrom,
    },
    Close {
        fd: i64,
    },
}

#[derive(Debug, Clone)]
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub enum FileSystemRes {
    Success,
    ReadResult(Vec<u8>),
    WriteBytes(usize),
    SeekBytes(u64),
}

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

pub static FILESYSTEM_MANAGER: RwLock<FileSystemManager> = RwLock::new(FileSystemManager {
    filesystems: BTreeMap::new(),
    filesystem_id: 0,
    fd: 0,
});

pub struct FileSystemManager {
    filesystems: BTreeMap<u64, Arc<unbounded::Sender<FileSystemReq>>>,
    filesystem_id: u64,
    fd: i64, // TODO: We will need a vacant fd BTreeMap.
}

impl FileSystemManager {
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

pub fn add_filesystem(tx: unbounded::Sender<FileSystemReq>) {
    let mut file_manager = FILESYSTEM_MANAGER.write();

    if file_manager.filesystem_id == u64::MAX {
        panic!("filesystem id overflow");
    }

    let id = file_manager.filesystem_id;
    file_manager.filesystem_id += 1;

    file_manager.filesystems.insert(id, Arc::new(tx));
}

pub struct FileDescriptor {
    pub fd: i64,
    pub filesystem_id: u64,
    pub path: String,
    pub rx: unbounded::Receiver<Result<FileSystemRes, FileSystemError>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileDescriptorError {
    FileDescriptionCreationError,
    ReadError,
    WriteError,
    SeekError,
    InterfaceIsNotReady,
}

#[derive(Clone)]
pub enum FileSystemError {
    CannotFindFile,
    OpenError,
    CreateError,
    ReadError,
    WriteError,
    SeekError,
}

impl FileDescriptor {
    pub fn new(
        path: &str,
        rx: unbounded::Receiver<Result<FileSystemRes, FileSystemError>>,
    ) -> Result<Self, FileManagerError> {
        let len = path.len();
        if len == 0 {
            return Err(FileManagerError::InvalidFilePath);
        }
        // TODO:Insert mount directory check and choose which interface to use.
        let filesystem_id = 0;

        let mut file_manager = FILESYSTEM_MANAGER.write();

        let fd = file_manager
            .get_new_fd()
            .ok_or(FileManagerError::OutOfFds)?;

        let path_string = String::from(path);

        Ok(FileDescriptor {
            fd,
            filesystem_id,
            path: path_string,
            rx,
        })
    }
}

impl FileDescriptor {
    pub fn get_tx(filesystem_id: u64) -> Arc<unbounded::Sender<FileSystemReq>> {
        let filesystem_manager = FILESYSTEM_MANAGER.read();
        filesystem_manager
            .filesystems
            .get(&filesystem_id)
            .unwrap()
            .clone()
    }

    pub async fn open(path: &str) -> Result<FileDescriptor, FileDescriptorError> {
        // TODO: determine the filesystem_id from the path
        let filesystem_id = 0;

        let tx = FileDescriptor::get_tx(filesystem_id);
        let (tx_fd, rx_fd) = unbounded::new();
        let file_handle = FileDescriptor::new(path, rx_fd)
            .or(Err(FileDescriptorError::FileDescriptionCreationError))?;

        tx.send(FileSystemReq::Open {
            fd: file_handle.fd,
            path: path.to_string(),
            tx: tx_fd,
        })
        .await
        .unwrap(); // TODO

        let res = file_handle.rx.recv().await.unwrap(); // TODO

        Ok(file_handle)
    }

    pub async fn create(path: &str) -> Result<FileDescriptor, FileDescriptorError> {
        // TODO: determine the filesystem_id from the path
        let filesystem_id = 0;

        let tx = FileDescriptor::get_tx(filesystem_id);
        let (tx_fd, rx_fd) = unbounded::new();
        let file_handle = FileDescriptor::new(path, rx_fd)
            .or(Err(FileDescriptorError::FileDescriptionCreationError))?;

        let Ok(_) = tx
            .send(FileSystemReq::Create {
                fd: file_handle.fd,
                path: path.to_string(),
                tx: tx_fd,
            })
            .await
        else {
            panic!("send error");
        };

        let res = file_handle.rx.recv().await.unwrap(); // TODO

        Ok(file_handle)
    }

    pub async fn read(&self, buf: &mut [u8]) -> Result<usize, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        let Ok(_) = tx
            .send(FileSystemReq::Read {
                fd: self.fd,
                bufsize: buf.len(),
            })
            .await
        else {
            panic!("send error");
        };

        let res = self.rx.recv().await.unwrap(); // TODO

        match res {
            Ok(FileSystemRes::ReadResult(data)) => {
                let len = buf.len().min(data.len());
                unsafe { core::ptr::copy_nonoverlapping(data.as_ptr(), buf.as_mut_ptr(), len) };
                Ok(len)
            }
            _ => Err(FileDescriptorError::ReadError),
        }
    }

    pub async fn write(&self, buf: &[u8]) -> Result<usize, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        let Ok(_) = tx
            .send(FileSystemReq::Write {
                fd: self.fd,
                buf: buf.to_vec(),
            })
            .await
        else {
            panic!("send error");
        };

        let res = self.rx.recv().await.unwrap(); // TODO

        match res {
            Ok(FileSystemRes::WriteBytes(bytes)) => Ok(bytes),
            _ => Err(FileDescriptorError::WriteError),
        }
    }

    pub async fn seek(&self, from: SeekFrom) -> Result<u64, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        let Ok(_) = tx.send(FileSystemReq::Seek { fd: self.fd, from }).await else {
            panic!("send error");
        };

        let res = self.rx.recv().await.unwrap(); //TODO

        match res {
            Ok(FileSystemRes::SeekBytes(bytes)) => Ok(bytes),
            _ => Err(FileDescriptorError::SeekError),
        }
    }

    pub async fn close(&self) -> Result<(), FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        let Ok(_) = tx.send(FileSystemReq::Close { fd: self.fd }).await else {
            panic!("send error");
        };

        let res = self.rx.recv().await.unwrap(); // TODO

        match res {
            Ok(FileSystemRes::Success) => Ok(()),
            _ => Err(FileDescriptorError::SeekError),
        }
    }
}
