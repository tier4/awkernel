use crate::channel::bounded;
use alloc::{
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::rwlock::RwLock;

pub enum FileSystemReq {
    Open {
        fd: i64,
        path: String,
        tx: bounded::Sender<Result<FileSystemRes, FileSystemError>>,
    },
    Create {
        fd: i64,
        path: String,
        tx: bounded::Sender<Result<FileSystemRes, FileSystemError>>,
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

pub static FILESYSTEM_MANAGER: RwLock<FileSystemManager> = RwLock::new(FileSystemManager {
    filesystems: alloc::collections::BTreeMap::new(),
    filesystem_id: 0,
    fd: 0,
});

pub struct FileSystemManager {
    filesystems: alloc::collections::BTreeMap<u64, Arc<bounded::Sender<FileSystemReq>>>,
    filesystem_id: u64,
    fd: i64,
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

pub fn add_filesystem(tx: bounded::Sender<FileSystemReq>) {
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
    pub rx: bounded::Receiver<Result<FileSystemRes, FileSystemError>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileDescriptorError {
    InvalidFilePath,
    OutOfFds,
    OpenError,
    CreateError,
    ReadError,
    WriteError,
    SeekError,
    CloseError,
    FileSystemIsNotReady,
}

#[derive(Clone, Debug)]
pub enum FileSystemError {
    NotFound,
    AlreadyExists,
    InvalidInput,
    NotEnoughSpace,
    CorruptedFileSystem,
    IoError,
    UnexpectedEof,
    WriteZero,
    InvalidFileNameLength,
    UnsupportedFileNameCharacter,
    DirectoryIsNotEmpty,
    UnknownError,
}

impl FileDescriptor {
    pub fn new(
        path: &str,
        rx: bounded::Receiver<Result<FileSystemRes, FileSystemError>>,
    ) -> Result<Self, FileDescriptorError> {
        let len = path.len();
        if len == 0 {
            return Err(FileDescriptorError::InvalidFilePath);
        }
        // TODO:Insert mount directory check and choose which interface to use.
        let filesystem_id = 0;

        let mut file_manager = FILESYSTEM_MANAGER.write();

        let fd = file_manager
            .get_new_fd()
            .ok_or(FileDescriptorError::OutOfFds)?;

        let path_string = String::from(path);

        Ok(FileDescriptor {
            fd,
            filesystem_id,
            path: path_string,
            rx,
        })
    }

    pub fn get_tx(filesystem_id: u64) -> Arc<bounded::Sender<FileSystemReq>> {
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
        let (tx_fd, rx_fd) = bounded::new(Default::default());
        let file_handle = FileDescriptor::new(path, rx_fd)?;

        tx.send(FileSystemReq::Open {
            fd: file_handle.fd,
            path: path.to_string(),
            tx: tx_fd,
        })
        .await
        .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = file_handle
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::Success) => Ok(file_handle),
            _ => Err(FileDescriptorError::OpenError),
        }
    }

    pub async fn create(path: &str) -> Result<FileDescriptor, FileDescriptorError> {
        // TODO: determine the filesystem_id from the path
        let filesystem_id = 0;

        let tx = FileDescriptor::get_tx(filesystem_id);
        let (tx_fd, rx_fd) = bounded::new(Default::default());
        let file_handle = FileDescriptor::new(path, rx_fd)?;

        tx.send(FileSystemReq::Create {
            fd: file_handle.fd,
            path: path.to_string(),
            tx: tx_fd,
        })
        .await
        .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = file_handle
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::Success) => Ok(file_handle),
            _ => Err(FileDescriptorError::CreateError),
        }
    }

    pub async fn read(&self, buf: &mut [u8]) -> Result<usize, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        tx.send(FileSystemReq::Read {
            fd: self.fd,
            bufsize: buf.len(),
        })
        .await
        .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = self
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::ReadResult(data)) => {
                let len = buf.len().min(data.len());
                if len > 0 {
                    buf[..len].copy_from_slice(&data.as_slice()[..len]);
                }
                Ok(len)
            }
            _ => Err(FileDescriptorError::ReadError),
        }
    }

    pub async fn write(&self, buf: &[u8]) -> Result<usize, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        tx.send(FileSystemReq::Write {
            fd: self.fd,
            buf: buf.to_vec(),
        })
        .await
        .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = self
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::WriteBytes(bytes)) => Ok(bytes),
            _ => Err(FileDescriptorError::WriteError),
        }
    }

    pub async fn seek(&self, from: SeekFrom) -> Result<u64, FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        tx.send(FileSystemReq::Seek { fd: self.fd, from })
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = self
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::SeekBytes(bytes)) => Ok(bytes),
            _ => Err(FileDescriptorError::SeekError),
        }
    }

    pub async fn close(&self) -> Result<(), FileDescriptorError> {
        let tx = FileDescriptor::get_tx(self.filesystem_id);

        tx.send(FileSystemReq::Close { fd: self.fd })
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        let response = self
            .rx
            .recv()
            .await
            .map_err(|_| FileDescriptorError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::Success) => Ok(()),
            _ => Err(FileDescriptorError::FileSystemIsNotReady),
        }
    }
}
