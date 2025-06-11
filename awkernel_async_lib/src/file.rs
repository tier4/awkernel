use crate::channel::bounded;
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{file::io::SeekFrom, sync::rwlock::RwLock};

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

#[derive(Eq, PartialEq, Debug, Clone)]
pub enum FileSystemRes {
    Success,
    ReadResult(Vec<u8>),
    WriteBytes(usize),
    SeekBytes(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FileSystemError {
    OutOfFds,
    FileSystemIsNotReady,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileDescriptorError {
    InvalidFilePath,
    OpenError,
    CreateError,
    ReadError,
    WriteError,
    SeekError,
    CloseError,
    FileSystemIsNotReady,
}

pub struct FileSystemManager {
    filesystems: BTreeMap<u64, Arc<bounded::Sender<FileSystemReq>>>,
    filesystem_id: u64,
    fd: i64,
}

impl FileSystemManager {
    fn get_new_fd(&mut self) -> Option<i64> {
        if self.fd == i64::MAX {
            return None;
        }
        self.fd += 1;
        Some(self.fd)
    }
}

pub static FILESYSTEM_MANAGER: RwLock<FileSystemManager> = RwLock::new(FileSystemManager {
    filesystems: BTreeMap::new(),
    filesystem_id: 0,
    fd: 0,
});

pub fn add_filesystem(tx: bounded::Sender<FileSystemReq>) {
    let mut manager = FILESYSTEM_MANAGER.write();
    if manager.filesystem_id == u64::MAX {
        panic!("filesystem id overflow");
    }
    let id = manager.filesystem_id;
    manager.filesystem_id += 1;
    manager.filesystems.insert(id, Arc::new(tx));
}

pub struct FileDescriptor {
    pub fd: i64,
    pub filesystem_id: u64,
    pub path: String,
    rx: bounded::Receiver<Result<FileSystemRes, FileSystemError>>,
}

impl FileDescriptor {
    pub async fn open(path: &str) -> Result<Self, FileSystemError> {
        Self::open_or_create(path, false).await
    }

    pub async fn create(path: &str) -> Result<Self, FileSystemError> {
        Self::open_or_create(path, true).await
    }

    pub async fn read(&self, buf: &mut [u8]) -> Result<usize, FileSystemError> {
        let req = FileSystemReq::Read {
            fd: self.fd,
            bufsize: buf.len(),
        };
        self.perform_io_op(req, |res| match res {
            FileSystemRes::ReadResult(data) => {
                let len = buf.len().min(data.len());
                if len > 0 {
                    buf[..len].copy_from_slice(&data[..len]);
                }
                Ok(len)
            }
            _ => unreachable!(),
        })
        .await
    }

    pub async fn write(&self, buf: &[u8]) -> Result<usize, FileSystemError> {
        let req = FileSystemReq::Write {
            fd: self.fd,
            buf: buf.to_vec(),
        };
        self.perform_io_op(req, |res| match res {
            FileSystemRes::WriteBytes(bytes) => Ok(bytes),
            _ => unreachable!(),
        })
        .await
    }

    pub async fn seek(&self, from: SeekFrom) -> Result<u64, FileSystemError> {
        let req = FileSystemReq::Seek { fd: self.fd, from };
        self.perform_io_op(req, |res| match res {
            FileSystemRes::SeekBytes(bytes) => Ok(bytes),
            _ => unreachable!(),
        })
        .await
    }

    pub async fn close(&self) -> Result<(), FileSystemError> {
        let req = FileSystemReq::Close { fd: self.fd };
        self.perform_io_op(req, |res| match res {
            FileSystemRes::Success => Ok(()),
            _ => unreachable!(),
        })
        .await
    }

    async fn open_or_create(path: &str, is_create: bool) -> Result<Self, FileSystemError> {
        if path.is_empty() {
            return Err(FileSystemError::InvalidFileNameLength);
        }

        // TODO: determine the filesystem_id from the path
        let filesystem_id = 0;
        let tx = Self::get_tx(filesystem_id)?;

        let fd = FILESYSTEM_MANAGER
            .write()
            .get_new_fd()
            .ok_or(FileSystemError::OutOfFds)?;
        let (tx_res, rx_res) = bounded::new(Default::default());

        let req = if is_create {
            FileSystemReq::Create {
                fd,
                path: path.to_string(),
                tx: tx_res,
            }
        } else {
            FileSystemReq::Open {
                fd,
                path: path.to_string(),
                tx: tx_res,
            }
        };

        tx.send(req)
            .await
            .map_err(|_| FileSystemError::FileSystemIsNotReady)?;
        let response = rx_res
            .recv()
            .await
            .map_err(|_| FileSystemError::FileSystemIsNotReady)?;

        match response {
            Ok(FileSystemRes::Success) => Ok(Self {
                fd,
                filesystem_id,
                path: path.to_string(),
                rx: rx_res,
            }),
            Err(e) => Err(e),
            _ => unreachable!(),
        }
    }

    async fn perform_io_op<F, T>(
        &self,
        req: FileSystemReq,
        response_handler: F,
    ) -> Result<T, FileSystemError>
    where
        F: FnOnce(FileSystemRes) -> Result<T, FileSystemError>,
    {
        let tx = Self::get_tx(self.filesystem_id)?;
        tx.send(req)
            .await
            .map_err(|_| FileSystemError::FileSystemIsNotReady)?;
        let response = self
            .rx
            .recv()
            .await
            .map_err(|_| FileSystemError::FileSystemIsNotReady)?;

        match response {
            Ok(res) => response_handler(res),
            Err(e) => Err(e),
        }
    }

    fn get_tx(filesystem_id: u64) -> Result<Arc<bounded::Sender<FileSystemReq>>, FileSystemError> {
        FILESYSTEM_MANAGER
            .read()
            .filesystems
            .get(&filesystem_id)
            .cloned()
            .ok_or(FileSystemError::FileSystemIsNotReady)
    }
}
