use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use crate::sync::rwlock::RwLock;

use super::if_file::{FileSystemWrapper, FileSystemWrapperError, SeekFrom};
pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

#[derive(Debug)]
pub enum FatFileSystemReq {
    Open { fd: i64, path: String },
    Create { fd: i64, path: String },
    Read { fd: i64, bufsize: usize },
    Write { fd: i64, buf: Vec<u8> },
    Seek { fd: i64, from: SeekFrom },
}

#[derive(Eq, PartialEq, Debug)]
pub enum FatFileSystemResult {
    Success,
    ReadResult(Vec<u8>),
    WriteBytes(usize),
    SeekBytes(usize),
}

#[derive(Debug)]
pub enum FatFsError {
    OpenError,
    CreateError,
    ReadError,
    WriteError,
    SeekError,
    InvalidFd,
}

pub struct PendingOperation {
    waker: Option<core::task::Waker>,
    result: Option<Result<FatFileSystemResult, FatFsError>>,
}

pub static PENDING_OPS: RwLock<BTreeMap<(u64, i64), PendingOperation>> =
    RwLock::new(BTreeMap::new());
static CMD_QUEUE: RwLock<Vec<FatFileSystemReq>> = RwLock::new(Vec::new()); // TODO: change this to RingQ

pub struct Fatfs {}

impl FileSystemWrapper for Fatfs {
    fn open(&self, interface_id: u64, fd: i64, path: &String) {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();
        let cmd_info = FatFileSystemReq::Open {
            fd,
            path: path.to_string(),
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
    }

    fn open_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError> {
        let id = (interface_id, fd);

        let mut pending_ops = PENDING_OPS.write();

        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                log::info!("Open operation completed for ({}, {})", id.0, id.1,);
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

    fn create(&self, interface_id: u64, fd: i64, path: &String) {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();
        let cmd_info = FatFileSystemReq::Create {
            fd,
            path: path.to_string(),
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
    }

    fn create_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError> {
        let id = (interface_id, fd);

        let mut pending_ops = PENDING_OPS.write();

        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                match result {
                    Ok(_) => Ok(true),
                    Err(_) => {
                        log::error!("Remote create operation failed for ({}, {})", id.0, id.1,);
                        Err(FileSystemWrapperError::CreateError) // TODO: Consider if it is okay to lose the information of error in fatfs.
                    }
                }
            } else {
                drop(pending_ops);
                Ok(false)
            }
        } else {
            panic!("PENDING_OPS entry not found for ({}, {}) in create_wait. This indicates a logic error.", id.0, id.1);
        }
    }

    fn read(&self, interface_id: u64, fd: i64, bufsize: usize) {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();
        let cmd_info = FatFileSystemReq::Read { fd, bufsize };
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
                "PENDING_OPS entry for ({}, {}) already existed on read push success.",
                id.0, id.1
            );
        }
        drop(pending_ops);

        super::wake_fs(interface_id);
    }

    fn read_wait(
        &self,
        interface_id: u64,
        fd: i64,
        buf: &mut [u8],
        waker: &core::task::Waker,
    ) -> Result<Option<usize>, FileSystemWrapperError> {
        let mut pending_ops = PENDING_OPS.write();

        let id = (interface_id, fd);
        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                match result {
                    Ok(FatFileSystemResult::ReadResult(data)) => {
                        let len = buf.len().min(data.len());
                        unsafe {
                            core::ptr::copy_nonoverlapping(data.as_ptr(), buf.as_mut_ptr(), len)
                        };
                        Ok(Some(len))
                    }
                    _ => {
                        log::error!("Remote read operation failed for ({}, {})", id.0, id.1,);
                        Err(FileSystemWrapperError::ReadError) // TODO: Consider if it is okay to lose the information of error in fatfs.
                    }
                }
            } else {
                drop(pending_ops);
                Ok(None)
            }
        } else {
            panic!(
                "PENDING_OPS entry not found for ({}, {}) in read. This indicates a logic error.",
                id.0, id.1
            );
        }
    }

    fn write(&self, interface_id: u64, fd: i64, buf: &[u8]) {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();
        let cmd_info = FatFileSystemReq::Write {
            fd,
            buf: buf.to_vec(),
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
                "PENDING_OPS entry for ({}, {}) already existed on read push success.",
                id.0, id.1
            );
        }
        drop(pending_ops);

        super::wake_fs(interface_id);
    }

    fn write_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<Option<usize>, FileSystemWrapperError> {
        let mut pending_ops = PENDING_OPS.write();

        let id = (interface_id, fd);
        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                match result {
                    Ok(FatFileSystemResult::WriteBytes(bytes)) => Ok(Some(bytes)),
                    _ => {
                        log::error!("Remote write operation failed for ({}, {})", id.0, id.1,);
                        Err(FileSystemWrapperError::WriteError) // TODO: Consider if it is okay to lose the information of error in fatfs.
                    }
                }
            } else {
                drop(pending_ops);
                Ok(None)
            }
        } else {
            panic!(
                "PENDING_OPS entry not found for ({}, {}) in read. This indicates a logic error.",
                id.0, id.1
            );
        }
    }

    fn seek(&self, interface_id: u64, fd: i64, from: SeekFrom) {
        let id = (interface_id, fd);

        let mut cmd_queue_guard = CMD_QUEUE.write();
        let cmd_info = FatFileSystemReq::Seek { fd, from };
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
                "PENDING_OPS entry for ({}, {}) already existed on read push success.",
                id.0, id.1
            );
        }
        drop(pending_ops);

        super::wake_fs(interface_id);
    }

    fn seek_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<Option<usize>, FileSystemWrapperError> {
        let mut pending_ops = PENDING_OPS.write();

        let id = (interface_id, fd);
        if let Some(op) = pending_ops.get_mut(&id) {
            if op.waker.is_none() {
                op.waker = Some(waker.clone());
            }

            if let Some(result) = op.result.take() {
                pending_ops.remove(&id);
                drop(pending_ops);

                match result {
                    Ok(FatFileSystemResult::SeekBytes(bytes)) => Ok(Some(bytes)),
                    _ => {
                        log::error!("Remote seek operation failed for ({}, {})", id.0, id.1,);
                        Err(FileSystemWrapperError::SeekError) // TODO: Consider if it is okay to lose the information of error in fatfs.
                    }
                }
            } else {
                drop(pending_ops);
                Ok(None)
            }
        } else {
            panic!(
                "PENDING_OPS entry not found for ({}, {}) in read. This indicates a logic error.",
                id.0, id.1
            );
        }
    }
}

pub fn complete_file_operation(
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
            "Received completion for unknown/cancelled operation: ({}, {})",
            interface_id, fd
        );
    }
}

pub fn cmd_queue_pop() -> Option<FatFileSystemReq> {
    let mut cmd_queue_guard = CMD_QUEUE.write();

    if cmd_queue_guard.len() == 0 {
        return None;
    }

    let cmdinfo = cmd_queue_guard.remove(0);
    Some(cmdinfo)
}
