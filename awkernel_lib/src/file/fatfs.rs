use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use crate::sync::rwlock::RwLock;

use super::if_file::{FileSystemWrapper, FileSystemWrapperError};
pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

#[derive(Debug)]
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

#[derive(Debug)]
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

pub struct Fatfs {}

impl FileSystemWrapper for Fatfs {
    fn open(&self, interface_id: u64, fd: i64, path: &String) {
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

        log::info!("call wake_fs");
        super::wake_fs(interface_id);
    }

    fn open_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError> {
        let id = (interface_id, fd);
        log::info!("FatfsInMemory::open_wait called for ({}, {})", id.0, id.1);

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
            "Received completion for unknown/cancelled open operation: ({}, {})",
            interface_id, fd
        );
    }
}

pub fn cmd_queue_pop() -> Option<FatFileSystemCmdInfo> {
    let mut cmd_queue_guard = CMD_QUEUE.write();

    log::info!("cmd_queue_pop");
    if cmd_queue_guard.len() == 0 {
        log::info!("no cmd");
        return None;
    }

    log::info!("cmdinfo");
    let cmdinfo = cmd_queue_guard.remove(0);
    Some(cmdinfo)
}
