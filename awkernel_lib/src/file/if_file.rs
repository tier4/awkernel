use alloc::{borrow::Cow, collections::BTreeMap, sync::Arc};
use awkernel_async_lib_verified::ringq::RingQ;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{FileManagerError, FileSystemResult, FILE_MANAGER};

const IF_FILE_CMD_QUEUE_SIZE: usize = 256;

#[cfg(not(feature = "std"))]
use alloc::{string::String, vec::Vec};

pub enum FileSystemCmd {
    OpenCmd,
    CreateCmd,
    ReadCmd,
    WriteCmd,
    SeekCmd,
}

pub struct FileSystemCmdInfo {
    pub cmd: FileSystemCmd,
    pub fd: i64,
    pub path: String,
    pub size: usize,
}

enum FileSystemWakeState {
    None,
    Notified,
    Wake(core::task::Waker),
}
enum FdWakeState {
    None,
    Notified,
    Wake(core::task::Waker),
}

pub(super) struct IfFile {
    pub(super) filesystem: Arc<dyn FileSystemWrapper + Sync + Send>,
    fdwakers: Mutex<BTreeMap<i64, FdWakeState>>,
    fswaker: Mutex<FileSystemWakeState>,
    pub(super) cmd_queue: Mutex<RingQ<FileSystemCmdInfo>>,
}

impl IfFile {
    pub fn new(filesystem: Arc<dyn FileSystemWrapper + Sync + Send>) -> Self {
        let fdwakers = Mutex::new(BTreeMap::new());
        let fswaker = Mutex::new(FileSystemWakeState::None);
        let cmd_queue = Mutex::new(RingQ::new(IF_FILE_CMD_QUEUE_SIZE));
        IfFile {
            filesystem,
            fdwakers,
            fswaker,
            cmd_queue,
        }
    }

    pub fn cmd_queue_pop(&self) -> Option<FileSystemCmdInfo> {
        let mut node = MCSNode::new();
        let mut cmd_queue_guard = self.cmd_queue.lock(&mut node);
        let cmdinfo = cmd_queue_guard.pop();
        cmdinfo
    }

    #[inline(always)]
    pub fn wake_fs(&self) {
        let mut node = MCSNode::new();
        let mut waker = self.fswaker.lock(&mut node);

        let FileSystemWakeState::Wake(w) = waker.as_ref() else {
            *waker = FileSystemWakeState::Notified;
            return;
        };

        w.wake_by_ref();

        *waker = FileSystemWakeState::None;
    }

    /// Returns true if the waker is registered successfully.
    /// Returns false if it is already notified.
    #[inline(always)]
    pub fn register_waker_for_fs(
        &self,
        waker: core::task::Waker,
    ) -> Result<bool, FileManagerError> {
        let mut node = MCSNode::new();
        let mut guard = self.fswaker.lock(&mut node);

        match guard.as_ref() {
            FileSystemWakeState::None => {
                *guard = FileSystemWakeState::Wake(waker);
                Ok(true)
            }
            FileSystemWakeState::Notified => {
                *guard = FileSystemWakeState::None;
                Ok(false)
            }
            FileSystemWakeState::Wake(_) => {
                *guard = FileSystemWakeState::Wake(waker);
                Ok(true)
            }
        }
    }

    pub fn register_waker_for_fd(&self, fd: i64, waker: core::task::Waker) {
        let mut node = MCSNode::new();
        let mut fdwakers = self.fdwakers.lock(&mut node);
        let fdwaker = fdwakers.get_mut(&fd);
        if let Some(fdwaker) = fdwaker {
            *fdwaker = FdWakeState::Wake(waker);
        } else {
            fdwakers.insert(fd, FdWakeState::Wake(waker));
        }
    }
}
pub enum FileSystemWrapperError {
    OpenError,
    CreateError,
    WriteError,
    ReadError,
    SeekError,
}

pub trait FileSystemWrapper {
    fn open(&self, path: &str, waker: core::task::Waker) -> Result<(), FileSystemWrapperError>;
    fn create(&self, path: &str);
    fn read(&self, fd: u32, buf: &mut u8, waker: core::task::Waker);
    fn device_short_name(&self) -> Cow<'static, str>;
    fn filesystem_short_name(&self) -> Cow<'static, str>;
}
