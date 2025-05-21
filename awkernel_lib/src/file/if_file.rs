use alloc::sync::Arc;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::FileManagerError;

#[cfg(not(feature = "std"))]
use alloc::string::String;

enum FileSystemWakeState {
    None,
    Notified,
    Wake(core::task::Waker),
}

pub(super) struct IfFile {
    pub(super) filesystem: Arc<dyn FileSystemWrapper + Sync + Send>,
    fswaker: Mutex<FileSystemWakeState>,
}

impl IfFile {
    pub fn new(filesystem: Arc<dyn FileSystemWrapper + Sync + Send>) -> Self {
        let fswaker = Mutex::new(FileSystemWakeState::None);
        IfFile {
            filesystem,
            fswaker,
        }
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
}
pub enum FileSystemWrapperError {
    OpenError,
    CreateError,
    WriteError,
    ReadError,
    SeekError,
}

pub trait FileSystemWrapper {
    fn open(&self, interface_id: u64, fd: i64, path: &String);

    fn open_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError>;

    fn create(&self, interface_id: u64, fd: i64, path: &String);

    fn create_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<bool, FileSystemWrapperError>;

    fn read(&self, interface_id: u64, fd: i64, size: usize);

    fn read_wait(
        &self,
        interface_id: u64,
        fd: i64,
        buf: &mut [u8],
        waker: &core::task::Waker,
    ) -> Result<Option<usize>, FileSystemWrapperError>;

    fn write(&self, interface_id: u64, fd: i64, buf: &[u8]);

    fn write_wait(
        &self,
        interface_id: u64,
        fd: i64,
        waker: &core::task::Waker,
    ) -> Result<Option<usize>, FileSystemWrapperError>;
    //fn device_short_name(&self) -> Cow<'static, str>;
    //fn filesystem_short_name(&self) -> Cow<'static, str>;
}
