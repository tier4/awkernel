//! # Network Interface Module
//!
//! This module provides the network interface module.
//!
//! `IfNet` is a structure that manages the network interface.
//! `NetDriver` is a structure that manages the network driver.
//!
//!　These structures contain the following mutex-protected fields:
//!
//! 1. `NetDriver::rx_ringq`
//! 2. `IfNet::tx_ringq`
//! 3. `IfNet::inner`
//!
//! These mutexes must be locked in the order shown above.

use core::{
    net::Ipv4Addr,
    sync::atomic::{AtomicUsize, Ordering},
};

use alloc::{
    collections::{btree_map, btree_set::BTreeSet, BTreeMap},
    sync::Arc,
};
use awkernel_async_lib_verified::ringq::RingQ;
use smoltcp::{
    iface::{Config, Interface, MulticastError, SocketSet},
    phy::{self, Checksum, Device, DeviceCapabilities},
    time::Instant,
    wire::HardwareAddress,
};

use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};

use super::{FileManagerError, FileSystemWrapper};

#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};
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

pub enum FileSystemCmd {
    OPEN_CMD,
    CREATE_CMD,
    READ_CMD,
    WRITE_CMD,
    SEEK_CMD,
}

pub struct FileSystemCmdInfo {
    pub cmd: FileSystemCmd,
    pub fd: i64,
    pub path: Vec<u8>,
    pub size: usize,
}

pub(super) struct IfFile {
    pub(super) filesystem: Arc<dyn FileSystemWrapper + Sync + Send>,
    fdwakers: BTreeMap<u64, Mutex<FdWakeState>>,
    waker: Mutex<FileSystemWakeState>,
    pub(super) cmd_queue: RingQ<FileSystemCmdInfo>,
}

impl IfFile {
    pub fn new(filesystem: Arc<dyn FileSystemWrapper + Sync + Send>) -> Self {
        IfFile { filesystem }
    }

    pub fn poll_read() {}

    #[inline(always)]
    pub fn wake_reader(&self) {
        let Some(waker) = self.reader.get() else {
            return;
        };

        let mut node = MCSNode::new();
        let mut waker = waker.lock(&mut node);

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
    pub fn register_waker_for_reader(
        &self,
        que_id: usize,
        waker: core::task::Waker,
    ) -> Result<bool, FileManagerError> {
        let Some(w) = self.reader.get(que_id) else {
            return Err(FileManagerError::InvalidQueueID);
        };

        let mut node = MCSNode::new();
        let mut guard = w.lock(&mut node);

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

trait FileSystemWrapper {
    fn open(&self, file: &str);
    fn create(&self, file: &str);
    fn read(&self, fd: u32, buf: &mut u8, waker: &core::task::Waker);
}
