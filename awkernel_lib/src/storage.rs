use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use storage_device::{StorageDevError, StorageDevice, StorageDeviceType};

pub mod storage_device;

#[derive(Debug)]
pub enum StorageManagerError {
    InvalidDeviceID,
    InvalidTransferID,
    DeviceError(StorageDevError),
    NotYetImplemented,
    PoolNotInitialized,
}

#[derive(Debug)]
pub struct StorageStatus {
    pub device_id: u64,
    pub device_name: Cow<'static, str>,
    pub device_type: StorageDeviceType,
    pub irqs: Vec<u16>,
    pub block_size: usize,
    pub num_blocks: u64,
}

static STORAGE_MANAGER: RwLock<StorageManager> = RwLock::new(StorageManager {
    devices: BTreeMap::new(),
    device_id: 0,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

pub struct StorageManager {
    devices: BTreeMap<u64, Arc<dyn StorageDevice>>,
    device_id: u64,
}

enum IRQWaker {
    Waker(core::task::Waker),
    Interrupted,
}

pub fn add_storage_device(device: Arc<dyn StorageDevice + Sync + Send>) -> u64 {
    let mut manager = STORAGE_MANAGER.write();

    if manager.device_id == u64::MAX {
        panic!("storage device id overflow");
    }

    let id = manager.device_id;
    manager.device_id += 1;

    manager.devices.insert(id, device);

    id
}

pub fn get_device_block_size(device_id: u64) -> Result<usize, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device = manager
        .devices
        .get(&device_id)
        .ok_or(StorageManagerError::InvalidDeviceID)?;

    Ok(device.block_size())
}

pub fn get_storage_device(device_id: u64) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device = manager
        .devices
        .get(&device_id)
        .ok_or(StorageManagerError::InvalidDeviceID)?;

    Ok(device.clone())
}

pub fn get_storage_status(device_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device = manager
        .devices
        .get(&device_id)
        .ok_or(StorageManagerError::InvalidDeviceID)?;

    let status = StorageStatus {
        device_id,
        device_name: device.device_name(),
        device_type: device.device_type(),
        irqs: device.irqs(),
        block_size: device.block_size(),
        num_blocks: device.num_blocks(),
    };

    Ok(status)
}

pub fn get_all_storage_statuses() -> Vec<StorageStatus> {
    let manager = STORAGE_MANAGER.read();

    let mut result = Vec::new();

    for id in manager.devices.keys() {
        if let Ok(status) = get_storage_status(*id) {
            result.push(status);
        }
    }

    result
}

pub fn get_device_namespace(device_id: u64) -> Option<u32> {
    let manager = STORAGE_MANAGER.read();

    let device = manager.devices.get(&device_id)?;
    device.get_namespace_id()
}

/// Service routine for storage device interrupt.
/// This routine should be called by interrupt handlers provided by device drivers.
pub fn storage_interrupt(irq: u16) {
    let mut node = MCSNode::new();
    let mut w = IRQ_WAKERS.lock(&mut node);

    match w.entry(irq) {
        Entry::Occupied(e) => {
            if matches!(e.get(), IRQWaker::Waker(_)) {
                let IRQWaker::Waker(w) = e.remove() else {
                    return;
                };

                w.wake();
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Interrupted);
        }
    }
}

/// Register a waker for a storage device interrupt service.
///
/// The old waker will be replaced.
/// The waker will be called when the storage device interrupt occurs once
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if the interrupt occurred before.
pub fn register_waker_for_storage_interrupt(irq: u16, waker: core::task::Waker) -> bool {
    let mut node = MCSNode::new();
    let mut w = IRQ_WAKERS.lock(&mut node);

    let entry = w.entry(irq);

    match entry {
        Entry::Occupied(mut e) => {
            if matches!(e.get(), IRQWaker::Interrupted) {
                e.remove();
                false
            } else {
                e.insert(IRQWaker::Waker(waker));
                true
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Waker(waker));
            true
        }
    }
}
