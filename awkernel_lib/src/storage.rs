use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};

#[derive(Debug)]
pub enum StorageManagerError {
    InvalidDeviceID,
    InvalidTransferID,
    DeviceError(StorageDevError),
    NotYetImplemented,
    PoolNotInitialized,
}

#[derive(Debug)]
pub enum StorageDevError {
    IoError,
    InvalidCommand,
    DeviceNotReady,
    InvalidBlock,
    BufferTooSmall,
    NotSupported,
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

#[derive(Debug, Clone, Copy)]
pub enum StorageDeviceType {
    NVMe,
    SATA,
    USB,
    VirtIO,
    Memory,
}

pub trait StorageDevice: Send + Sync {
    fn device_id(&self) -> u64;

    fn device_name(&self) -> Cow<'static, str>;

    fn device_short_name(&self) -> Cow<'static, str>;

    fn device_type(&self) -> StorageDeviceType;

    fn irqs(&self) -> Vec<u16>;

    fn interrupt(&self, irq: u16) -> Result<(), StorageDevError>;

    fn block_size(&self) -> usize;

    /// Get the total number of blocks  
    fn num_blocks(&self) -> u64;

    fn read_blocks(&self, buf: &mut [u8], transfer_id: u16) -> Result<(), StorageDevError>;

    fn write_blocks(&self, buf: &[u8], transfer_id: u16) -> Result<(), StorageDevError>;

    fn flush(&self, _transfer_id: u16) -> Result<(), StorageDevError> {
        Ok(())
    }
}

static STORAGE_MANAGER: RwLock<StorageManager> = RwLock::new(StorageManager {
    devices: BTreeMap::new(),
    device_id: 0,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

struct DeviceInfo {
    device: Arc<dyn StorageDevice>,
    _namespace_id: Option<u32>,
}

pub struct StorageManager {
    devices: BTreeMap<u64, DeviceInfo>,
    device_id: u64,
}

enum IRQWaker {
    Waker(core::task::Waker),
    Interrupted,
}

/// Add a storage device to the manager
pub fn add_storage_device<T>(device: Arc<T>, namespace_id: Option<u32>) -> u64
where
    T: StorageDevice + Send + Sync + 'static,
{
    let mut manager = STORAGE_MANAGER.write();

    if manager.device_id == u64::MAX {
        panic!("storage device id overflow");
    }

    let id = manager.device_id;
    manager.device_id += 1;

    let device_info = DeviceInfo {
        device: device.clone() as Arc<dyn StorageDevice>,
        _namespace_id: namespace_id,
    };
    manager.devices.insert(id, device_info);

    id
}

/// Get a storage device as Arc<dyn StorageDevice>
pub fn get_storage_device(device_id: u64) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device_info = manager
        .devices
        .get(&device_id)
        .ok_or(StorageManagerError::InvalidDeviceID)?;

    Ok(device_info.device.clone())
}

/// Get status information about a storage device
pub fn get_storage_status(device_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device_info = manager
        .devices
        .get(&device_id)
        .ok_or(StorageManagerError::InvalidDeviceID)?;

    let device = &device_info.device;

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

/// Get status information for all storage devices
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
