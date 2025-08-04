use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};

use crate::file::block_device::BlockDevice;

#[derive(Debug)]
pub enum StorageManagerError {
    InvalidInterfaceID,
    DeviceError(StorageDevError),
    NotYetImplemented,
}

#[derive(Debug)]
pub enum StorageDevError {
    IoError,
    InvalidCommand,
    DeviceNotReady,
}

#[derive(Debug)]
pub struct StorageStatus {
    pub interface_id: u64,
    pub device_name: Cow<'static, str>,
    pub device_type: StorageDeviceType,
    pub irqs: Vec<u16>,
    pub block_size: usize,
    pub num_blocks: u64,
    pub is_ready: bool,
}

#[derive(Debug, Clone, Copy)]
pub enum StorageDeviceType {
    NVMe,
    SATA,
    USB,
    VirtIO,
}

pub trait StorageDevice: BlockDevice + Send + Sync {
    /// Get the device name
    fn device_name(&self) -> Cow<'static, str>;
    
    /// Get the device short name (e.g., "nvme0")
    fn device_short_name(&self) -> Cow<'static, str>;
    
    /// Get the device type
    fn device_type(&self) -> StorageDeviceType;
    
    /// Get list of IRQs used by this device
    fn irqs(&self) -> Vec<u16>;
    
    /// Handle an interrupt for this device
    fn interrupt(&self, irq: u16) -> Result<(), StorageDevError>;
    
    /// Check if the device is ready for I/O
    fn is_ready(&self) -> bool;
    
    /// Bring the device up (enable it)
    fn up(&self) -> Result<(), StorageDevError>;
    
    /// Bring the device down (disable it)
    fn down(&self) -> Result<(), StorageDevError>;
}

static STORAGE_MANAGER: RwLock<StorageManager> = RwLock::new(StorageManager {
    devices: BTreeMap::new(),
    interface_id: 0,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

pub struct StorageManager {
    devices: BTreeMap<u64, Arc<dyn StorageDevice>>,
    interface_id: u64,
}

enum IRQWaker {
    Waker(core::task::Waker),
    Interrupted,
}

/// Add a storage device to the manager
pub fn add_storage_device(device: Arc<dyn StorageDevice>) -> u64 {
    let mut manager = STORAGE_MANAGER.write();
    
    if manager.interface_id == u64::MAX {
        panic!("storage interface id overflow");
    }
    
    let id = manager.interface_id;
    manager.interface_id += 1;
    
    manager.devices.insert(id, device);
    
    id
}

/// Get information about a storage device
pub fn get_storage_device(interface_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let device = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;
    
    let status = StorageStatus {
        interface_id,
        device_name: device.device_name(),
        device_type: device.device_type(),
        irqs: device.irqs(),
        block_size: device.block_size(),
        num_blocks: device.num_blocks(),
        is_ready: device.is_ready(),
    };
    
    Ok(status)
}

/// Get all storage devices
pub fn get_all_storage_devices() -> Vec<StorageStatus> {
    let manager = STORAGE_MANAGER.read();
    
    let mut result = Vec::new();
    
    for id in manager.devices.keys() {
        if let Ok(status) = get_storage_device(*id) {
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

/// Handle a storage interrupt
/// Returns true if more work is pending
pub fn handle_storage_interrupt(interface_id: u64, irq: u16) -> bool {
    let manager = STORAGE_MANAGER.read();
    
    let Some(device) = manager.devices.get(&interface_id) else {
        return false;
    };
    
    // Call the device's interrupt handler
    let _ = device.interrupt(irq);
    
    // For now, assume no more work is pending
    // Individual drivers can implement more sophisticated logic
    false
}

/// Enable a storage device
pub fn up(interface_id: u64) -> Result<(), StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let Some(device) = manager.devices.get(&interface_id) else {
        return Err(StorageManagerError::InvalidInterfaceID);
    };
    
    device.up().map_err(StorageManagerError::DeviceError)
}

/// Disable a storage device
pub fn down(interface_id: u64) -> Result<(), StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let Some(device) = manager.devices.get(&interface_id) else {
        return Err(StorageManagerError::InvalidInterfaceID);
    };
    
    device.down().map_err(StorageManagerError::DeviceError)
}

/// Get a reference to a storage device for block operations
pub fn get_block_device(interface_id: u64) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    manager
        .devices
        .get(&interface_id)
        .cloned()
        .ok_or(StorageManagerError::InvalidInterfaceID)
}