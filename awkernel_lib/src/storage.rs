use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use core::any::Any;

use crate::file::block_device::BlockResult;

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
    
    // Block device methods
    
    /// Get the block size in bytes
    fn block_size(&self) -> usize;
    
    /// Get a reference to self as Any for downcasting
    fn as_any(&self) -> &dyn Any;
    
    /// Get the total number of blocks  
    fn num_blocks(&self) -> u64;
    
    /// Read a single block into the provided buffer
    ///
    /// The buffer must be at least `block_size()` bytes.
    fn read_block(&self, block_num: u64, buf: &mut [u8]) -> BlockResult<()>;
    
    /// Write a single block from the provided buffer
    ///
    /// The buffer must be exactly `block_size()` bytes.
    fn write_block(&mut self, block_num: u64, buf: &[u8]) -> BlockResult<()>;
    
    /// Read multiple blocks into the provided buffer
    ///
    /// Default implementation calls `read_block` multiple times.
    fn read_blocks(&self, start_block: u64, num_blocks: u32, buf: &mut [u8]) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.read_block(start_block + i, &mut buf[offset..offset + block_size])?;
        }
        Ok(())
    }
    
    /// Write multiple blocks from the provided buffer
    ///
    /// Default implementation calls `write_block` multiple times.
    fn write_blocks(&mut self, start_block: u64, num_blocks: u32, buf: &[u8]) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.write_block(start_block + i, &buf[offset..offset + block_size])?;
        }
        Ok(())
    }
    
    /// Flush any cached writes to the device
    fn flush(&mut self) -> BlockResult<()> {
        Ok(())
    }
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


/// Get a reference to a storage device for block operations
pub fn get_block_device(interface_id: u64) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    manager
        .devices
        .get(&interface_id)
        .cloned()
        .ok_or(StorageManagerError::InvalidInterfaceID)
}