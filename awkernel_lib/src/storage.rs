mod transfer;

// Re-export commonly used transfer functions
pub use transfer::{
    allocate_transfer, free_transfer, init_transfer_pool, transfer_get_blocks, transfer_get_info,
    transfer_get_lba, transfer_get_nsid, transfer_get_status, transfer_get_timeout_ms,
    transfer_is_completed, transfer_is_poll_mode, transfer_is_read, transfer_mark_completed,
    transfer_set_params, transfer_set_poll_mode, transfer_set_waker, wake_completed_transfers,
    DEFAULT_IO_TIMEOUT_MS, DEFAULT_TRANSFER_TIMEOUT_MS,
};

use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use core::any::Any;
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};

use crate::file::block_device_adapter::BlockResult;

#[derive(Debug)]
pub enum StorageManagerError {
    InvalidInterfaceID,
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
    fn device_id(&self) -> u64;

    fn device_name(&self) -> Cow<'static, str>;

    fn device_short_name(&self) -> Cow<'static, str>;

    fn device_type(&self) -> StorageDeviceType;

    fn irqs(&self) -> Vec<u16>;

    fn interrupt(&self, irq: u16) -> Result<(), StorageDevError>;

    fn block_size(&self) -> usize;

    /// Get a reference to self as Any for downcasting
    fn as_any(&self) -> &dyn Any;

    /// Get the total number of blocks  
    fn num_blocks(&self) -> u64;

    /// Read blocks into the provided buffer
    ///
    /// The buffer must be at least `block_size() * transfer.blocks` bytes.
    /// For single block operations, set transfer.blocks = 1.
    /// transfer_id: Pre-allocated transfer ID with parameters already set
    fn read_blocks(&self, buf: &mut [u8], transfer_id: u16) -> BlockResult<()>;

    /// Write blocks from the provided buffer
    ///
    /// The buffer must be exactly `block_size() * transfer.blocks` bytes.
    /// For single block operations, set transfer.blocks = 1.
    /// transfer_id: Pre-allocated transfer ID with parameters already set
    fn write_blocks(&self, buf: &[u8], transfer_id: u16) -> BlockResult<()>;

    /// Flush any cached writes to the device
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn flush(&self, _transfer_id: u16) -> BlockResult<()> {
        Ok(())
    }
}

static STORAGE_MANAGER: RwLock<StorageManager> = RwLock::new(StorageManager {
    devices: BTreeMap::new(),
    interface_id: 0,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

struct DeviceInfo {
    device: Arc<dyn StorageDevice>,
    namespace_id: Option<u32>,
    // Store the concrete type for downcasting when needed (e.g., for FatFS)
    concrete_device: Arc<dyn Any + Send + Sync>,
}

pub struct StorageManager {
    devices: BTreeMap<u64, DeviceInfo>,
    interface_id: u64,
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

    if manager.interface_id == u64::MAX {
        panic!("storage interface id overflow");
    }

    let id = manager.interface_id;
    manager.interface_id += 1;

    let device_info = DeviceInfo {
        device: device.clone() as Arc<dyn StorageDevice>,
        namespace_id,
        // Store the concrete type for potential downcasting
        concrete_device: device.clone() as Arc<dyn Any + Send + Sync>,
    };
    manager.devices.insert(id, device_info);

    id
}

/// Get a storage device as Arc<dyn StorageDevice>
pub fn get_storage_device(
    interface_id: u64,
) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device_info = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;

    Ok(device_info.device.clone())
}

/// Downcast a storage device to its concrete type
pub fn downcast_storage_device<T: StorageDevice + Send + Sync + 'static>(
    interface_id: u64,
) -> Option<Arc<T>> {
    let manager = STORAGE_MANAGER.read();

    manager.devices.get(&interface_id).and_then(|info| {
        // Attempt to downcast Arc<dyn Any> to Arc<T>
        Arc::downcast::<T>(info.concrete_device.clone()).ok()
    })
}

/// Get status information about a storage device
pub fn get_storage_status(interface_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device_info = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;

    let device = &device_info.device;

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

/// Handle a storage interrupt
/// Returns true if more work is pending
pub fn handle_storage_interrupt(interface_id: u64, irq: u16) -> bool {
    let manager = STORAGE_MANAGER.read();

    let Some(device_info) = manager.devices.get(&interface_id) else {
        return false;
    };

    // Call the device's interrupt handler
    let _ = device_info.device.interrupt(irq);

    // Drop the manager lock before waking tasks to avoid potential deadlocks
    drop(manager);

    // Wake any async tasks waiting on completed transfers for this device
    // interface_id is the same as device_id for storage devices
    wake_completed_transfers(interface_id);

    // For now, assume no more work is pending
    // Individual drivers can implement more sophisticated logic
    false
}

/// Get the namespace ID for a storage device
pub fn get_device_namespace(device_id: u64) -> Option<u32> {
    let manager = STORAGE_MANAGER.read();

    manager
        .devices
        .get(&device_id)
        .and_then(|info| info.namespace_id)
}

/// Get the block size for a storage device
pub fn get_device_block_size(device_id: u64) -> Result<usize, StorageManagerError> {
    let device = get_storage_device(device_id)?;
    Ok(device.block_size())
}

/// Future for waiting on transfer completion
struct TransferCompletionFuture {
    transfer_id: u16,
    poll_count: u32,
}

impl TransferCompletionFuture {
    fn new(transfer_id: u16) -> Self {
        Self {
            transfer_id,
            poll_count: 0,
        }
    }
}

impl Future for TransferCompletionFuture {
    type Output = Result<(), StorageManagerError>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        self.poll_count += 1;

        // Register waker first - this ensures the interrupt handler can wake us
        // if the transfer completes after we check
        transfer_set_waker(self.transfer_id, Some(cx.waker().clone()))?;

        // Check if transfer is completed
        let completed = transfer_is_completed(self.transfer_id)?;

        if completed {
            let status = transfer_get_status(self.transfer_id)?;
            if status == 0 {
                Poll::Ready(Ok(()))
            } else {
                Poll::Ready(Err(StorageManagerError::DeviceError(
                    StorageDevError::IoError,
                )))
            }
        } else {
            // For polling mode timeout check
            let is_poll = transfer_is_poll_mode(self.transfer_id)?;
            if is_poll {
                let timeout_ms = transfer_get_timeout_ms(self.transfer_id)?;
                if self.poll_count > timeout_ms {
                    transfer_mark_completed(self.transfer_id, 1)?;
                    return Poll::Ready(Err(StorageManagerError::DeviceError(
                        StorageDevError::IoError,
                    )));
                }
            }

            Poll::Pending
        }
    }
}

pub async fn async_read_block(
    device_id: u64,
    start_lba: u64,
    buf: &mut [u8],
) -> Result<(), StorageManagerError> {
    let block_size = get_device_block_size(device_id)?;
    let num_blocks = buf.len() / block_size;
    if buf.len() % block_size != 0 {
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }

    let transfer_id = allocate_transfer(device_id)?;
    let nsid = get_device_namespace(device_id).unwrap_or(0);
    transfer_set_params(transfer_id, start_lba, num_blocks as u32, true, nsid)?;

    let device = get_storage_device(device_id)?;
    let submit_result = device.read_blocks(buf, transfer_id);

    if submit_result.is_err() {
        transfer_mark_completed(transfer_id, 1)?; // Non-zero = error
        let _ = free_transfer(transfer_id);
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }

    let completion_future = TransferCompletionFuture::new(transfer_id);
    let result = completion_future.await;

    // Always free transfer
    let _ = free_transfer(transfer_id);
    result
}

pub async fn async_write_block(
    device_id: u64,
    start_lba: u64,
    buf: &[u8],
) -> Result<(), StorageManagerError> {
    let block_size = get_device_block_size(device_id)?;
    let num_blocks = buf.len() / block_size;
    if buf.len() % block_size != 0 {
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }

    let transfer_id = allocate_transfer(device_id)?;
    let nsid = get_device_namespace(device_id).unwrap_or(0);
    transfer_set_params(transfer_id, start_lba, num_blocks as u32, false, nsid)?;

    let device = get_storage_device(device_id)?;
    let submit_result = device.write_blocks(buf, transfer_id);

    if submit_result.is_err() {
        transfer_mark_completed(transfer_id, 1)?; // Non-zero = error
        let _ = free_transfer(transfer_id);
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }

    let completion_future = TransferCompletionFuture::new(transfer_id);
    let result = completion_future.await;

    let _ = free_transfer(transfer_id);

    result
}
