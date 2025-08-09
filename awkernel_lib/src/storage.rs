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
use core::sync::atomic::{AtomicBool, AtomicU16, Ordering};
use core::task::{Context, Poll, Waker};

use crate::file::block_device::BlockResult;

// Default timeout values for storage operations
pub const DEFAULT_IO_TIMEOUT_MS: u32 = 5000; // 5 seconds for I/O operations
pub const DEFAULT_TRANSFER_TIMEOUT_MS: u32 = 10000; // 10 seconds for transfers

#[derive(Debug)]
pub enum StorageManagerError {
    InvalidInterfaceID,
    InvalidTransferID,
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

/// Storage transfer structure for async I/O operations
pub struct StorageTransfer {
    pub nsid: u32,
    pub lba: u64,
    pub blocks: u32,
    pub read: bool,
    pub completed: AtomicBool,
    pub waker: Mutex<Option<Waker>>,
    pub status: AtomicU16,
    pub device_id: u64,
    pub poll: bool,
    pub timeout_ms: u32,
    pub start_time_ms: AtomicU64, // Time when transfer started (in milliseconds)
}

use core::sync::atomic::AtomicU64;

impl Default for StorageTransfer {
    fn default() -> Self {
        Self {
            nsid: 0,
            lba: 0,
            blocks: 0,
            read: true,
            completed: AtomicBool::new(false),
            waker: Mutex::new(None),
            status: AtomicU16::new(0),
            device_id: 0,
            poll: false,
            timeout_ms: DEFAULT_TRANSFER_TIMEOUT_MS,
            start_time_ms: AtomicU64::new(0),
        }
    }
}

/// Global storage transfer pool
pub struct StorageTransferPool {
    transfers: Vec<StorageTransfer>,
    free_list: Mutex<Vec<u16>>,
}

// Maximum number of concurrent transfers that can be allocated from the pool.
// This value is chosen to balance memory usage with concurrent I/O capability:
// - 256 allows for reasonable parallelism in multi-queue NVMe devices
// - Each transfer uses minimal memory (< 100 bytes)
// - Typical workloads rarely exceed 64 concurrent I/Os
// This could be made configurable in the future based on system requirements.
const MAX_TRANSFERS: usize = 256;

// Error message for uninitialized transfer pool
const POOL_NOT_INITIALIZED: &str =
    "Storage transfer pool not initialized. Call init_transfer_pool() first";

static STORAGE_TRANSFER_POOL: Mutex<Option<StorageTransferPool>> = Mutex::new(None);

/// Initialize the storage transfer pool
pub fn init_transfer_pool() {
    let mut node = MCSNode::new();
    let mut pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    if pool_guard.is_none() {
        let mut transfers = Vec::with_capacity(MAX_TRANSFERS);
        let mut free_list = Vec::with_capacity(MAX_TRANSFERS);

        for i in 0..MAX_TRANSFERS {
            transfers.push(StorageTransfer::default());
            free_list.push(i as u16);
        }

        *pool_guard = Some(StorageTransferPool {
            transfers,
            free_list: Mutex::new(free_list),
        });
    }
}

/// Allocate a transfer from the pool (synchronous)
pub fn allocate_transfer_sync(device_id: u64) -> Result<u16, StorageManagerError> {
    let mut node = MCSNode::new();
    let mut pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_mut() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    let mut free_node = MCSNode::new();
    let mut free_list = pool.free_list.lock(&mut free_node);

    if let Some(id) = free_list.pop() {
        // Reset the transfer
        let transfer = &mut pool.transfers[id as usize];
        transfer.completed.store(false, Ordering::Release);
        transfer.status.store(0, Ordering::Release);
        transfer.device_id = device_id;
        transfer.nsid = 0; // Will be set explicitly by caller

        // Clear waker
        let mut waker_node = MCSNode::new();
        let mut waker = transfer.waker.lock(&mut waker_node);
        *waker = None;

        Ok(id)
    } else {
        Err(StorageManagerError::DeviceError(
            StorageDevError::DeviceNotReady,
        ))
    }
}

/// Set transfer parameters
pub fn transfer_set_params(
    id: u16,
    lba: u64,
    blocks: u32,
    read: bool,
    nsid: u32,
) -> Result<(), StorageManagerError> {
    let mut node = MCSNode::new();
    let mut pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_mut() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &mut pool.transfers[id as usize];
    transfer.lba = lba;
    transfer.blocks = blocks;
    transfer.read = read;
    transfer.nsid = nsid;
    Ok(())
}

/// Set polling mode and timeout
pub fn transfer_set_poll_mode(
    id: u16,
    poll: bool,
    timeout_ms: u32,
) -> Result<(), StorageManagerError> {
    let mut node = MCSNode::new();
    let mut pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_mut() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &mut pool.transfers[id as usize];
    transfer.poll = poll;
    transfer.timeout_ms = timeout_ms;
    Ok(())
}

/// Get LBA
pub fn transfer_get_lba(id: u16) -> Result<u64, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].lba)
}

/// Get block count
pub fn transfer_get_blocks(id: u16) -> Result<u32, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].blocks)
}

/// Get namespace ID
pub fn transfer_get_nsid(id: u16) -> Result<u32, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].nsid)
}

/// Check if transfer is a read operation
pub fn transfer_is_read(id: u16) -> Result<bool, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].read)
}

/// Check if transfer is completed (atomic)
pub fn transfer_is_completed(id: u16) -> Result<bool, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize]
        .completed
        .load(Ordering::Acquire))
}

/// Get transfer status (atomic)
pub fn transfer_get_status(id: u16) -> Result<u16, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].status.load(Ordering::Acquire))
}

/// Mark transfer as completed with status (atomic)
pub fn transfer_mark_completed(id: u16, status: u16) -> Result<(), StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &pool.transfers[id as usize];
    transfer.status.store(status, Ordering::Release);
    transfer.completed.store(true, Ordering::Release);
    Ok(())
}

/// Set waker for async operations
pub fn transfer_set_waker(id: u16, waker: Option<Waker>) -> Result<(), StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let mut waker_node = MCSNode::new();
    let mut waker_guard = pool.transfers[id as usize].waker.lock(&mut waker_node);
    *waker_guard = waker;
    Ok(())
}

/// Check if transfer is in polling mode
pub fn transfer_is_poll_mode(id: u16) -> Result<bool, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].poll)
}

/// Get timeout in milliseconds
pub fn transfer_get_timeout_ms(id: u16) -> Result<u32, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].timeout_ms)
}

/// Get transfer info for validation (combines multiple fields for efficiency)
pub fn transfer_get_info(id: u16) -> Result<(u64, u32, u32, bool), StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &pool.transfers[id as usize];
    Ok((transfer.lba, transfer.blocks, transfer.nsid, transfer.read))
}

/// Free a transfer back to the pool
pub fn free_transfer(id: u16) {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    let mut free_node = MCSNode::new();
    let mut free_list = pool.free_list.lock(&mut free_node);

    free_list.push(id);
}

pub trait StorageDevice: Send + Sync {
    /// Get the device ID
    fn device_id(&self) -> u64;

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

/// Information about a registered storage device
struct DeviceInfo {
    device: Mutex<Arc<dyn StorageDevice>>,
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
/// The device is stored both as dyn StorageDevice and as its concrete type for downcasting
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
        device: Mutex::new(device.clone() as Arc<dyn StorageDevice>),
        namespace_id,
        // Store the concrete type for potential downcasting
        concrete_device: device.clone() as Arc<dyn Any + Send + Sync>,
    };
    manager.devices.insert(id, device_info);

    id
}

/// Downcast a storage device to its concrete type
/// Use this only when you need the concrete type (e.g., for FatFS mounting)
/// Returns None if the device doesn't exist or isn't of the requested type
pub fn downcast_storage_device<T: StorageDevice + Send + Sync + 'static>(
    interface_id: u64
) -> Option<Arc<T>> {
    let manager = STORAGE_MANAGER.read();
    
    manager.devices.get(&interface_id).and_then(|info| {
        // Attempt to downcast Arc<dyn Any> to Arc<T>
        Arc::downcast::<T>(info.concrete_device.clone()).ok()
    })
}

/// Get information about a storage device
pub fn get_storage_device(interface_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();

    let device_info = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;

    let mut node = MCSNode::new();
    let device_guard = device_info.device.lock(&mut node);
    let device = device_guard.as_ref();

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

    let Some(device_info) = manager.devices.get(&interface_id) else {
        return false;
    };

    let mut node = MCSNode::new();
    let device_guard = device_info.device.lock(&mut node);

    // Call the device's interrupt handler
    let _ = device_guard.as_ref().interrupt(irq);

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
        .map(|info| {
            let mut node = MCSNode::new();
            let device_guard = info.device.lock(&mut node);
            device_guard.clone()
        })
        .ok_or(StorageManagerError::InvalidInterfaceID)
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
    let device = get_block_device(device_id)?;
    Ok(device.block_size())
}

/// Check completed transfers and wake waiting tasks
pub fn wake_completed_transfers(device_id: u64) {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);

    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => panic!("{}", POOL_NOT_INITIALIZED),
    };

    let mut wakers_to_wake = Vec::new();

    // Scan transfers for completed ones
    for transfer in &pool.transfers {
        if transfer.device_id == device_id && transfer.completed.load(Ordering::Acquire) {
            let mut waker_node = MCSNode::new();
            let mut waker_guard = transfer.waker.lock(&mut waker_node);
            if let Some(waker) = waker_guard.take() {
                wakers_to_wake.push(waker);
            }
        }
    }

    // Drop the lock before waking
    drop(pool_guard);

    // Wake all collected tasks
    for waker in wakers_to_wake {
        waker.wake();
    }
}

/// Future for waiting on transfer completion with timeout support
struct TransferCompletionFuture {
    transfer_id: u16,
    poll_count: u32, // Track number of polls for timeout
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
        let completed = transfer_is_completed(self.transfer_id)?;

        if completed {
            let status = transfer_get_status(self.transfer_id)?;
            if status == 0 {
                // Success
                Poll::Ready(Ok(()))
            } else {
                Poll::Ready(Err(StorageManagerError::DeviceError(
                    StorageDevError::IoError,
                )))
            }
        } else {
            // For polling mode, check timeout based on poll iterations
            // Each poll represents roughly 1ms of waiting in typical async runtime
            let is_poll = transfer_is_poll_mode(self.transfer_id)?;
            if is_poll {
                self.poll_count += 1;
                let timeout_ms = transfer_get_timeout_ms(self.transfer_id)?;
                // Convert timeout_ms to approximate poll iterations
                if self.poll_count > timeout_ms {
                    // Mark transfer as timed out
                    transfer_mark_completed(self.transfer_id, 1)?; // Non-zero indicates error
                    return Poll::Ready(Err(StorageManagerError::DeviceError(
                        StorageDevError::IoError,
                    )));
                }
            }

            // Register waker for IRQ handler task to use
            transfer_set_waker(self.transfer_id, Some(cx.waker().clone()))?;
            Poll::Pending
        }
    }
}

/// Async wrapper for allocating a transfer
pub async fn allocate_transfer(device_id: u64) -> Result<u16, StorageManagerError> {
    // For now, just use sync version
    // Could be made truly async if pool is exhausted
    allocate_transfer_sync(device_id)
}

/// Common async I/O operation logic
async fn async_io_operation(
    device_id: u64,
    start_lba: u64,
    buf_len: usize,
    is_read: bool,
    io_fn: impl FnOnce(Arc<dyn StorageDevice>, u16) -> BlockResult<()>,
) -> Result<(), StorageManagerError> {
    // Get block size to calculate number of blocks
    let block_size = get_device_block_size(device_id)?;

    // Calculate number of blocks from buffer size
    let num_blocks = buf_len / block_size;
    if buf_len % block_size != 0 {
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }

    // Allocate transfer
    let transfer_id = allocate_transfer(device_id).await?;

    // Ensure transfer is freed on all paths
    let result = async {
        // Set up the transfer metadata with correct number of blocks
        let nsid = get_device_namespace(device_id).unwrap_or(0);
        transfer_set_params(transfer_id, start_lba, num_blocks as u32, is_read, nsid)?;

        // Get device and perform I/O operation
        let device = get_block_device(device_id)?;
        io_fn(device, transfer_id)
            .map_err(|_| StorageManagerError::DeviceError(StorageDevError::IoError))?;

        // Wait for completion
        TransferCompletionFuture::new(transfer_id).await?;

        Ok(())
    }
    .await;

    // Always free transfer
    free_transfer(transfer_id);
    result
}

/// Async read operation (handles both single and multi-block)
/// Buffer size determines number of blocks to read
pub async fn async_read_block(
    device_id: u64,
    start_lba: u64, // Renamed for clarity
    buf: &mut [u8],
) -> Result<(), StorageManagerError> {
    async_io_operation(
        device_id,
        start_lba,
        buf.len(),
        true,
        |device, transfer_id| device.read_blocks(buf, transfer_id),
    )
    .await
}

/// Async write operation (handles both single and multi-block)
/// Buffer size determines number of blocks to write
pub async fn async_write_block(
    device_id: u64,
    start_lba: u64, // Renamed for clarity
    buf: &[u8],
) -> Result<(), StorageManagerError> {
    async_io_operation(
        device_id,
        start_lba,
        buf.len(),
        false,
        |device, transfer_id| device.write_blocks(buf, transfer_id),
    )
    .await
}
