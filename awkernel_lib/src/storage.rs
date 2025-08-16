mod transfer;

// Re-export commonly used transfer functions
pub use transfer::{
    allocate_transfer, free_transfer, init_transfer_pool, transfer_get_blocks,
    transfer_get_info, transfer_get_lba, transfer_get_nsid, transfer_get_status,
    transfer_get_timeout_ms, transfer_is_completed, transfer_is_poll_mode, transfer_is_read,
    transfer_mark_completed, transfer_set_params, transfer_set_poll_mode, transfer_set_waker,
    wake_completed_transfers, StorageOp, StorageRequest, DEFAULT_IO_TIMEOUT_MS, DEFAULT_TRANSFER_TIMEOUT_MS,
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
use core::slice;
use core::task::{Context, Poll, Waker};

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
    device: Arc<dyn StorageDevice>,
    namespace_id: Option<u32>,
    // Store the concrete type for downcasting when needed (e.g., for FatFS)
    concrete_device: Arc<dyn Any + Send + Sync>,
    // Request queue for this device
    request_queue: Arc<Mutex<RequestQueue>>,
}

pub struct StorageManager {
    devices: BTreeMap<u64, DeviceInfo>,
    interface_id: u64,
}

/// Simple request queue for storage devices
pub struct RequestQueue {
    requests: Vec<StorageRequest>,
    waker: Option<Waker>,
}

impl RequestQueue {
    pub fn new() -> Self {
        Self {
            requests: Vec::new(),
            waker: None,
        }
    }
    
    pub fn push(&mut self, request: StorageRequest) {
        self.requests.push(request);
    }
    
    pub fn wake_if_waiting(&mut self) {
        if let Some(waker) = self.waker.take() {
            waker.wake();
        }
    }
    
    pub fn pop(&mut self) -> Option<StorageRequest> {
        if self.requests.is_empty() {
            None
        } else {
            Some(self.requests.remove(0))
        }
    }
    
    pub fn set_waker(&mut self, waker: Waker) {
        self.waker = Some(waker);
    }
}

/// Future for waiting on the next request from the queue
pub struct RequestQueueFuture {
    queue: Arc<Mutex<RequestQueue>>,
}

impl RequestQueueFuture {
    pub fn new(queue: Arc<Mutex<RequestQueue>>) -> Self {
        Self { queue }
    }
}

impl Future for RequestQueueFuture {
    type Output = StorageRequest;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);
        
        if let Some(request) = queue.pop() {
            Poll::Ready(request)
        } else {
            queue.set_waker(cx.waker().clone());
            Poll::Pending
        }
    }
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
        device: device.clone() as Arc<dyn StorageDevice>,
        namespace_id,
        // Store the concrete type for potential downcasting
        concrete_device: device.clone() as Arc<dyn Any + Send + Sync>,
        request_queue: Arc::new(Mutex::new(RequestQueue::new())),
    };
    manager.devices.insert(id, device_info);

    id
}

/// Get a storage device as Arc<dyn StorageDevice>
/// This allows working with any device type without knowing the concrete type
pub fn get_storage_device(interface_id: u64) -> Result<Arc<dyn StorageDevice>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let device_info = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;
    
    Ok(device_info.device.clone())
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

// Note: get_block_device has been removed as it's redundant with get_storage_device

/// Get the namespace ID for a storage device
pub fn get_device_namespace(device_id: u64) -> Option<u32> {
    let manager = STORAGE_MANAGER.read();

    manager
        .devices
        .get(&device_id)
        .and_then(|info| info.namespace_id)
}

/// Queue a storage request for a device
pub fn queue_storage_request(device_id: u64, request: StorageRequest) -> Result<(), StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let device_info = manager.devices.get(&device_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;
    
    let mut node = MCSNode::new();
    let mut queue = device_info.request_queue.lock(&mut node);
    queue.push(request);
    
    // Explicitly wake the submission task if it's waiting for requests
    queue.wake_if_waiting();
    
    Ok(())
}

/// Get the request queue for a device (for the submission task)
pub fn get_device_request_queue(device_id: u64) -> Option<Arc<Mutex<RequestQueue>>> {
    let manager = STORAGE_MANAGER.read();
    manager.devices.get(&device_id).map(|info| info.request_queue.clone())
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
        
        // Always register waker first - this ensures the interrupt handler can wake us
        transfer_set_waker(self.transfer_id, Some(cx.waker().clone()))?;
        
        // Check if already completed
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
            // Check completion again after registering waker
            // This handles the case where I/O completes between the initial check
            // and waker registration (especially in polling mode)
            let completed_after_waker = transfer_is_completed(self.transfer_id)?;
            
            if completed_after_waker {
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
}


/// Common async I/O operation logic
async fn _async_io_operation(
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
    let transfer_id = allocate_transfer(device_id)?;

    // Ensure transfer is freed on all paths
    let result = async {
        // Set up the transfer metadata with correct number of blocks
        let nsid = get_device_namespace(device_id).unwrap_or(0);
        transfer_set_params(transfer_id, start_lba, num_blocks as u32, is_read, nsid)?;

        // Get device and perform I/O operation
        let device = get_storage_device(device_id)?;
        io_fn(device, transfer_id)
            .map_err(|_| StorageManagerError::DeviceError(StorageDevError::IoError))?;

        // Wait for completion
        TransferCompletionFuture::new(transfer_id).await?;

        Ok(())
    }
    .await;

    // Always free transfer
    let _ = free_transfer(transfer_id);
    result
}

/// Async read operation (handles both single and multi-block)
/// Buffer size determines number of blocks to read
pub async fn async_read_block(
    device_id: u64,
    start_lba: u64, // Renamed for clarity
    buf: &mut [u8],
) -> Result<(), StorageManagerError> {
    // Get block size to calculate number of blocks
    let block_size = get_device_block_size(device_id)?;
    
    // Calculate number of blocks from buffer size
    let num_blocks = buf.len() / block_size;
    if buf.len() % block_size != 0 {
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }
    
    // Allocate transfer
    let transfer_id = allocate_transfer(device_id)?;
    
    // Set up the transfer metadata
    let nsid = get_device_namespace(device_id).unwrap_or(0);
    transfer_set_params(transfer_id, start_lba, num_blocks as u32, true, nsid)?;
    
    // For now, we'll rely on the completion future registering the waker directly
    // The submission task will yield to ensure the future gets polled
    
    // Queue the request to the submission task
    let request = StorageRequest {
        transfer_id,
        device_id,
        operation: StorageOp::Read { 
            buf_ptr: buf.as_mut_ptr(),
            buf_len: buf.len(),
        },
        waker: None,
    };
    
    queue_storage_request(device_id, request)?;
    
    // Create completion future that will register its waker
    let completion_future = TransferCompletionFuture::new(transfer_id);
    
    // Wait for completion
    let result = completion_future.await;
    
    // Always free transfer
    let _ = free_transfer(transfer_id);
    result
}

/// Async write operation (handles both single and multi-block)
/// Buffer size determines number of blocks to write
pub async fn async_write_block(
    device_id: u64,
    start_lba: u64, // Renamed for clarity
    buf: &[u8],
) -> Result<(), StorageManagerError> {
    // Get block size to calculate number of blocks
    let block_size = get_device_block_size(device_id)?;
    
    // Calculate number of blocks from buffer size
    let num_blocks = buf.len() / block_size;
    if buf.len() % block_size != 0 {
        return Err(StorageManagerError::DeviceError(StorageDevError::IoError));
    }
    
    // Allocate transfer
    let transfer_id = allocate_transfer(device_id)?;
    
    // Set up the transfer metadata
    let nsid = get_device_namespace(device_id).unwrap_or(0);
    transfer_set_params(transfer_id, start_lba, num_blocks as u32, false, nsid)?;
    
    // For now, we'll rely on the completion future registering the waker directly
    // The submission task will yield to ensure the future gets polled
    
    // Queue the request to the submission task
    let request = StorageRequest {
        transfer_id,
        device_id,
        operation: StorageOp::Write { 
            buf_ptr: buf.as_ptr(),
            buf_len: buf.len(),
        },
        waker: None,
    };
    
    queue_storage_request(device_id, request)?;
    
    // Create completion future that will register its waker
    let completion_future = TransferCompletionFuture::new(transfer_id);
    
    // Wait for completion
    let result = completion_future.await;
    
    // Always free transfer
    let _ = free_transfer(transfer_id);
    
    result
}

/// Storage submission task - processes requests from the queue
/// This task should be spawned once per storage device
pub async fn storage_submission_task(device_id: u64) {
    log::info!("Starting storage submission task for device {}", device_id);
    
    // Get the request queue for this device
    let queue = match get_device_request_queue(device_id) {
        Some(q) => q,
        None => {
            log::error!("No request queue found for device {}", device_id);
            return;
        }
    };
    
    // Get the device once
    let device = match get_storage_device(device_id) {
        Ok(d) => d,
        Err(e) => {
            log::error!("Failed to get storage device {}: {:?}", device_id, e);
            return;
        }
    };
    
    // Process requests forever
    loop {
        // Wait for the next request
        let request = RequestQueueFuture::new(queue.clone()).await;
        
        // The completion future should have been polled at least once by now,
        // which would have registered its waker. If not, the I/O completion
        // will still mark the transfer as complete, and the future will see
        // this when it's eventually polled.
        let result = match request.operation {
            StorageOp::Read { buf_ptr, buf_len } => {
                // SAFETY: The buffer pointer is valid for the duration of the async operation
                // The caller ensures the buffer remains valid until completion
                let buf = unsafe { slice::from_raw_parts_mut(buf_ptr, buf_len) };
                device.read_blocks(buf, request.transfer_id)
            }
            StorageOp::Write { buf_ptr, buf_len } => {
                // SAFETY: The buffer pointer is valid for the duration of the async operation
                let buf = unsafe { slice::from_raw_parts(buf_ptr, buf_len) };
                device.write_blocks(buf, request.transfer_id)
            }
            StorageOp::Flush => {
                device.flush(request.transfer_id)
            }
        };
        
        // If submission failed, mark the transfer as failed
        if result.is_err() {
            log::error!("Failed to submit I/O for transfer {}", request.transfer_id);
            let _ = transfer_mark_completed(request.transfer_id, 1); // Non-zero = error
        }
        
        // Hardware will complete the I/O and interrupt will wake the waiting task
    }
}
