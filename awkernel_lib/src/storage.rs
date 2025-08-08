use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use core::any::Any;
use core::sync::atomic::{AtomicBool, AtomicU16, Ordering};
use core::task::{Context, Poll, Waker};
use core::pin::Pin;
use core::future::Future;

use crate::file::block_device::BlockResult;
use crate::dma_map::DmaMap;

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

/// Storage transfer structure for async I/O operations
pub struct StorageTransfer {
    pub nsid: u32,
    pub lba: u64,
    pub blocks: u32,
    pub dmamap: Option<DmaMap>,
    pub read: bool,
    pub completed: AtomicBool,
    pub waker: Mutex<Option<Waker>>,
    pub status: AtomicU16,
    pub device_id: u64,
    pub poll: bool,
    pub timeout_ms: u32,
}

impl Default for StorageTransfer {
    fn default() -> Self {
        Self {
            nsid: 0,
            lba: 0,
            blocks: 0,
            dmamap: None,
            read: true,
            completed: AtomicBool::new(false),
            waker: Mutex::new(None),
            status: AtomicU16::new(0),
            device_id: 0,
            poll: false,
            timeout_ms: 10000,  // Default 10 second timeout
        }
    }
}

/// Global storage transfer pool
pub struct StorageTransferPool {
    transfers: Vec<StorageTransfer>,
    free_list: Mutex<Vec<u16>>,
}

const MAX_TRANSFERS: usize = 256;
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
        None => return Err(StorageManagerError::NotYetImplemented),
    };
    
    let mut free_node = MCSNode::new();
    let mut free_list = pool.free_list.lock(&mut free_node);
    
    if let Some(id) = free_list.pop() {
        // Reset the transfer
        let transfer = &mut pool.transfers[id as usize];
        transfer.completed.store(false, Ordering::Release);
        transfer.status.store(0, Ordering::Release);
        transfer.device_id = device_id;
        
        // Clear waker
        let mut waker_node = MCSNode::new();
        let mut waker = transfer.waker.lock(&mut waker_node);
        *waker = None;
        
        Ok(id)
    } else {
        Err(StorageManagerError::DeviceError(StorageDevError::DeviceNotReady))
    }
}

/// Get a transfer by ID
pub fn get_transfer(id: u16) -> Result<&'static StorageTransfer, StorageManagerError> {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);
    
    let pool = match pool_guard.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::NotYetImplemented),
    };
    
    if (id as usize) < pool.transfers.len() {
        // SAFETY: We return a static reference that is valid as long as the pool exists
        // The pool is never deallocated once created
        unsafe {
            let transfer_ptr = &pool.transfers[id as usize] as *const StorageTransfer;
            Ok(&*transfer_ptr)
        }
    } else {
        Err(StorageManagerError::InvalidInterfaceID)
    }
}

/// Get a mutable transfer by ID
pub fn get_transfer_mut(id: u16) -> Result<&'static mut StorageTransfer, StorageManagerError> {
    let mut node = MCSNode::new();
    let mut pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);
    
    let pool = match pool_guard.as_mut() {
        Some(p) => p,
        None => return Err(StorageManagerError::NotYetImplemented),
    };
    
    if (id as usize) < pool.transfers.len() {
        // SAFETY: We return a static mutable reference that is valid as long as the pool exists
        // The pool is never deallocated once created, and we ensure exclusive access
        unsafe {
            let transfer_ptr = &mut pool.transfers[id as usize] as *mut StorageTransfer;
            Ok(&mut *transfer_ptr)
        }
    } else {
        Err(StorageManagerError::InvalidInterfaceID)
    }
}

/// Free a transfer back to the pool
pub fn free_transfer(id: u16) {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);
    
    if let Some(pool) = pool_guard.as_ref() {
        let mut free_node = MCSNode::new();
        let mut free_list = pool.free_list.lock(&mut free_node);
        
        // Clear the transfer's DMA map
        if let Ok(transfer) = get_transfer_mut(id) {
            transfer.dmamap = None;
        }
        
        free_list.push(id);
    }
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
    
    /// Read a single block into the provided buffer
    ///
    /// The buffer must be at least `block_size()` bytes.
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn read_block(&self, block_num: u64, buf: &mut [u8], transfer_id: u16) -> BlockResult<()>;
    
    /// Write a single block from the provided buffer
    ///
    /// The buffer must be exactly `block_size()` bytes.
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn write_block(&mut self, block_num: u64, buf: &[u8], transfer_id: u16) -> BlockResult<()>;
    
    /// Read multiple blocks into the provided buffer
    ///
    /// Default implementation calls `read_block` multiple times.
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn read_blocks(&self, start_block: u64, num_blocks: u32, buf: &mut [u8], transfer_id: u16) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.read_block(start_block + i, &mut buf[offset..offset + block_size], transfer_id)?;
        }
        Ok(())
    }
    
    /// Write multiple blocks from the provided buffer
    ///
    /// Default implementation calls `write_block` multiple times.
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn write_blocks(&mut self, start_block: u64, num_blocks: u32, buf: &[u8], transfer_id: u16) -> BlockResult<()> {
        let block_size = self.block_size();
        for i in 0..num_blocks as u64 {
            let offset = (i as usize) * block_size;
            self.write_block(start_block + i, &buf[offset..offset + block_size], transfer_id)?;
        }
        Ok(())
    }
    
    /// Flush any cached writes to the device
    /// transfer_id: Pre-allocated transfer ID for tracking the operation
    fn flush(&mut self, _transfer_id: u16) -> BlockResult<()> {
        Ok(())
    }
}

static STORAGE_MANAGER: RwLock<StorageManager> = RwLock::new(StorageManager {
    devices: BTreeMap::new(),
    interface_id: 0,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

pub struct StorageManager {
    devices: BTreeMap<u64, Arc<Mutex<Arc<dyn StorageDevice>>>>,
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
    
    // Wrap the Arc<dyn StorageDevice> in a Mutex
    let mutex_device = Arc::new(Mutex::new(device));
    manager.devices.insert(id, mutex_device);
    
    id
}

/// Get information about a storage device
pub fn get_storage_device(interface_id: u64) -> Result<StorageStatus, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    let device_mutex = manager
        .devices
        .get(&interface_id)
        .ok_or(StorageManagerError::InvalidInterfaceID)?;
    
    let mut node = MCSNode::new();
    let device_guard = device_mutex.lock(&mut node);
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
    
    let Some(device_mutex) = manager.devices.get(&interface_id) else {
        return false;
    };
    
    let mut node = MCSNode::new();
    let device_guard = device_mutex.lock(&mut node);
    
    // Call the device's interrupt handler
    let _ = device_guard.as_ref().interrupt(irq);
    
    // For now, assume no more work is pending
    // Individual drivers can implement more sophisticated logic
    false
}


/// Get a reference to a storage device for block operations
pub fn get_block_device(interface_id: u64) -> Result<Arc<Mutex<Arc<dyn StorageDevice>>>, StorageManagerError> {
    let manager = STORAGE_MANAGER.read();
    
    manager
        .devices
        .get(&interface_id)
        .cloned()
        .ok_or(StorageManagerError::InvalidInterfaceID)
}

/// Check completed transfers and wake waiting tasks
pub fn wake_completed_transfers(device_id: u64) {
    let mut node = MCSNode::new();
    let pool_guard = STORAGE_TRANSFER_POOL.lock(&mut node);
    
    if let Some(pool) = pool_guard.as_ref() {
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
}

/// Future for waiting on transfer completion
struct TransferCompletionFuture {
    transfer_id: u16,
}

impl Future for TransferCompletionFuture {
    type Output = Result<(), StorageManagerError>;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        let transfer = get_transfer(self.transfer_id)?;
        
        if transfer.completed.load(Ordering::Acquire) {
            let status = transfer.status.load(Ordering::Acquire);
            if status == 0 {  // Success
                Poll::Ready(Ok(()))
            } else {
                Poll::Ready(Err(StorageManagerError::DeviceError(StorageDevError::IoError)))
            }
        } else {
            // Register waker for IRQ handler task to use
            let mut node = MCSNode::new();
            let mut waker = transfer.waker.lock(&mut node);
            *waker = Some(cx.waker().clone());
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

/// Async read block operation
pub async fn async_read_block(
    device_id: u64,
    block_num: u64,
    buf: &mut [u8]
) -> Result<(), StorageManagerError> {
    // Allocate transfer
    let transfer_id = allocate_transfer(device_id).await?;
    
    // Ensure transfer is freed on all paths
    let result = async {
        // Set up the transfer metadata
        // Note: For simple read/write, we don't set up DMA here as the device will handle it
        // The transfer is mainly used for async completion tracking
        if let Ok(transfer) = get_transfer_mut(transfer_id) {
            transfer.lba = block_num;
            transfer.blocks = 1;
            transfer.read = true;
            transfer.nsid = 1; // Default namespace
        }
        
        // Submit I/O through device (non-blocking)
        let device_mutex = get_block_device(device_id)?;
        {
            let mut node = MCSNode::new();
            let device_guard = device_mutex.lock(&mut node);
            let device = device_guard.as_ref();
            device.read_block(block_num, buf, transfer_id)
                .map_err(|_| StorageManagerError::DeviceError(StorageDevError::IoError))?;
        }
        
        // Wait for completion
        TransferCompletionFuture { transfer_id }.await?;
        
        // Sync DMA buffer if needed
        let transfer = get_transfer(transfer_id)?;
        if let Some(ref dmamap) = transfer.dmamap {
            dmamap.sync(0, dmamap.mapsize(), crate::dma_map::DmaSyncOp::PostRead).ok();
        }
        
        Ok(())
    }.await;
    
    // Always free transfer
    free_transfer(transfer_id);
    result
}

/// Async write block operation
pub async fn async_write_block(
    device_id: u64,
    block_num: u64,
    buf: &[u8]
) -> Result<(), StorageManagerError> {
    // Allocate transfer
    let transfer_id = allocate_transfer(device_id).await?;
    
    // Ensure transfer is freed on all paths
    let result = async {
        // Set up the transfer metadata
        if let Ok(transfer) = get_transfer_mut(transfer_id) {
            transfer.lba = block_num;
            transfer.blocks = 1;
            transfer.read = false;
            transfer.nsid = 1; // Default namespace
        }
        
        // Get device and perform write
        let device_mutex = get_block_device(device_id)?;
        {
            let mut node = MCSNode::new();
            let device_guard = device_mutex.lock(&mut node);
            // We have Arc<dyn StorageDevice> - need to get mutable access
            // This is safe because we have exclusive access via the mutex
            let device_arc = device_guard.clone();
            drop(device_guard);
            
            // Use unsafe to get mutable access
            unsafe {
                let device_ptr = Arc::as_ptr(&device_arc) as *mut dyn StorageDevice;
                (*device_ptr).write_block(block_num, buf, transfer_id)
                    .map_err(|_| StorageManagerError::DeviceError(StorageDevError::IoError))?;
            }
        }
        
        // Wait for completion
        TransferCompletionFuture { transfer_id }.await?;
        
        // Sync DMA buffer if needed
        let transfer = get_transfer(transfer_id)?;
        if let Some(ref dmamap) = transfer.dmamap {
            dmamap.sync(0, dmamap.mapsize(), crate::dma_map::DmaSyncOp::PostWrite).ok();
        }
        
        Ok(())
    }.await;
    
    // Always free transfer
    free_transfer(transfer_id);
    result
}

