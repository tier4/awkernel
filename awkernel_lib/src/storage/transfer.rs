//! Storage transfer management
use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, AtomicU16, Ordering};
use core::task::Waker;

use super::{StorageDevError, StorageManagerError};

pub const DEFAULT_IO_TIMEOUT_MS: u32 = 5000; // 5 seconds for I/O operations
pub const DEFAULT_TRANSFER_TIMEOUT_MS: u32 = 10000; // 10 seconds for transfers

pub struct StorageTransfer {
    pub device_id: u64,
    pub lba: u64,
    pub blocks: u32,
    pub nsid: u32,
    pub read: bool,
    pub poll: bool,
    pub timeout_ms: u32,
    pub completed: AtomicBool,
    pub status: AtomicU16,
    pub waker: Mutex<Option<Waker>>,
}

impl Default for StorageTransfer {
    fn default() -> Self {
        Self {
            device_id: 0,
            lba: 0,
            blocks: 0,
            nsid: 0,
            read: true,
            poll: false,
            timeout_ms: DEFAULT_IO_TIMEOUT_MS,
            completed: AtomicBool::new(false),
            status: AtomicU16::new(0),
            waker: Mutex::new(None),
        }
    }
}

pub struct StorageTransferPool {
    transfers: Vec<StorageTransfer>,
    free_list: Mutex<Vec<u16>>,
}

const MAX_TRANSFERS: usize = 256;

static STORAGE_TRANSFER_POOL: RwLock<Option<StorageTransferPool>> = RwLock::new(None);

pub fn init_transfer_pool() {
    let mut storage_transfer_pool = STORAGE_TRANSFER_POOL.write();

    if storage_transfer_pool.is_none() {
        let mut transfers = Vec::with_capacity(MAX_TRANSFERS);
        let mut free_list = Vec::with_capacity(MAX_TRANSFERS);

        for i in 0..MAX_TRANSFERS {
            transfers.push(StorageTransfer::default());
            free_list.push(i as u16);
        }

        *storage_transfer_pool = Some(StorageTransferPool {
            transfers,
            free_list: Mutex::new(free_list),
        });
    }
}

/// TODO: Could implement async version that waits when pool is exhausted
pub fn allocate_transfer(device_id: u64) -> Result<u16, StorageManagerError> {
    let mut storage_transfer_pool = STORAGE_TRANSFER_POOL.write();

    let pool = match storage_transfer_pool.as_mut() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
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

pub fn transfer_set_params(
    id: u16,
    lba: u64,
    blocks: u32,
    read: bool,
    nsid: u32,
) -> Result<(), StorageManagerError> {
    let mut storage_transfer_pool = STORAGE_TRANSFER_POOL.write();

    let pool = match storage_transfer_pool.as_mut() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
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

pub fn transfer_set_poll_mode(
    id: u16,
    poll: bool,
    timeout_ms: u32,
) -> Result<(), StorageManagerError> {
    let mut storage_transfer_pool = STORAGE_TRANSFER_POOL.write();

    let pool = match storage_transfer_pool.as_mut() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &mut pool.transfers[id as usize];
    transfer.poll = poll;
    transfer.timeout_ms = timeout_ms;
    Ok(())
}

pub fn transfer_get_lba(id: u16) -> Result<u64, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].lba)
}

pub fn transfer_get_blocks(id: u16) -> Result<u32, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].blocks)
}

pub fn transfer_get_nsid(id: u16) -> Result<u32, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].nsid)
}

pub fn transfer_is_read(id: u16) -> Result<bool, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].read)
}

pub fn transfer_is_completed(id: u16) -> Result<bool, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize]
        .completed
        .load(Ordering::Acquire))
}

pub fn transfer_get_status(id: u16) -> Result<u16, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].status.load(Ordering::Acquire))
}

pub fn transfer_mark_completed(id: u16, status: u16) -> Result<(), StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &pool.transfers[id as usize];
    transfer.status.store(status, Ordering::Release);
    transfer.completed.store(true, Ordering::Release);
    Ok(())
}

pub fn transfer_set_waker(id: u16, waker: Option<Waker>) -> Result<(), StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let mut waker_node = MCSNode::new();
    let mut waker_guard = pool.transfers[id as usize].waker.lock(&mut waker_node);
    *waker_guard = waker;
    Ok(())
}

pub fn transfer_is_poll_mode(id: u16) -> Result<bool, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].poll)
}

pub fn transfer_get_timeout_ms(id: u16) -> Result<u32, StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    Ok(pool.transfers[id as usize].timeout_ms)
}

pub fn transfer_get_info(id: u16) -> Result<(u64, u32, u32, bool), StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    if (id as usize) >= pool.transfers.len() {
        return Err(StorageManagerError::InvalidTransferID);
    }

    let transfer = &pool.transfers[id as usize];
    Ok((transfer.lba, transfer.blocks, transfer.nsid, transfer.read))
}

pub fn free_transfer(id: u16) -> Result<(), StorageManagerError> {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return Err(StorageManagerError::PoolNotInitialized),
    };

    let mut free_node = MCSNode::new();
    let mut free_list = pool.free_list.lock(&mut free_node);

    free_list.push(id);
    Ok(())
}

pub fn wake_completed_transfers(device_id: u64) {
    let storage_transfer_pool = STORAGE_TRANSFER_POOL.read();

    let pool = match storage_transfer_pool.as_ref() {
        Some(p) => p,
        None => return,
    };

    let mut wakers_to_wake = alloc::vec::Vec::new();

    for transfer in &pool.transfers {
        if transfer.device_id == device_id && transfer.completed.load(Ordering::Acquire) {
            let mut waker_node = MCSNode::new();
            let mut waker_guard = transfer.waker.lock(&mut waker_node);
            if let Some(waker) = waker_guard.take() {
                wakers_to_wake.push(waker);
            }
        }
    }

    drop(storage_transfer_pool);

    for waker in wakers_to_wake {
        waker.wake();
    }
}
