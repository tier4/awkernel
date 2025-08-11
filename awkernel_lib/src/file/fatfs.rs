pub mod boot_sector;
pub mod dir;
pub mod dir_entry;
pub mod error;
pub mod file;
pub mod fs;
pub mod table;
pub mod time;

use crate::{
    allocator::System,
    storage::StorageDevice,
    file::{
        block_device::BlockDeviceAdapter,
        fatfs::{
            fs::{format_volume, FileSystem, FormatVolumeOptions, FsOptions, LossyOemCpConverter},
            time::NullTimeProvider,
        },
        memfs::MemoryBlockDevice,
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};

use alloc::{format, string::String, sync::Arc, vec::Vec};
use core::alloc::{GlobalAlloc, Layout};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024;

/// Type alias for the memory-based FAT filesystem
type MemoryFatFs = FileSystem<BlockDeviceAdapter, NullTimeProvider, LossyOemCpConverter>;

static FAT_FS_INSTANCE: RwLock<Option<Arc<MemoryFatFs>>> = RwLock::new(None);

pub fn init_memory_fatfs() -> Result<(), String> {
    let mut fs_guard = FAT_FS_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("FAT filesystem has already been initialized.".into());
    }

    // Allocate memory using System allocator for proper alignment
    let disk_layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
        .map_err(|_| "Invalid layout for memory filesystem allocation.")?;

    let raw_disk_memory = unsafe { System.alloc(disk_layout) };
    if raw_disk_memory.is_null() {
        return Err("Failed to allocate memory for the in-memory disk.".into());
    }

    // Create a Vec from the allocated memory
    let disk_data = unsafe {
        Vec::from_raw_parts(
            raw_disk_memory,
            MEMORY_FILESYSTEM_SIZE,
            MEMORY_FILESYSTEM_SIZE,
        )
    };

    // Create a MemoryBlockDevice with 512 byte blocks using the pre-allocated memory
    let block_size = 512;
    let memory_device: Arc<dyn StorageDevice> = Arc::new(MemoryBlockDevice::from_vec(disk_data, block_size));
    
    // Create the filesystem using BlockDeviceAdapter
    let file_system = match create_fatfs_from_block_device(memory_device, true) {
        Ok(fs) => fs,
        Err(e) => {
            return Err(format!("Failed to create FileSystem instance: {e:?}"));
        }
    };

    *fs_guard = Some(Arc::new(file_system));

    Ok(())
}

pub fn get_memory_fatfs() -> Arc<FileSystem<BlockDeviceAdapter, NullTimeProvider, LossyOemCpConverter>> {
    let fs_guard = FAT_FS_INSTANCE.read();

    (*fs_guard)
        .clone()
        .expect("FAT filesystem has not been initialized. Call init_fatfs() first.")
}

/// Create a FAT filesystem from a block device
pub fn create_fatfs_from_block_device(
    device: Arc<dyn StorageDevice>,
    format: bool,
) -> Result<FileSystem<BlockDeviceAdapter, NullTimeProvider, LossyOemCpConverter>, String> {
    let mut adapter = BlockDeviceAdapter::new(device);
    
    if format {
        format_volume(&mut adapter, FormatVolumeOptions::new())
            .map_err(|e| format!("Failed to format FAT volume: {e:?}"))?;
    }
    
    FileSystem::new(adapter, FsOptions::new())
        .map_err(|e| format!("Failed to create FileSystem instance: {e:?}"))
}

/// Create a FAT filesystem from a block device adapter
pub fn create_fatfs_from_adapter(
    mut adapter: BlockDeviceAdapter,
    format: bool,
) -> Result<FileSystem<BlockDeviceAdapter, NullTimeProvider, LossyOemCpConverter>, String> {
    if format {
        format_volume(&mut adapter, FormatVolumeOptions::new())
            .map_err(|e| format!("Failed to format FAT volume: {e:?}"))?;
    }
    
    FileSystem::new(adapter, FsOptions::new())
        .map_err(|e| format!("Failed to create FileSystem instance: {e:?}"))
}

/// Format a block device with FAT filesystem
pub fn format_block_device_as_fat(
    device: Arc<dyn StorageDevice>,
) -> Result<(), String> {
    let mut adapter = BlockDeviceAdapter::new(device);
    
    format_volume(&mut adapter, FormatVolumeOptions::new())
        .map_err(|e| format!("Failed to format FAT volume: {e:?}"))
}
