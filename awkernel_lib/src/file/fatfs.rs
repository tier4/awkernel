pub mod boot_sector;
pub mod dir;
pub mod dir_entry;
pub mod error;
pub mod file;
pub mod fs;
pub mod table;
pub mod time;

use crate::{
    file::{
        block_device::BlockDevice,
        block_device_adapter::BlockDeviceAdapter,
        fatfs::{
            fs::{format_volume, FileSystem, FormatVolumeOptions, FsOptions, LossyOemCpConverter},
            time::NullTimeProvider,
        },
        block_device::MemoryBlockDevice,
    },
    sync::rwlock::RwLock,
};

use alloc::{format, string::String, sync::Arc};
use core::fmt::Debug;

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024;

static FAT_FS_INSTANCE: RwLock<
    Option<Arc<FileSystem<BlockDeviceAdapter<MemoryBlockDevice>, NullTimeProvider, LossyOemCpConverter>>>,
> = RwLock::new(None);

pub fn init_memory_fatfs() -> Result<(), String> {
    let mut fs_guard = FAT_FS_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("FAT filesystem has already been initialized.".into());
    }

    // Create a MemoryBlockDevice with 512 byte blocks
    let block_size = 512;
    let num_blocks = MEMORY_FILESYSTEM_SIZE as u64 / block_size as u64;
    let memory_device = Arc::new(MemoryBlockDevice::new(block_size, num_blocks));
    
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

pub fn get_memory_fatfs() -> Arc<FileSystem<BlockDeviceAdapter<MemoryBlockDevice>, NullTimeProvider, LossyOemCpConverter>> {
    let fs_guard = FAT_FS_INSTANCE.read();

    (*fs_guard)
        .clone()
        .expect("FAT filesystem has not been initialized. Call init_fatfs() first.")
}

/// Create a FAT filesystem from a block device
pub fn create_fatfs_from_block_device<D: BlockDevice + Debug + 'static>(
    device: Arc<D>,
    format: bool,
) -> Result<FileSystem<BlockDeviceAdapter<D>, NullTimeProvider, LossyOemCpConverter>, String> {
    let mut adapter = BlockDeviceAdapter::new(device);
    
    if format {
        format_volume(&mut adapter, FormatVolumeOptions::new())
            .map_err(|e| format!("Failed to format FAT volume: {:?}", e))?;
    }
    
    FileSystem::new(adapter, FsOptions::new())
        .map_err(|e| format!("Failed to create FileSystem instance: {:?}", e))
}

/// Format a block device with FAT filesystem
pub fn format_block_device_as_fat<D: BlockDevice + Debug + 'static>(
    device: Arc<D>,
) -> Result<(), String> {
    let mut adapter = BlockDeviceAdapter::new(device);
    
    format_volume(&mut adapter, FormatVolumeOptions::new())
        .map_err(|e| format!("Failed to format FAT volume: {:?}", e))
}
