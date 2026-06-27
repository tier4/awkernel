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
    file::{
        fatfs::{
            fs::{format_volume, FileSystem, FormatVolumeOptions, FsOptions, LossyOemCpConverter},
            time::NullTimeProvider,
        },
        io::{Seek, SeekFrom},
        memfs::InMemoryDisk,
    },
    paging::PAGESIZE,
    storage::{
        disk_adapter::BlockDeviceDisk,
        storage_device::StorageDevice,
    },
    sync::rwlock::RwLock,
};

use alloc::{format, string::String, sync::Arc, vec::Vec};
use core::alloc::{GlobalAlloc, Layout};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024;

static FAT_FS_INSTANCE: RwLock<
    Option<Arc<FileSystem<InMemoryDisk, NullTimeProvider, LossyOemCpConverter>>>,
> = RwLock::new(None);

pub fn init_memory_fatfs() -> Result<(), String> {
    let mut fs_guard = FAT_FS_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("FAT filesystem has already been initialized.".into());
    }

    let disk_layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
        .map_err(|_| "Invalid layout for memory filesystem allocation.")?;

    let raw_disk_memory = unsafe { System.alloc(disk_layout) };
    if raw_disk_memory.is_null() {
        return Err("Failed to allocate memory for the in-memory disk.".into());
    }

    let disk_data = unsafe {
        Vec::from_raw_parts(
            raw_disk_memory,
            MEMORY_FILESYSTEM_SIZE,
            MEMORY_FILESYSTEM_SIZE,
        )
    };

    let mut in_memory_disk = InMemoryDisk::new(disk_data, 0);

    if let Err(e) = format_volume(&mut in_memory_disk, FormatVolumeOptions::new()) {
        return Err(format!("Failed to format FAT volume: {e:?}"));
    }

    let file_system = match FileSystem::new(in_memory_disk, FsOptions::new()) {
        Ok(fs) => fs,
        Err(e) => {
            return Err(format!("Failed to create FileSystem instance: {e:?}"));
        }
    };

    *fs_guard = Some(Arc::new(file_system));

    Ok(())
}

pub fn get_memory_fatfs() -> Arc<FileSystem<InMemoryDisk, NullTimeProvider, LossyOemCpConverter>> {
    let fs_guard = FAT_FS_INSTANCE.read();

    (*fs_guard)
        .clone()
        .expect("FAT filesystem has not been initialized. Call init_fatfs() first.")
}

// ── Storage-device-backed FAT filesystem ─────────────────────────────────────

static FAT_FS_STORAGE_INSTANCE: RwLock<
    Option<Arc<FileSystem<BlockDeviceDisk, NullTimeProvider, LossyOemCpConverter>>>,
> = RwLock::new(None);

/// Format a storage device as FAT and mount it.
///
/// Use for a brand-new or blank device (e.g. a fresh RAM disk).
/// All existing data on the device will be destroyed.
pub fn format_and_mount_fatfs(
    device: Arc<dyn StorageDevice + Sync + Send>,
) -> Result<(), String> {
    let mut fs_guard = FAT_FS_STORAGE_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("Storage-backed FAT filesystem has already been initialized.".into());
    }

    let mut disk = BlockDeviceDisk::new(device);

    if let Err(e) = format_volume(&mut disk, FormatVolumeOptions::new()) {
        return Err(format!("Failed to format FAT volume: {e:?}"));
    }

    disk.seek(SeekFrom::Start(0))
        .map_err(|e| format!("Failed to seek to start after format: {e}"))?;

    let file_system = FileSystem::new(disk, FsOptions::new())
        .map_err(|e| format!("Failed to create FileSystem instance: {e:?}"))?;

    *fs_guard = Some(Arc::new(file_system));
    Ok(())
}

/// Try to mount an existing FAT on the device; format and mount if the device
/// does not already contain a valid FAT.
///
/// Use for persistent devices (e.g. virtio-blk) that survive across reboots:
/// the first boot formats the disk, subsequent boots just mount it.
pub fn mount_or_format_fatfs(
    device: Arc<dyn StorageDevice + Sync + Send>,
) -> Result<(), String> {
    let mut fs_guard = FAT_FS_STORAGE_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("Storage-backed FAT filesystem has already been initialized.".into());
    }

    // First attempt: try to mount without formatting.
    let disk = BlockDeviceDisk::new(device.clone());
    if let Ok(fs) = FileSystem::new(disk, FsOptions::new()) {
        log::info!("Mounted existing FAT on storage device.");
        *fs_guard = Some(Arc::new(fs));
        return Ok(());
    }

    log::info!("No valid FAT found — formatting storage device.");

    // Second attempt: format then mount.
    let mut disk = BlockDeviceDisk::new(device);
    if let Err(e) = format_volume(&mut disk, FormatVolumeOptions::new()) {
        return Err(format!("Failed to format FAT volume: {e:?}"));
    }
    disk.seek(SeekFrom::Start(0))
        .map_err(|e| format!("Failed to seek to start after format: {e}"))?;

    let file_system = FileSystem::new(disk, FsOptions::new())
        .map_err(|e| format!("Failed to create FileSystem instance after format: {e:?}"))?;

    *fs_guard = Some(Arc::new(file_system));
    Ok(())
}

/// Returns the storage-backed FAT filesystem handle.
///
/// Panics if neither `format_and_mount_fatfs` nor `mount_or_format_fatfs` has
/// been called yet.
pub fn get_storage_fatfs(
) -> Arc<FileSystem<BlockDeviceDisk, NullTimeProvider, LossyOemCpConverter>> {
    let fs_guard = FAT_FS_STORAGE_INSTANCE.read();
    (*fs_guard)
        .clone()
        .expect("Storage-backed FAT filesystem has not been initialized.")
}

/// Returns true if the storage-backed FAT filesystem has been initialized.
pub fn is_storage_fatfs_ready() -> bool {
    FAT_FS_STORAGE_INSTANCE.read().is_some()
}
