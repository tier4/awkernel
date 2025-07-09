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
            time::AwkernelTimeProvider,
        },
        memfs::InMemoryDisk,
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};

use alloc::{sync::Arc, vec::Vec};
use core::alloc::{GlobalAlloc, Layout};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024;

static FAT_FS_INSTANCE: RwLock<
    Option<Arc<FileSystem<InMemoryDisk, AwkernelTimeProvider, LossyOemCpConverter>>>,
> = RwLock::new(None);

pub fn init_memory_fatfs() -> Result<(), &'static str> {
    let mut fs_guard = FAT_FS_INSTANCE.write();
    if fs_guard.is_some() {
        return Err("FAT filesystem has already been initialized.");
    }

    let disk_layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
        .map_err(|_| "Invalid layout for memory filesystem allocation.")?;

    let raw_disk_memory = unsafe { System.alloc(disk_layout) };
    if raw_disk_memory.is_null() {
        return Err("Failed to allocate memory for the in-memory disk.");
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
        log::error!("Error formatting FAT filesystem: {e:?}");
        return Err("Failed to format FAT volume.");
    }

    let fs_options = FsOptions {
        update_accessed_date: false,
        oem_cp_converter: LossyOemCpConverter::new(),
        time_provider: AwkernelTimeProvider::new(),
        strict: true,
    };
    
    let file_system = match FileSystem::new(in_memory_disk, fs_options) {
        Ok(fs) => fs,
        Err(e) => {
            log::error!("Error creating new FileSystem instance: {e:?}");
            return Err("Failed to create FileSystem instance.");
        }
    };

    *fs_guard = Some(Arc::new(file_system));

    Ok(())
}

pub fn get_memory_fatfs() -> Arc<FileSystem<InMemoryDisk, AwkernelTimeProvider, LossyOemCpConverter>> {
    let fs_guard = FAT_FS_INSTANCE.read();

    (*fs_guard)
        .clone()
        .expect("FAT filesystem has not been initialized. Call init_fatfs() first.")
}
