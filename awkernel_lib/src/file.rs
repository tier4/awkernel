pub mod error;
pub mod fatfs;
pub mod io;
pub mod memfs;
pub mod vfs;

use crate::{
    allocator::System,
    file::{
        fatfs::fs::{format_volume, FileSystem, FormatVolumeOptions, FsOptions},
        io::{IoBase, Read, Seek, SeekFrom, Write},
        memfs::InMemoryDisk,
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};
use alloc::{collections::btree_map::BTreeMap, string::String, sync::Arc, vec::Vec};

use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

static FILE_MANAGER: RwLock<FileManager> = RwLock::new(FileManager {
    interfaces: BTreeMap::new(),
    interface_id: 0,
});

pub struct FileManager {
    interfaces: BTreeMap<u64, Arc<IfFile>>,
    interface_id: u64,
}

pub fn init_filesystem() {
    let result = {
        let layout = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE)
            .expect("Invalid layout for memory filesystem");
        unsafe { System.alloc(layout) }
    };

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let mut disk = InMemoryDisk::new(data, 0);
    let options = FormatVolumeOptions::new();

    match format_volume(&mut disk, options) {
        Ok(_) => log::info!("FAT filesystem formatted successfully in memory!"),
        Err(e) => log::info!("Error formatting: {:?}", e),
    }

    let fs = match FileSystem::new(disk, FsOptions::new()) {
        Ok(fs) => fs,
        Err(e) => panic!("Error new file system: {:?}", e),
    };
}

pub(super) struct IfFile {}
