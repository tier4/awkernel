#![no_std]

extern crate alloc;

use alloc::{string::String, sync::Arc, vec::Vec};
use awkernel_async_lib::file::fatfs;
use awkernel_lib::{
    allocator::System,
    file::{
        fatfs::fs::{FileSystem, FormatVolumeOptions, FsOptions, format_volume},
        io::{IoBase, Read, Seek, SeekFrom, Write},
        memfs::InMemoryDisk,
    },
    paging::PAGESIZE,
};

use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test fatfs".into(),
        fatfs_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

async fn fatfs_test() {
    log::info!("fatfs_test");
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
    let root_dir = FileSystem::root_dir(&Arc::new(fs));
    let mut file = match root_dir.create_file("file.txt") {
        Ok(file) => file,
        Err(e) => panic!("Error create file: {:?}", e),
    };

    let data_to_write = b"Hello World!";
    let w_bytes = match file.write(data_to_write) {
        Ok(w_bytes) => w_bytes,
        Err(e) => panic!("Erro write file: {:?}", e),
    };

    let _ = file.seek(SeekFrom::Start(0));

    let mut buf = Vec::new();
    buf.resize(w_bytes, 0);
    let _ = match file.read(&mut buf) {
        Ok(r_bytes) => r_bytes,
        Err(e) => panic!("Erro read file: {:?}", e),
    };

    match core::str::from_utf8(&buf) {
        Ok(s) => log::info!("Vec<u8> 内容 (UTF-8): {}", s),
        Err(_) => log::info!("Vec<u8> 内容 (UTF-8): [不正な UTF-8 シーケンス]",),
    }
    loop {}
}
