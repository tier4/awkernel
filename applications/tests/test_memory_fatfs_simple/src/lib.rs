#![no_std]

extern crate alloc;

use awkernel_async_lib::{
    file::{
        mount::{
            mount,
            create_memory_block_device,
            DEFAULT_BLOCK_SIZE,
            MountOptions,
        },
        filesystem::AsyncSeekAndWrite,
        mount_aware_vfs_path::MountAwareAsyncVfsPath,
    },
};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test memory fatfs mount".into(),
        memory_fatfs_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn memory_fatfs_test() {
    log::info!("Testing memory FatFS mount...");
    
    // Create a memory block device
    let device_size = 512 * 1024; // 512KB
    let device = match create_memory_block_device(device_size, DEFAULT_BLOCK_SIZE) {
        Ok(dev) => dev,
        Err(e) => {
            log::error!("Failed to create memory block device: {e:?}");
            return;
        }
    };
    
    // Create mount options with format=true to format the new device
    let mut options = MountOptions::new();
    options.fs_options.insert("format".into(), "true".into());
    
    // Mount the filesystem
    match mount(
        "/test",
        "memory:512KB",
        "fatfs",
        device,
        options,
    ).await {
        Ok(_) => log::info!("Memory filesystem mounted at /test"),
        Err(e) => {
            log::error!("Failed to mount filesystem: {e:?}");
            return;
        }
    }
    
    // Create and write a file
    let file_path = MountAwareAsyncVfsPath::new("/test/hello.txt");
    
    match file_path.create_file().await {
        Ok(mut writer) => {
            match writer.write_all(b"Hello from memory FatFS!").await {
                Ok(_) => log::info!("Successfully wrote to file"),
                Err(e) => {
                    log::error!("Failed to write: {e:?}");
                    return;
                }
            }
            match writer.flush().await {
                Ok(_) => log::info!("File flushed successfully"),
                Err(e) => {
                    log::error!("Failed to flush: {e:?}");
                    return;
                }
            }
        }
        Err(e) => {
            log::error!("Failed to create file: {e:?}");
            return;
        }
    }
    
    // Read it back
    match file_path.open_file().await {
        Ok(mut reader) => {
            let mut contents = alloc::string::String::new();
            match reader.read_to_string(&mut contents).await {
                Ok(_) => {
                    log::info!("File contents: {contents}");
                    if contents == "Hello from memory FatFS!" {
                        log::info!("✓ Memory FatFS test passed!");
                    } else {
                        log::error!("File contents don't match!");
                    }
                }
                Err(e) => {
                    log::error!("Failed to read: {e:?}");
                }
            }
        }
        Err(e) => {
            log::error!("Failed to open file: {e:?}");
        }
    }
}