#![no_std]

extern crate alloc;

use awkernel_async_lib::{
    file::{
        mount::{MountManager, mount_memory_fatfs},
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
    
    // Initialize mount system
    match MountManager::init() {
        Ok(_) => log::info!("Mount manager initialized"),
        Err(e) => {
            log::error!("Failed to initialize mount manager: {:?}", e);
            return;
        }
    }
    
    // Mount memory filesystem
    match mount_memory_fatfs("/test", 512 * 1024).await {
        Ok(_) => log::info!("Memory filesystem mounted at /test"),
        Err(e) => {
            log::error!("Failed to mount memory filesystem: {:?}", e);
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
                    log::error!("Failed to write: {:?}", e);
                    return;
                }
            }
            match writer.flush().await {
                Ok(_) => log::info!("File flushed successfully"),
                Err(e) => {
                    log::error!("Failed to flush: {:?}", e);
                    return;
                }
            }
        }
        Err(e) => {
            log::error!("Failed to create file: {:?}", e);
            return;
        }
    }
    
    // Read it back
    match file_path.open_file().await {
        Ok(mut reader) => {
            let mut contents = alloc::string::String::new();
            match reader.read_to_string(&mut contents).await {
                Ok(_) => {
                    log::info!("File contents: {}", contents);
                    if contents == "Hello from memory FatFS!" {
                        log::info!("✓ Memory FatFS test passed!");
                    } else {
                        log::error!("File contents don't match!");
                    }
                }
                Err(e) => {
                    log::error!("Failed to read: {:?}", e);
                }
            }
        }
        Err(e) => {
            log::error!("Failed to open file: {:?}", e);
        }
    }
}