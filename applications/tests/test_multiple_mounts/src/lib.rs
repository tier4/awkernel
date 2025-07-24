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
        "test multiple mounts".into(),
        multiple_mounts_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn multiple_mounts_test() {
    log::info!("Testing multiple filesystem mounts...");
    
    // Initialize mount system
    match MountManager::init() {
        Ok(_) => log::info!("Mount manager initialized"),
        Err(e) => {
            log::error!("Failed to initialize mount manager: {:?}", e);
            return;
        }
    }
    
    // Mount first filesystem at /data
    match mount_memory_fatfs("/data", 256 * 1024).await {
        Ok(_) => log::info!("Mounted filesystem at /data"),
        Err(e) => {
            log::error!("Failed to mount at /data: {:?}", e);
            return;
        }
    }
    
    // Mount second filesystem at /temp
    match mount_memory_fatfs("/temp", 128 * 1024).await {
        Ok(_) => log::info!("Mounted filesystem at /temp"),
        Err(e) => {
            log::error!("Failed to mount at /temp: {:?}", e);
            return;
        }
    }
    
    // Write to first filesystem
    let data_file = MountAwareAsyncVfsPath::new("/data/config.txt");
    match data_file.create_file().await {
        Ok(mut writer) => {
            match writer.write_all(b"System configuration data").await {
                Ok(_) => log::info!("Wrote to /data/config.txt"),
                Err(e) => {
                    log::error!("Failed to write to /data: {:?}", e);
                    return;
                }
            }
            writer.flush().await.ok();
        }
        Err(e) => {
            log::error!("Failed to create /data/config.txt: {:?}", e);
            return;
        }
    }
    
    // Write to second filesystem
    let temp_file = MountAwareAsyncVfsPath::new("/temp/log.txt");
    match temp_file.create_file().await {
        Ok(mut writer) => {
            match writer.write_all(b"Temporary log data").await {
                Ok(_) => log::info!("Wrote to /temp/log.txt"),
                Err(e) => {
                    log::error!("Failed to write to /temp: {:?}", e);
                    return;
                }
            }
            writer.flush().await.ok();
        }
        Err(e) => {
            log::error!("Failed to create /temp/log.txt: {:?}", e);
            return;
        }
    }
    
    // Read back from both filesystems
    match data_file.open_file().await {
        Ok(mut reader) => {
            let mut contents = alloc::string::String::new();
            match reader.read_to_string(&mut contents).await {
                Ok(_) => {
                    if contents == "System configuration data" {
                        log::info!("✓ /data filesystem working correctly");
                    } else {
                        log::error!("/data contents don't match!");
                    }
                }
                Err(e) => log::error!("Failed to read from /data: {:?}", e),
            }
        }
        Err(e) => log::error!("Failed to open /data/config.txt: {:?}", e),
    }
    
    match temp_file.open_file().await {
        Ok(mut reader) => {
            let mut contents = alloc::string::String::new();
            match reader.read_to_string(&mut contents).await {
                Ok(_) => {
                    if contents == "Temporary log data" {
                        log::info!("✓ /temp filesystem working correctly");
                    } else {
                        log::error!("/temp contents don't match!");
                    }
                }
                Err(e) => log::error!("Failed to read from /temp: {:?}", e),
            }
        }
        Err(e) => log::error!("Failed to open /temp/log.txt: {:?}", e),
    }
    
    log::info!("✓ Multiple mounts test completed!");
}