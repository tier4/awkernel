#![no_std]

extern crate alloc;

use awkernel_async_lib::{
    file::{
        mount::{mount, MountOptions},
        filesystem::AsyncSeekAndWrite,
        path::AsyncVfsPath,
    },
};
use awkernel_lib::file::memfs::create_memory_block_device;

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
    
    // Mount first filesystem at /data
    let data_device = match create_memory_block_device(256 * 1024, 512) {
        Ok(device) => device,
        Err(e) => {
            log::error!("Failed to create data device: {:?}", e);
            return;
        }
    };
    let mut data_options = MountOptions::new();
    data_options.fs_options.insert("format".into(), "true".into());
    match mount("/data", "data", "fatfs", data_device, data_options).await {
        Ok(_) => log::info!("Mounted filesystem at /data"),
        Err(e) => {
            log::error!("Failed to mount at /data: {:?}", e);
            return;
        }
    }
    
    // Mount second filesystem at /temp
    let temp_device = match create_memory_block_device(128 * 1024, 512) {
        Ok(device) => device,
        Err(e) => {
            log::error!("Failed to create temp device: {:?}", e);
            return;
        }
    };
    let mut temp_options = MountOptions::new();
    temp_options.fs_options.insert("format".into(), "true".into());
    match mount("/temp", "temp", "fatfs", temp_device, temp_options).await {
        Ok(_) => log::info!("Mounted filesystem at /temp"),
        Err(e) => {
            log::error!("Failed to mount at /temp: {:?}", e);
            return;
        }
    }
    
    // Write to first filesystem
    let data_file = AsyncVfsPath::new("/data/config.txt");
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
    let temp_file = AsyncVfsPath::new("/temp/log.txt");
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