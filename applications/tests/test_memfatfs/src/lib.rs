#![no_std]

extern crate alloc;

use alloc::vec;
use awkernel_async_lib::file::{
    mount::{mount, MountOptions},
    path::AsyncVfsPath,
};
use awkernel_lib::file::{
    fatfs::init_memory_fatfs,
    memfs::create_memory_block_device,
};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test fatfs".into(),
        memfatfs_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn memfatfs_test() {
    // Create a memory block device
    let device = match create_memory_block_device(1024 * 1024, 512) {
        Some(dev) => dev,
        None => {
            log::error!("Failed to create memory block device");
            return;
        }
    };

    // Mount the FAT filesystem
    let mount_options = MountOptions::new();
    if let Err(e) = mount("/", device, "fatfs", mount_options) {
        log::error!("Failed to mount FAT filesystem: {e:?}");
        return;
    }
    log::info!("In-memory FAT filesystem mounted successfully.");

    let root_path = AsyncVfsPath::new("/");
    let file_name = "test.txt";
    let data_to_write = b"Hello from the in-memory FAT filesystem!";
    let bytes_written;

    let file_path = root_path.join(file_name).unwrap();
    log::info!("Attempting to create and write to file '{file_name}'");

    match file_path.create_file().await {
        Ok(mut file) => match file.write(data_to_write).await {
            Ok(len) => {
                bytes_written = len;
                log::info!("Successfully wrote {bytes_written} bytes to '{file_name}'.");
            }
            Err(e) => {
                log::error!("Failed to write to file '{file_name}': {e:?}");
                return;
            }
        },
        Err(e) => {
            log::error!("Failed to create file '{file_name}': {e:?}");
            return;
        }
    };

    log::info!("Attempting to open and read from file '{file_name}'");
    if bytes_written == 0 {
        log::warn!("No bytes were written, skipping file read operation.");
        return;
    }

    match file_path.open_file().await {
        Ok(mut file) => {
            let mut read_buffer = vec![0; bytes_written];
            match file.read(&mut read_buffer).await {
                Ok(bytes_read) => {
                    log::info!("Successfully read {bytes_read} bytes from '{file_name}'.");
                    if bytes_read != bytes_written {
                        log::warn!(
                            "Bytes read ({bytes_read}) does not match bytes written ({bytes_written})."
                        );
                    }

                    match core::str::from_utf8(&read_buffer[..bytes_read]) {
                        Ok(s) => log::info!("Content of '{file_name}': \"{s}\""),
                        Err(_) => log::warn!(
                            "Content of '{}' is not valid UTF-8. Raw bytes: {:?}",
                            file_name,
                            &read_buffer[..bytes_read]
                        ),
                    }
                }
                Err(e) => {
                    log::error!("Failed to read from file '{file_name}': {e:?}");
                }
            }
        }
        Err(e) => {
            log::error!("Failed to open file '{file_name}': {e:?}");
        }
    }

    log::info!("FAT filesystem test completed.");
}
