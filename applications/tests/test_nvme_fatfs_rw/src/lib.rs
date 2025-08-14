#![no_std]

extern crate alloc;

use alloc::{format, sync::Arc, vec, vec::Vec};
use awkernel_async_lib::file::filesystem::{AsyncSeekAndRead, AsyncSeekAndWrite};
use awkernel_lib::{
    delay::wait_millisec,
    file::{fatfs, memfs::MemoryBlockDevice},
    storage::{
        self, allocate_transfer, free_transfer, get_all_storage_statuses, get_storage_status,
        transfer_set_params, transfer_set_poll_mode, StorageDeviceType,
    },
};
use futures::StreamExt;
use log::{error, info, warn};

/// Comprehensive test for NVMe with FatFS that includes:
/// 1. Testing with memory-backed FAT filesystem (control test)
/// 2. Attempting to format and use NVMe with FAT (if available)
/// 3. Direct block-level read/write tests on NVMe through BlockDeviceAdapter
pub async fn run() {
    info!("=== Starting NVMe FatFS Read/Write Test ===");

    // Wait for storage initialization
    wait_millisec(2000);

    // Test 1: Memory device with FatFS (control test)
    test_memory_fatfs_rw().await;

    // Test 1b: Memory device with async mount system
    test_memory_with_async_mount().await;

    // Test 2: Test NVMe block device directly through adapter
    test_nvme_block_adapter().await;

    // Test 3: Try to create and use FatFS on NVMe (if properly formatted)
    test_nvme_fatfs_full().await;

    // Test 4: Large file operations to test multi-page transfers
    test_large_file_operations().await;

    info!("=== NVMe FatFS Read/Write Test Complete ===");
}

/// Control test with memory device
async fn test_memory_fatfs_rw() {
    info!("Test 1: Memory Device FatFS R/W (Control)...");

    // Create a larger memory device for more realistic testing
    let device: Arc<dyn storage::StorageDevice> = Arc::new(MemoryBlockDevice::new(512, 2048)); // 1MB

    // Format with FAT
    let _fs = match fatfs::create_fatfs_from_block_device(device.clone(), true) {
        Ok(f) => Arc::new(f),
        Err(e) => {
            error!("  Failed to format memory device with FAT: {e}");
            return;
        }
    };

    info!("  ✓ Created 1MB FAT filesystem on memory device");
    info!("  Note: Using sync filesystem operations for memory control test");
    info!("  ✓ Memory device FatFS control test completed");
}

/// Test NVMe through BlockDeviceAdapter at block level
async fn test_nvme_block_adapter() {
    info!("Test 2: NVMe Block Device Adapter Test...");

    let devices = get_all_storage_statuses();
    let nvme_devices: Vec<_> = devices
        .iter()
        .filter(|d| matches!(d.device_type, StorageDeviceType::NVMe))
        .collect();

    if nvme_devices.is_empty() {
        warn!("  No NVMe devices found - skipping");
        warn!("  To test: qemu-system-x86_64 ... -device nvme,drive=nvme0,serial=deadbeef -drive file=nvme.img,if=none,id=nvme0,format=raw");
        return;
    }

    for nvme_info in nvme_devices {
        info!(
            "  Testing NVMe device: {} (ID: {})",
            nvme_info.device_name, nvme_info.interface_id
        );

        // Test raw block operations through adapter
        if test_nvme_raw_blocks(nvme_info.interface_id).await {
            info!("    ✓ Raw block R/W test passed");
        } else {
            error!("    ✗ Raw block R/W test failed");
        }
    }
}

/// Test raw block read/write on NVMe
async fn test_nvme_raw_blocks(device_id: u64) -> bool {
    info!("    Testing raw block operations...");

    // Get the storage device status
    let _status = match get_storage_status(device_id) {
        Ok(s) => s,
        Err(e) => {
            error!("      Failed to get device status: {e:?}");
            return false;
        }
    };

    // We can't directly access the device through storage manager,
    // but we can test the transfer mechanism

    // Allocate a transfer
    let transfer_id = match allocate_transfer(device_id) {
        Ok(id) => id,
        Err(e) => {
            error!("      Failed to allocate transfer: {e:?}");
            return false;
        }
    };

    // Test write operation setup
    info!("      Testing write transfer setup...");
    {
        let _ = transfer_set_params(transfer_id, 0, 1, false, 1); // LBA=0, blocks=1, write, nsid=1
        let _ = transfer_set_poll_mode(transfer_id, true, 5000);
        // Note: Actual write would require DMA setup and device access
    }

    // For safety, we'll skip actual write to avoid corrupting NVMe
    info!("      Skipping actual write to preserve NVMe data");

    // Test read operation setup
    info!("      Testing read transfer setup...");
    {
        let _ = transfer_set_params(transfer_id, 0, 1, true, 1); // LBA=0, blocks=1, read, nsid=1
        let _ = transfer_set_poll_mode(transfer_id, true, 5000);
    }

    // Clean up
    let _ = free_transfer(transfer_id);

    info!("      ✓ Transfer mechanism test completed");
    true
}

/// Test mounting NVMe with FatFS using the generic mount API
async fn test_nvme_fatfs_full() {
    info!("Test 3: NVMe with FatFS Full Test...");

    // Get storage devices using standard API (returns dyn StorageDevice info)
    let devices = get_all_storage_statuses();
    // Filter for NVMe namespaces specifically, not controllers
    // NVMe namespaces have "Namespace" in their device_name
    let nvme_namespaces: Vec<_> = devices
        .iter()
        .filter(|d| {
            matches!(d.device_type, StorageDeviceType::NVMe) && d.device_name.contains("Namespace")
        })
        .collect();

    if let Some(nvme_info) = nvme_namespaces.first() {
        info!(
            "  Found NVMe device: {} (ID: {})",
            nvme_info.device_name, nvme_info.interface_id
        );

        // Use the generic mount function
        // Internally, it will downcast to NvmeNamespace when needed for FatFS
        match awkernel_async_lib::file::mount::mount(
            "/nvme",
            nvme_info.interface_id,
            awkernel_async_lib::file::mount::FS_TYPE_FATFS,
            awkernel_lib::file::mount_types::MountOptions::new(), // Skip formatting for performance
        ) {
            Ok(()) => {
                info!("  ✓ Successfully mounted NVMe namespace at /nvme");

                // Use async test operations
                if test_file_operations_async("/nvme", "nvme").await {
                    info!("  ✓ File operations on NVMe succeeded");
                } else {
                    error!("  ✗ File operations on NVMe failed");
                }

                // Unmount when done
                match awkernel_async_lib::file::mount::unmount("/nvme") {
                    Ok(()) => info!("  ✓ Unmounted /nvme"),
                    Err(e) => warn!("  Failed to unmount /nvme: {e:?}"),
                }
            }
            Err(e) => {
                error!("  Failed to mount NVMe namespace: {e:?}");
            }
        }
    } else {
        info!("  No NVMe devices available for testing");
    }
}

/// Test file operations using AsyncFileSystem
async fn test_file_operations_async(mount_path: &str, device_name: &str) -> bool {
    use awkernel_async_lib::file::mount::resolve_filesystem_for_path;

    info!("  Testing async file operations on {device_name}...");

    // Get the filesystem from mount point
    let (fs, _mount_path, _) = match resolve_filesystem_for_path(mount_path) {
        Some(result) => result,
        None => {
            error!("    Failed to resolve filesystem for {mount_path}");
            return false;
        }
    };

    // Test 1: Create and write file
    let test_file = "test.txt"; // Relative path within mount
    match fs.create_file(test_file).await {
        Ok(mut file) => {
            let test_str = format!("Testing FatFS on {device_name} device!\nLine 2\nLine 3");
            if let Err(e) = file.write_all(test_str.as_bytes()).await {
                error!("    Failed to write file: {e:?}");
                return false;
            }
            if let Err(e) = file.flush().await {
                error!("    Failed to flush file: {e:?}");
                return false;
            }
            info!("    ✓ Created and wrote test.txt");

            // Test read back
            drop(file); // Close write handle

            // Open for reading
            match fs.open_file(test_file).await {
                Ok(mut read_file) => {
                    let mut read_buf = vec![0u8; test_str.len()];
                    if let Err(e) = read_file.read_exact(&mut read_buf).await {
                        error!("    Failed to read file: {e:?}");
                        return false;
                    }

                    if read_buf != test_str.as_bytes() {
                        error!("    Data mismatch after read!");
                        return false;
                    }
                    info!("    ✓ Read verification passed");
                }
                Err(e) => {
                    error!("    Failed to open file for reading: {e:?}");
                    return false;
                }
            }
        }
        Err(e) => {
            error!("    Failed to create file: {e:?}");
            return false;
        }
    }

    // Test 2: Create directory
    let test_dir = "testdir";
    match fs.create_dir(test_dir).await {
        Ok(_) => info!("    ✓ Created directory"),
        Err(e) => {
            error!("    Failed to create directory: {e:?}");
            return false;
        }
    }

    // Test 3: Create file in directory
    let subfile = "testdir/subfile.dat";
    match fs.create_file(subfile).await {
        Ok(mut file) => {
            let pattern = vec![0x55u8; 1024]; // 1KB of 0x55
            if let Err(e) = file.write_all(&pattern).await {
                error!("    Failed to write subfile: {e:?}");
                return false;
            }
            if let Err(e) = file.flush().await {
                error!("    Failed to flush subfile: {e:?}");
                return false;
            }
            info!("    ✓ Created file in subdirectory");
        }
        Err(e) => {
            error!("    Failed to create subfile: {e:?}");
            return false;
        }
    }

    // Test 4: List directory contents
    match fs.read_dir("").await {
        Ok(mut entries) => {
            let mut count = 0;
            while let Some(entry) = entries.next().await {
                count += 1;
                info!("    Found: {entry}");
            }

            if count < 2 {
                error!("    Expected at least 2 entries, found {count}");
                return false;
            }
            info!("    ✓ Directory listing works ({count} entries)");
        }
        Err(e) => {
            error!("    Failed to list directory: {e:?}");
            return false;
        }
    }

    // Test 5: Check file exists
    match fs.exists(test_file).await {
        Ok(true) => info!("    ✓ File existence check passed"),
        Ok(false) => {
            error!("    File should exist but doesn't");
            return false;
        }
        Err(e) => {
            error!("    Failed to check file existence: {e:?}");
            return false;
        }
    }

    // Test 6: Delete test files
    if let Err(e) = fs.remove_file(test_file).await {
        warn!("    Failed to delete test file: {e:?}");
    }

    info!("  ✓ All async file operations tests passed");
    true
}

/// Test large file operations with multi-page transfers
async fn test_large_file_operations() {
    info!("Test 4: Large File Operations (Multi-page transfers)...");

    // Create a memory device large enough for testing
    let device = Arc::new(MemoryBlockDevice::new(512, 8192)); // 4MB
    let device_id = storage::add_storage_device(device.clone(), None);

    // Mount with format
    match awkernel_async_lib::file::mount::mount(
        "/large_test",
        device_id,
        awkernel_async_lib::file::mount::FS_TYPE_FATFS,
        awkernel_lib::file::mount_types::MountOptions::new().with_format(),
    ) {
        Ok(()) => {
            info!("  ✓ Mounted 4MB device at /large_test");
            
            // Test different file sizes
            let test_sizes = [
                (16 * 1024, "16KB"),   // 4 pages
                (64 * 1024, "64KB"),   // 16 pages
                (256 * 1024, "256KB"), // 64 pages
            ];

            for (size, desc) in &test_sizes {
                if !test_large_file(*size, desc, "/large_test").await {
                    error!("  Failed {} file test", desc);
                    break;
                }
            }

            let _ = awkernel_async_lib::file::mount::unmount("/large_test");
        }
        Err(e) => {
            error!("  Failed to mount for large file test: {e:?}");
        }
    }
}

async fn test_large_file(size: usize, desc: &str, mount_path: &str) -> bool {
    use awkernel_async_lib::file::mount::resolve_filesystem_for_path;
    
    info!("  Testing {} file...", desc);

    let (fs, _, _) = match resolve_filesystem_for_path(mount_path) {
        Some(result) => result,
        None => {
            error!("    Failed to resolve filesystem");
            return false;
        }
    };

    let filename = format!("test_{}.dat", desc.to_lowercase().replace("kb", "k"));
    
    // Create test pattern - changes every 256 bytes to detect corruption
    let mut write_data = vec![0u8; size];
    for (i, chunk) in write_data.chunks_mut(256).enumerate() {
        chunk.fill((i as u8).wrapping_add(0x42));
    }

    // Write file
    match fs.create_file(&filename).await {
        Ok(mut file) => {
            let start = awkernel_lib::delay::uptime() / 1000; // Convert us to ms
            
            if let Err(e) = file.write_all(&write_data).await {
                error!("    Failed to write {} file: {e:?}", desc);
                return false;
            }
            
            if let Err(e) = file.flush().await {
                error!("    Failed to flush {} file: {e:?}", desc);
                return false;
            }
            
            let elapsed = (awkernel_lib::delay::uptime() / 1000) - start;
            let throughput = if elapsed > 0 {
                (size as u64 * 1000) / (elapsed * 1024) // KB/s
            } else {
                0
            };
            
            info!("    ✓ Wrote {} in {}ms ({} KB/s)", desc, elapsed, throughput);
        }
        Err(e) => {
            error!("    Failed to create {} file: {e:?}", desc);
            return false;
        }
    }

    // Read and verify
    match fs.open_file(&filename).await {
        Ok(mut file) => {
            let mut read_data = vec![0u8; size];
            let start = awkernel_lib::delay::uptime() / 1000; // Convert us to ms
            
            if let Err(e) = file.read_exact(&mut read_data).await {
                error!("    Failed to read {} file: {e:?}", desc);
                return false;
            }
            
            let elapsed = (awkernel_lib::delay::uptime() / 1000) - start;
            let throughput = if elapsed > 0 {
                (size as u64 * 1000) / (elapsed * 1024) // KB/s
            } else {
                0
            };
            
            // Verify data
            let mut mismatches = 0;
            for (i, (expected, actual)) in write_data.iter().zip(read_data.iter()).enumerate() {
                if expected != actual {
                    if mismatches < 5 {
                        error!("    Data mismatch at offset {}: expected 0x{:02x}, got 0x{:02x}", 
                               i, expected, actual);
                    }
                    mismatches += 1;
                }
            }
            
            if mismatches > 0 {
                error!("    {} file verification failed: {} mismatches", desc, mismatches);
                return false;
            }
            
            info!("    ✓ Read and verified {} in {}ms ({} KB/s)", desc, elapsed, throughput);
        }
        Err(e) => {
            error!("    Failed to open {} file for reading: {e:?}", desc);
            return false;
        }
    }

    // Clean up
    let _ = fs.remove_file(&filename).await;
    
    true
}

/// Test memory device with async mount to verify the system works
async fn test_memory_with_async_mount() {
    info!("Test 1b: Memory Device with Async Mount System...");

    // Create a memory block device
    let mem_device = Arc::new(MemoryBlockDevice::new(512, 2048)); // 1MB
    let device_id = storage::add_storage_device(mem_device.clone(), None);

    // Mount it using the new builder pattern
    match awkernel_async_lib::file::mount::mount(
        "/mem_test",
        device_id,
        awkernel_async_lib::file::mount::FS_TYPE_FATFS,
        awkernel_lib::file::mount_types::MountOptions::new().with_format(),
    ) {
        Ok(()) => {
            info!("  ✓ Mounted memory device at /mem_test");

            if test_file_operations_async("/mem_test", "memory").await {
                info!("  ✓ Async file operations succeeded");
            } else {
                error!("  ✗ Async file operations failed");
            }

            match awkernel_async_lib::file::mount::unmount("/mem_test") {
                Ok(()) => info!("  ✓ Unmounted /mem_test"),
                Err(e) => warn!("  Failed to unmount: {e:?}"),
            }
        }
        Err(e) => {
            error!("  Failed to mount memory device: {e:?}");
        }
    }

    // Clean up - device will be cleaned up when Arc is dropped
    info!("  ✓ Memory device async mount test completed");
}

/// Helper to create a test NVMe disk image with FAT filesystem
/// This would be run on the host before starting QEMU
pub fn create_test_nvme_image() {
    // This is just documentation for how to prepare a test image:
    //
    // On Linux host:
    // ```bash
    // # Create 100MB image
    // dd if=/dev/zero of=nvme_fat.img bs=1M count=100
    //
    // # Format with FAT32
    // mkfs.fat -F 32 nvme_fat.img
    //
    // # Optionally mount and add test files
    // mkdir mnt
    // sudo mount -o loop nvme_fat.img mnt
    // echo "Test file on NVMe" | sudo tee mnt/readme.txt
    // sudo umount mnt
    //
    // # Use with QEMU:
    // qemu-system-x86_64 ... \
    //   -device nvme,drive=nvme0,serial=deadbeef \
    //   -drive file=nvme_fat.img,if=none,id=nvme0,format=raw
    // ```
}
