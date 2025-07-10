#![no_std]

extern crate alloc;

use alloc::vec;
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_async_lib::file::path::AsyncVfsPath;
use awkernel_lib::file::fatfs::init_memory_fatfs;
use log::info;

pub async fn run() {
    // Initialize memory FatFS if not already done
    match init_memory_fatfs() {
        Ok(_) => info!("In-memory FAT filesystem initialized for simple consistency test."),
        Err(e) => {
            info!("Failed to initialize in-memory FAT filesystem: {e:?}");
            return;
        }
    }
    
    awkernel_async_lib::spawn(
        "fatfs simple consistency test".into(),
        simple_consistency_test(),
        SchedulerType::FIFO,
    )
    .await;
}

async fn simple_consistency_test() {
    info!("Starting simple FatFS consistency test");
    
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    
    // Test 1: Simple create, write, close, read (known to work)
    info!("Test 1: Simple sequential test");
    {
        let file_path = root_path.join("test1.txt").unwrap();
        
        // Create and write
        let mut file = file_path.create_file().await.expect("Failed to create test1");
        file.write(b"Test 1 data").await.expect("Failed to write test1");
        drop(file);
        
        // Read back
        let mut file = file_path.open_file().await.expect("Failed to open test1");
        let mut buf = vec![0u8; 100];
        let read = file.read(&mut buf).await.expect("Failed to read test1");
        info!("Test 1: Read {} bytes", read);
    }
    
    // Test 2: Create file with one handle, then create another handle before closing first
    info!("Test 2: Two handles, close in order");
    {
        let file_path = root_path.join("test2.txt").unwrap();
        
        // Create first handle and write
        let mut file1 = file_path.create_file().await.expect("Failed to create test2 handle 1");
        file1.write(b"Handle 1 data").await.expect("Failed to write with handle 1");
        
        // Create second handle while first is still open
        let file2 = file_path.create_file().await.expect("Failed to create test2 handle 2");
        
        // Close both
        drop(file1);
        drop(file2);
        
        // Try to read
        match file_path.open_file().await {
            Ok(mut file) => {
                let mut buf = vec![0u8; 100];
                let read = file.read(&mut buf).await.expect("Failed to read test2");
                info!("Test 2: SUCCESS - Read {} bytes", read);
            }
            Err(e) => {
                info!("Test 2: FAILED - Could not open file: {:?}", e);
            }
        }
    }
    
    // Test 3: Create handle, close it, then create another handle
    info!("Test 3: Sequential handles");
    {
        let file_path = root_path.join("test3.txt").unwrap();
        
        // Create first handle, write and close
        let mut file1 = file_path.create_file().await.expect("Failed to create test3 handle 1");
        file1.write(b"First write").await.expect("Failed to write first");
        drop(file1);
        
        // Create second handle, write and close
        let mut file2 = file_path.create_file().await.expect("Failed to create test3 handle 2");
        use awkernel_lib::file::io::SeekFrom;
        file2.seek(SeekFrom::End(0)).await.expect("Failed to seek");
        file2.write(b" Second write").await.expect("Failed to write second");
        drop(file2);
        
        // Try to read
        match file_path.open_file().await {
            Ok(mut file) => {
                let mut buf = vec![0u8; 100];
                let read = file.read(&mut buf).await.expect("Failed to read test3");
                info!("Test 3: Read {} bytes: {:?}", read, core::str::from_utf8(&buf[..read]));
            }
            Err(e) => {
                info!("Test 3: Could not open file: {:?}", e);
            }
        }
    }
    
    info!("Simple FatFS consistency test completed");
}