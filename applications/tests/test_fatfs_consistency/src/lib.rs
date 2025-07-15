#![no_std]

extern crate alloc;

use alloc::borrow::Cow;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;
use awkernel_async_lib::file::path::AsyncVfsPath;
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::file::fatfs::init_memory_fatfs;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use log::info;

static TEST_PASSED: AtomicBool = AtomicBool::new(false);
static WRITE_COUNT: AtomicU32 = AtomicU32::new(0);
static EXPECTED_LINES: AtomicU32 = AtomicU32::new(0);

const TEST_FILE_PATH: &str = "test_consistency.txt";
const NUM_WRITERS: usize = 3;
const WRITES_PER_TASK: usize = 5;

pub async fn run() {
    // Initialize memory FatFS if not already done
    match init_memory_fatfs() {
        Ok(_) => info!("In-memory FAT filesystem initialized for consistency test."),
        Err(e) => {
            info!("Failed to initialize in-memory FAT filesystem: {:?}", e);
            return;
        }
    }

    awkernel_async_lib::spawn(
        "fatfs consistency test".into(),
        consistency_test(),
        SchedulerType::FIFO,
    )
    .await
    .join()
    .await;

    // Run metadata cache cleanup test
    awkernel_async_lib::spawn(
        "metadata cache cleanup test".into(),
        metadata_cache_cleanup_test(),
        SchedulerType::FIFO,
    )
    .await
    .join()
    .await;
}

async fn writer_task(id: usize) -> usize {
    info!("Writer {} starting", id);
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join(TEST_FILE_PATH).unwrap();

    // Keep file handle open for all writes
    let mut file = match file_path.create_file().await {
        Ok(f) => {
            info!("Writer {} created/opened file", id);
            f
        }
        Err(e) => {
            info!("Writer {} failed to create file: {:?}", id, e);
            return 0;
        }
    };

    let mut lines_written = 0;

    for i in 0..WRITES_PER_TASK {
        // Seek to end to append
        use awkernel_lib::file::io::SeekFrom;
        match file.seek(SeekFrom::End(0)).await {
            Ok(pos) => {
                info!("Writer {} at position {} for iteration {}", id, pos, i);
            }
            Err(e) => {
                info!("Writer {} failed to seek: {:?}", id, e);
                continue;
            }
        }

        // Write data unique to this writer
        let data = format!("Writer {} iteration {}\n", id, i);
        match file.write(data.as_bytes()).await {
            Ok(_) => {
                lines_written += 1;
                WRITE_COUNT.fetch_add(1, Ordering::Relaxed);
                info!("Writer {} wrote iteration {}", id, i);
            }
            Err(e) => {
                info!("Writer {} failed to write: {:?}", id, e);
                continue;
            }
        }

        // Yield to allow other tasks to run
        for _ in 0..3 {
            awkernel_async_lib::r#yield().await;
        }
    }

    // Explicitly drop the file
    drop(file);
    info!("Writer {} finished, wrote {} lines", id, lines_written);

    lines_written
}

async fn monitor_task() {
    info!("Monitor starting");
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join(TEST_FILE_PATH).unwrap();

    // Wait a bit for writers to start
    for _ in 0..20 {
        awkernel_async_lib::r#yield().await;
    }

    let mut checks = 0;
    loop {
        match file_path.open_file().await {
            Ok(mut file) => {
                let mut buffer = vec![0u8; 2048];
                match file.read(&mut buffer).await {
                    Ok(bytes_read) => {
                        if let Ok(content) = core::str::from_utf8(&buffer[..bytes_read]) {
                            let lines: Vec<&str> =
                                content.lines().filter(|l| !l.is_empty()).collect();
                            info!("Monitor: File has {} lines", lines.len());
                        }
                    }
                    Err(e) => {
                        info!("Monitor: Failed to read: {:?}", e);
                    }
                }
            }
            Err(_) => {
                info!("Monitor: File not found yet");
            }
        }

        checks += 1;
        if checks > 20 {
            break;
        }

        // Check periodically
        for _ in 0..10 {
            awkernel_async_lib::r#yield().await;
        }
    }

    info!("Monitor finished");
}

async fn consistency_test() {
    info!("Starting FatFS consistency test");

    // First, ensure we can create a file
    info!("Pre-test: Creating initial file");
    {
        let root_path = AsyncVfsPath::new_in_memory_fatfs();
        let file_path = root_path.join(TEST_FILE_PATH).unwrap();
        match file_path.create_file().await {
            Ok(mut f) => {
                f.write(b"Initial line\n")
                    .await
                    .expect("Initial write failed");
                EXPECTED_LINES.store(1, Ordering::Relaxed);
                info!("Pre-test: Initial file created successfully");
            }
            Err(e) => {
                info!("Pre-test: Failed to create initial file: {:?}", e);
                return;
            }
        }
    }

    // Spawn writer tasks
    let mut writer_handles = Vec::new();
    for i in 0..NUM_WRITERS {
        let handle = awkernel_async_lib::spawn(
            Cow::Owned(format!("writer_{}", i)),
            writer_task(i),
            SchedulerType::FIFO,
        )
        .await;
        writer_handles.push(handle);
    }

    // Spawn monitor task
    let monitor_handle =
        awkernel_async_lib::spawn("monitor".into(), monitor_task(), SchedulerType::FIFO).await;

    // Wait for all writers to complete
    let mut total_lines_written = 0;
    for handle in writer_handles {
        match handle.join().await {
            Ok(lines) => total_lines_written += lines,
            Err(_) => info!("Writer task was cancelled"),
        }
    }

    info!(
        "All writers completed, total lines written: {}",
        total_lines_written
    );
    EXPECTED_LINES.fetch_add(total_lines_written as u32, Ordering::Relaxed);

    // Wait for monitor to finish
    let _ = monitor_handle.join().await;

    // Give some time for file system to settle
    for _ in 0..10 {
        awkernel_async_lib::r#yield().await;
    }

    // Final check - read the file
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join(TEST_FILE_PATH).unwrap();

    match file_path.open_file().await {
        Ok(mut file) => {
            let mut buffer = vec![0u8; 4096];
            let bytes_read = file.read(&mut buffer).await.unwrap_or(0);

            if let Ok(content) = core::str::from_utf8(&buffer[..bytes_read]) {
                let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
                let expected = EXPECTED_LINES.load(Ordering::Relaxed) as usize;

                info!(
                    "Final check: Found {} lines, expected {}",
                    lines.len(),
                    expected
                );

                // Print first few lines
                for (i, line) in lines.iter().take(5).enumerate() {
                    info!("  Line {}: {}", i, line);
                }

                if lines.len() == expected {
                    info!("SUCCESS: File consistency maintained!");
                    TEST_PASSED.store(true, Ordering::Relaxed);
                } else {
                    info!("FAILURE: Line count mismatch");
                }
            }
        }
        Err(e) => {
            info!("Final check: Failed to open file: {:?}", e);
        }
    }

    if TEST_PASSED.load(Ordering::Relaxed) {
        info!("FatFS consistency test PASSED!");
    } else {
        info!("FatFS consistency test FAILED!");
    }

    // Run concurrent truncation test
    concurrent_truncation_test().await;
}

async fn truncation_writer_task(id: usize) -> usize {
    info!("Truncation writer {} starting", id);
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join("truncation_test.txt").unwrap();

    let mut lines_written = 0;

    for i in 0..5 {
        // Open file for each iteration to get fresh handle
        let mut file = match file_path.create_file().await {
            Ok(f) => f,
            Err(e) => {
                info!("Truncation writer {} failed to open file: {:?}", id, e);
                continue;
            }
        };

        // Write some data
        let data = format!(
            "Truncation writer {} iteration {} - this is a longer line to test cluster allocation\n",
            id, i
        );

        // Seek to end to append
        use awkernel_lib::file::io::SeekFrom;
        if let Err(e) = file.seek(SeekFrom::End(0)).await {
            info!("Truncation writer {} failed to seek: {:?}", id, e);
            continue;
        }

        match file.write(data.as_bytes()).await {
            Ok(_) => {
                lines_written += 1;
                info!("Truncation writer {} wrote iteration {}", id, i);
            }
            Err(e) => {
                info!("Truncation writer {} failed to write: {:?}", id, e);
            }
        }

        // Yield to allow truncation
        for _ in 0..5 {
            awkernel_async_lib::r#yield().await;
        }
    }

    info!(
        "Truncation writer {} finished, wrote {} lines",
        id, lines_written
    );
    lines_written
}

async fn truncation_task() {
    info!("Truncation task starting");
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join("truncation_test.txt").unwrap();

    // Wait for writers to write some data
    for _ in 0..10 {
        awkernel_async_lib::r#yield().await;
    }

    for i in 0..3 {
        match file_path.open_file().await {
            Ok(mut file) => {
                // Read current size
                use awkernel_lib::file::io::SeekFrom;
                let size = match file.seek(SeekFrom::End(0)).await {
                    Ok(pos) => pos as u32,
                    Err(e) => {
                        info!("Truncation task: Failed to seek: {:?}", e);
                        continue;
                    }
                };

                if size > 100 {
                    // Truncate to smaller size
                    let new_size = size / 2;
                    if let Err(e) = file.seek(SeekFrom::Start(new_size as u64)).await {
                        info!("Truncation task: Failed to seek for truncate: {:?}", e);
                        continue;
                    }

                    // Truncate is not available on async file interface, simulate by writing
                    // For now just log that we would truncate
                    info!(
                        "Truncation task: Would truncate file from {} to {} bytes",
                        size, new_size
                    );
                }
            }
            Err(e) => {
                info!("Truncation task: Failed to open file: {:?}", e);
            }
        }

        // Wait before next truncation
        for _ in 0..20 {
            awkernel_async_lib::r#yield().await;
        }
    }

    info!("Truncation task finished");
}

async fn reader_with_position_task(id: usize) {
    info!("Position reader {} starting", id);
    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join("truncation_test.txt").unwrap();

    // Wait for file to be created
    for _ in 0..5 {
        awkernel_async_lib::r#yield().await;
    }

    // Open file once and keep reading
    let mut file = match file_path.open_file().await {
        Ok(f) => f,
        Err(e) => {
            info!("Position reader {} failed to open file: {:?}", id, e);
            return;
        }
    };

    let mut last_pos = 0u64;

    for i in 0..10 {
        // Try to read from current position
        let mut buffer = vec![0u8; 256];
        match file.read(&mut buffer).await {
            Ok(bytes_read) => {
                use awkernel_lib::file::io::SeekFrom;
                let current_pos = file.seek(SeekFrom::Current(0)).await.unwrap_or(0);
                info!(
                    "Position reader {}: iteration {}, read {} bytes, position {} -> {}",
                    id, i, bytes_read, last_pos, current_pos
                );
                last_pos = current_pos;
            }
            Err(e) => {
                info!(
                    "Position reader {}: Failed to read at iteration {}: {:?}",
                    id, i, e
                );
                // Try to recover by seeking to start
                use awkernel_lib::file::io::SeekFrom;
                if let Ok(pos) = file.seek(SeekFrom::Start(0)).await {
                    info!(
                        "Position reader {}: Recovered by seeking to start ({})",
                        id, pos
                    );
                    last_pos = pos;
                }
            }
        }

        // Yield to allow truncation/writing
        for _ in 0..3 {
            awkernel_async_lib::r#yield().await;
        }
    }

    info!("Position reader {} finished", id);
}

async fn concurrent_truncation_test() {
    info!("Starting concurrent truncation test");

    // Create initial file
    {
        let root_path = AsyncVfsPath::new_in_memory_fatfs();
        let file_path = root_path.join("truncation_test.txt").unwrap();
        match file_path.create_file().await {
            Ok(mut f) => {
                f.write(b"Initial content for truncation test\n")
                    .await
                    .expect("Initial write failed");
                info!("Truncation test: Initial file created");
            }
            Err(e) => {
                info!("Truncation test: Failed to create initial file: {:?}", e);
                return;
            }
        }
    }

    // Spawn writers, truncator, and readers
    let mut writer_handles = Vec::new();
    let mut reader_handles = Vec::new();

    // Spawn writers
    for i in 0..2 {
        let handle = awkernel_async_lib::spawn(
            Cow::Owned(format!("truncation_writer_{}", i)),
            truncation_writer_task(i),
            SchedulerType::FIFO,
        )
        .await;
        writer_handles.push(handle);
    }

    // Spawn truncation task
    let truncation_handle = awkernel_async_lib::spawn(
        "truncation_task".into(),
        truncation_task(),
        SchedulerType::FIFO,
    )
    .await;

    // Spawn readers
    for i in 0..2 {
        let handle = awkernel_async_lib::spawn(
            Cow::Owned(format!("position_reader_{}", i)),
            reader_with_position_task(i),
            SchedulerType::FIFO,
        )
        .await;
        reader_handles.push(handle);
    }

    // Wait for all writer tasks to complete
    for handle in writer_handles {
        let _ = handle.join().await;
    }

    // Wait for all reader tasks to complete
    for handle in reader_handles {
        let _ = handle.join().await;
    }
    let _ = truncation_handle.join().await;

    info!("Concurrent truncation test completed");
}

// Test metadata cache cleanup
async fn metadata_cache_cleanup_test() {
    info!("Starting metadata cache cleanup test");

    let root_path = AsyncVfsPath::new_in_memory_fatfs();
    let file_path = root_path.join("cache_test.txt").unwrap();

    // Create and drop multiple file handles to test cache cleanup
    for i in 0..5 {
        // Create a file
        let mut file = match file_path.create_file().await {
            Ok(f) => f,
            Err(e) => {
                info!("Failed to create file in iteration {}: {:?}", i, e);
                continue;
            }
        };

        // Write some data
        let data = format!("Test data for iteration {}\n", i);
        if let Err(e) = file.write(data.as_bytes()).await {
            info!("Failed to write in iteration {}: {:?}", i, e);
        }

        // Open the same file multiple times to test shared metadata
        let _file2 = file_path.open_file().await.ok();
        let _file3 = file_path.open_file().await.ok();

        // All handles will be dropped here, should clean up cache
    }

    // Open the file again to verify it still works
    match file_path.open_file().await {
        Ok(mut file) => {
            let mut buffer = vec![0u8; 100];
            match file.read(&mut buffer).await {
                Ok(bytes_read) => {
                    info!("Successfully read {} bytes after cache cleanup", bytes_read);
                }
                Err(e) => {
                    info!("Failed to read after cache cleanup: {:?}", e);
                }
            }
        }
        Err(e) => {
            info!("Failed to open file after cache cleanup: {:?}", e);
        }
    }

    info!("Metadata cache cleanup test completed");
}
