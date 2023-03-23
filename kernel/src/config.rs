pub use crate::arch::config::*;

/// Heap size is 256MiB
#[allow(dead_code)]
pub const HEAP_SIZE: u64 = 256 * 1024 * 1024;
/// Backup Heap size is 32 MiB
pub const BACKUP_HEAP_SIZE: u64 = 32 * 1024 * 1024;

#[cfg(test)]
#[allow(dead_code)]
pub const HEAP_START: u64 = 0;
