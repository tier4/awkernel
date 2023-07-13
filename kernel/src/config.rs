pub use crate::arch::config::*;

/// Backup Heap size is 32 MiB
#[allow(dead_code)]
pub const BACKUP_HEAP_SIZE: usize = 32 * 1024 * 1024;

#[cfg(test)]
#[allow(dead_code)]
pub const HEAP_START: usize = 0;
