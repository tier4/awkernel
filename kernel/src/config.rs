pub use crate::arch::config::*;

/// Heap size is 64MiB.
pub const HEAP_SIZE: u64 = 64 * 1024 * 1024;

#[cfg(test)]
pub const HEAP_START: u64 = 0;
