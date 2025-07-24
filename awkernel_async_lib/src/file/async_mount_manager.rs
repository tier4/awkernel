//! Legacy async mount manager - use mount module instead
//!
//! This module is deprecated. Please use the new mount module for all
//! mount operations.

// Re-export from new mount module for backward compatibility
pub use super::mount::{
    MountManager as AsyncMountManager,
    mount_memory_fatfs,
};