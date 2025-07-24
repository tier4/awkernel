//! Mount validation and security checks
//!
//! This module provides validation for mount operations including path validation,
//! permission checks, and filesystem compatibility verification.

use alloc::string::String;
use alloc::vec::Vec;
use alloc::{vec, format};
use super::mount_types::{MountError, MountFlags, MountOptions};

/// Mount path validation rules
pub struct MountValidator {
    /// Allowed mount prefixes (e.g., /mnt, /media)
    allowed_prefixes: Vec<String>,
    /// Disallowed mount paths (e.g., /proc, /sys)
    forbidden_paths: Vec<String>,
    /// Maximum mount path depth
    max_path_depth: usize,
    /// Allow mounting over existing mounts
    allow_overmount: bool,
}

impl Default for MountValidator {
    fn default() -> Self {
        Self {
            allowed_prefixes: vec![],
            forbidden_paths: vec![
                "/proc".into(),
                "/sys".into(),
                "/dev".into(),
            ],
            max_path_depth: 10,
            allow_overmount: false,
        }
    }
}

impl MountValidator {
    /// Create a new mount validator with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a permissive validator (for testing)
    pub fn permissive() -> Self {
        Self {
            allowed_prefixes: vec![],
            forbidden_paths: vec![],
            max_path_depth: 20,
            allow_overmount: true,
        }
    }

    /// Add an allowed mount prefix
    pub fn add_allowed_prefix(&mut self, prefix: String) {
        self.allowed_prefixes.push(prefix);
    }

    /// Add a forbidden path
    pub fn add_forbidden_path(&mut self, path: String) {
        self.forbidden_paths.push(path);
    }

    /// Validate a mount path
    pub fn validate_mount_path(&self, path: &str) -> Result<(), MountError> {
        // Must be absolute path
        if !path.starts_with('/') {
            return Err(MountError::InvalidPath("Path must be absolute".into()));
        }

        // Check forbidden paths
        for forbidden in &self.forbidden_paths {
            if path.starts_with(forbidden) {
                return Err(MountError::PermissionDenied);
            }
        }

        // Check allowed prefixes if any are configured
        if !self.allowed_prefixes.is_empty() {
            let allowed = self.allowed_prefixes.iter()
                .any(|prefix| path.starts_with(prefix));
            if !allowed {
                return Err(MountError::InvalidPath(
                    "Path not in allowed mount locations".into()
                ));
            }
        }

        // Check path depth
        let depth = path.split('/').filter(|s| !s.is_empty()).count();
        if depth > self.max_path_depth {
            return Err(MountError::InvalidPath(
                format!("Path depth {} exceeds maximum {}", depth, self.max_path_depth)
            ));
        }

        // Check for invalid characters
        if path.contains('\0') || path.contains("..") {
            return Err(MountError::InvalidPath(
                "Path contains invalid characters".into()
            ));
        }

        Ok(())
    }

    /// Validate mount source
    pub fn validate_mount_source(&self, source: &str, fs_type: &str) -> Result<(), MountError> {
        // Different validation based on filesystem type
        match fs_type {
            "devfs" | "procfs" | "sysfs" => {
                // Virtual filesystems don't need device validation
                Ok(())
            }
            "tmpfs" | "ramfs" => {
                // Memory filesystems just need a name
                if source.is_empty() {
                    Err(MountError::InvalidPath("Source name required".into()))
                } else {
                    Ok(())
                }
            }
            _ => {
                // Block device filesystems need device path
                if !source.starts_with("/dev/") {
                    Err(MountError::DeviceNotFound(
                        "Source must be a device path".into()
                    ))
                } else {
                    Ok(())
                }
            }
        }
    }

    /// Validate mount flags
    pub fn validate_mount_flags(&self, flags: &MountFlags, fs_type: &str) -> Result<(), MountError> {
        // Some filesystems require specific flags
        match fs_type {
            "procfs" | "sysfs" => {
                // These should always be nodev
                if !flags.nodev {
                    return Err(MountError::InvalidPath(
                        format!("{} must be mounted with nodev", fs_type)
                    ));
                }
            }
            _ => {}
        }

        Ok(())
    }

    /// Validate mount options
    pub fn validate_mount_options(&self, options: &MountOptions, fs_type: &str) -> Result<(), MountError> {
        // Validate flags
        self.validate_mount_flags(&options.flags, fs_type)?;

        // Validate filesystem-specific options
        match fs_type {
            "tmpfs" | "ramfs" => {
                // Check size option
                if let Some(size_str) = options.fs_options.get("size") {
                    let size: usize = size_str.parse()
                        .map_err(|_| MountError::InvalidPath("Invalid size option".into()))?;
                    
                    // Reasonable size limits (1KB to 1GB)
                    if size < 1024 || size > 1024 * 1024 * 1024 {
                        return Err(MountError::InvalidPath(
                            "Size must be between 1KB and 1GB".into()
                        ));
                    }
                }
            }
            "fatfs" => {
                // Check format option
                if let Some(format_str) = options.fs_options.get("format") {
                    match format_str.as_str() {
                        "true" | "false" => {}
                        _ => return Err(MountError::InvalidPath(
                            "Format option must be true or false".into()
                        )),
                    }
                }
            }
            _ => {}
        }

        Ok(())
    }

    /// Full mount validation
    pub fn validate_mount(
        &self,
        path: &str,
        source: &str,
        fs_type: &str,
        options: &MountOptions,
    ) -> Result<(), MountError> {
        self.validate_mount_path(path)?;
        self.validate_mount_source(source, fs_type)?;
        self.validate_mount_options(options, fs_type)?;
        Ok(())
    }
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, 
        "tmpfs" | "ramfs" | "fatfs" | "ext4" | "procfs" | "sysfs" | "devfs"
    )
}

/// Get default mount flags for a filesystem type
pub fn get_default_mount_flags(fs_type: &str) -> MountFlags {
    match fs_type {
        "procfs" | "sysfs" => MountFlags {
            readonly: false,
            noexec: true,
            nosuid: true,
            nodev: true,
        },
        "devfs" => MountFlags {
            readonly: false,
            noexec: true,
            nosuid: true,
            nodev: false, // devfs needs device access
        },
        _ => MountFlags::new(),
    }
}

/// Sanitize a mount path
pub fn sanitize_mount_path(path: &str) -> String {
    // Remove trailing slashes except for root
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        "/".into()
    } else {
        trimmed.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_validation() {
        let validator = MountValidator::new();
        
        // Valid paths
        assert!(validator.validate_mount_path("/mnt/data").is_ok());
        assert!(validator.validate_mount_path("/").is_ok());
        
        // Invalid paths
        assert!(validator.validate_mount_path("relative/path").is_err());
        assert!(validator.validate_mount_path("/proc/mounts").is_err());
        assert!(validator.validate_mount_path("/path/../escape").is_err());
        assert!(validator.validate_mount_path("/path\0null").is_err());
    }

    #[test]
    fn test_source_validation() {
        let validator = MountValidator::new();
        
        // Valid sources
        assert!(validator.validate_mount_source("tmpfs", "tmpfs").is_ok());
        assert!(validator.validate_mount_source("none", "procfs").is_ok());
        assert!(validator.validate_mount_source("/dev/sda1", "ext4").is_ok());
        
        // Invalid sources
        assert!(validator.validate_mount_source("", "tmpfs").is_err());
        assert!(validator.validate_mount_source("sda1", "ext4").is_err());
    }

    #[test]
    fn test_options_validation() {
        let validator = MountValidator::new();
        
        // Valid tmpfs options
        let mut options = MountOptions::new();
        options.fs_options.insert("size".into(), "1048576".into());
        assert!(validator.validate_mount_options(&options, "tmpfs").is_ok());
        
        // Invalid size
        options.fs_options.insert("size".into(), "100".into());
        assert!(validator.validate_mount_options(&options, "tmpfs").is_err());
        
        // Valid fatfs format option
        let mut options = MountOptions::new();
        options.fs_options.insert("format".into(), "true".into());
        assert!(validator.validate_mount_options(&options, "fatfs").is_ok());
        
        // Invalid format option
        options.fs_options.insert("format".into(), "yes".into());
        assert!(validator.validate_mount_options(&options, "fatfs").is_err());
    }

    #[test]
    fn test_filesystem_support() {
        assert!(is_filesystem_supported("tmpfs"));
        assert!(is_filesystem_supported("fatfs"));
        assert!(!is_filesystem_supported("unknown"));
    }

    #[test]
    fn test_path_sanitization() {
        assert_eq!(sanitize_mount_path("/mnt/data/"), "/mnt/data");
        assert_eq!(sanitize_mount_path("/"), "/");
        assert_eq!(sanitize_mount_path("////"), "/");
    }
}