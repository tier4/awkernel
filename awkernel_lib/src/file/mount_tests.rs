//! Comprehensive tests for the mount table implementation

#[cfg(test)]
mod tests {
    use alloc::sync::Arc;
    use alloc::collections::BTreeMap;
    use crate::file::{
        mount::{MountTable, get_mount_table, mount, unmount, list_mounts},
        mount_types::{MountOptions, MountFlags, MountError, MountTable as MountTableTrait},
        mount_lifecycle::{MountLifecycleManager, TrackedFileHandle},
        mount_validation::{MountValidator, is_filesystem_supported},
    };

    #[test]
    fn test_mount_table_initialization() {
        let table1 = get_mount_table();
        let table2 = get_mount_table();
        
        // Should return the same instance
        assert!(Arc::ptr_eq(&table1, &table2));
    }

    #[test]
    fn test_basic_mount_unmount() {
        let _table = get_mount_table();
        
        // Mount a filesystem
        let mount_id = mount("/test", "/dev/test", "tmpfs", MountOptions::new())
            .expect("Mount should succeed");
        assert!(mount_id > 0);
        
        // Verify mount exists
        let mounts = list_mounts();
        assert_eq!(mounts.len(), 1);
        assert_eq!(mounts[0].path, "/test");
        
        // Unmount
        unmount("/test").expect("Unmount should succeed");
        
        // Verify mount removed
        let mounts = list_mounts();
        assert_eq!(mounts.len(), 0);
    }

    #[test]
    fn test_duplicate_mount_error() {
        let _table = get_mount_table();
        
        // First mount should succeed
        mount("/dup", "/dev/test1", "tmpfs", MountOptions::new())
            .expect("First mount should succeed");
        
        // Second mount at same path should fail
        let result = mount("/dup", "/dev/test2", "tmpfs", MountOptions::new());
        assert!(matches!(result, Err(MountError::AlreadyMounted(_))));
        
        // Cleanup
        unmount("/dup").ok();
    }

    #[test]
    fn test_unmount_nonexistent() {
        let _table = get_mount_table();
        
        let result = unmount("/nonexistent");
        assert!(matches!(result, Err(MountError::NotMounted(_))));
    }

    #[test]
    fn test_mount_resolution() {
        let mut table = MountTable::new();
        
        // Create mount hierarchy
        table.mount("/", "/dev/root", "ext4", MountOptions::new()).unwrap();
        table.mount("/home", "/dev/home", "ext4", MountOptions::new()).unwrap();
        table.mount("/home/user", "/dev/user", "ext4", MountOptions::new()).unwrap();
        table.mount("/var", "/dev/var", "ext4", MountOptions::new()).unwrap();
        
        // Test resolution
        assert_eq!(table.get_mount_info("/").unwrap().path, "/");
        assert_eq!(table.get_mount_info("/etc/config").unwrap().path, "/");
        assert_eq!(table.get_mount_info("/home").unwrap().path, "/home");
        assert_eq!(table.get_mount_info("/home/user/docs").unwrap().path, "/home/user");
        assert_eq!(table.get_mount_info("/var/log").unwrap().path, "/var");
    }

    #[test]
    fn test_mount_flags() {
        let _table = get_mount_table();
        
        let mut options = MountOptions::new();
        options.flags.readonly = true;
        options.flags.noexec = true;
        
        mount("/readonly", "/dev/test", "tmpfs", options).unwrap();
        
        let mounts = list_mounts();
        let mount = mounts.iter().find(|m| m.path == "/readonly").unwrap();
        assert!(mount.flags.readonly);
        assert!(mount.flags.noexec);
        
        unmount("/readonly").ok();
    }

    #[test]
    fn test_mount_options() {
        let _table = get_mount_table();
        
        let mut options = MountOptions::new();
        options.add_option("size", "1048576");
        options.add_option("mode", "0755");
        
        mount("/opts", "/dev/test", "tmpfs", options.clone()).unwrap();
        
        let mounts = list_mounts();
        let mount = mounts.iter().find(|m| m.path == "/opts").unwrap();
        assert_eq!(mount.fs_options.get("size").unwrap(), "1048576");
        assert_eq!(mount.fs_options.get("mode").unwrap(), "0755");
        
        unmount("/opts").ok();
    }

    #[test]
    fn test_path_normalization() {
        let mut table = MountTable::new();
        
        // Mount with trailing slash
        table.mount("/test/", "/dev/test", "tmpfs", MountOptions::new()).unwrap();
        
        // Should find with or without trailing slash
        assert!(table.is_mount_point("/test"));
        assert!(table.is_mount_point("/test/"));
        
        // Mount with ./ and ../
        let result = table.mount("/test/../other", "/dev/other", "tmpfs", MountOptions::new());
        assert!(result.is_ok());
        
        // Should be normalized to /other
        assert!(table.is_mount_point("/other"));
    }

    #[test]
    fn test_mount_lifecycle() {
        let manager = Arc::new(MountLifecycleManager::new());
        let mount_info = crate::file::mount_types::MountInfo {
            path: "/lifecycle".into(),
            source: "/dev/test".into(),
            fs_type: "tmpfs".into(),
            flags: MountFlags::new(),
            mount_id: 1,
            fs_options: BTreeMap::new(),
        };
        
        let _lifecycle = manager.register_mount(mount_info);
        
        // Should be able to unmount initially
        assert!(manager.unregister_mount("/lifecycle").is_ok());
        
        // Re-register for file handle test
        let mount_info = crate::file::mount_types::MountInfo {
            path: "/lifecycle".into(),
            source: "/dev/test".into(),
            fs_type: "tmpfs".into(),
            flags: MountFlags::new(),
            mount_id: 2,
            fs_options: BTreeMap::new(),
        };
        manager.register_mount(mount_info);
        
        // Create a tracked file handle
        let _handle = TrackedFileHandle::new(&manager, "/lifecycle").unwrap();
        
        // Should not be able to unmount with open file
        assert!(manager.unregister_mount("/lifecycle").is_err());
        
        // Drop handle
        drop(_handle);
        
        // Should be able to unmount now
        assert!(manager.unregister_mount("/lifecycle").is_ok());
    }

    #[test]
    fn test_mount_validation() {
        let mut validator = MountValidator::new();
        validator.add_allowed_prefix("/mnt".into());
        validator.add_allowed_prefix("/media".into());
        
        // Valid paths
        assert!(validator.validate_mount_path("/mnt/usb").is_ok());
        assert!(validator.validate_mount_path("/media/cdrom").is_ok());
        
        // Invalid paths
        assert!(validator.validate_mount_path("/home").is_err()); // Not in allowed
        assert!(validator.validate_mount_path("/proc/mounts").is_err()); // Forbidden
        assert!(validator.validate_mount_path("relative").is_err()); // Not absolute
        
        // Valid sources
        assert!(validator.validate_mount_source("/dev/sda1", "ext4").is_ok());
        assert!(validator.validate_mount_source("tmpfs", "tmpfs").is_ok());
        
        // Invalid sources
        assert!(validator.validate_mount_source("sda1", "ext4").is_err());
        assert!(validator.validate_mount_source("", "tmpfs").is_err());
    }

    #[test]
    fn test_filesystem_support() {
        assert!(is_filesystem_supported("tmpfs"));
        assert!(is_filesystem_supported("fatfs"));
        assert!(is_filesystem_supported("ext4"));
        assert!(!is_filesystem_supported("unknownfs"));
    }

    #[test]
    fn test_concurrent_mount_operations() {
        use alloc::vec;
        
        let table = Arc::new(MountTable::new());
        let mut results = vec![];
        
        // Simulate concurrent mounts
        for i in 0..10 {
            let path = format!("/concurrent{}", i);
            let source = format!("/dev/test{}", i);
            
            // In real code this would be in separate threads
            unsafe {
                let table_ptr = Arc::as_ptr(&table) as *mut MountTable;
                let result = (*table_ptr).mount(&path, &source, "tmpfs", MountOptions::new());
                results.push(result);
            }
        }
        
        // All should succeed
        assert!(results.iter().all(|r| r.is_ok()));
        
        // Verify all mounts exist
        assert_eq!(table.list_mounts().len(), 10);
    }

    #[test]
    fn test_mount_boundary_detection() {
        let mut table = MountTable::new();
        
        table.mount("/mnt", "/dev/mnt", "ext4", MountOptions::new()).unwrap();
        table.mount("/mntdata", "/dev/data", "ext4", MountOptions::new()).unwrap();
        
        // /mnt/file should resolve to /mnt, not /mntdata
        let info = table.get_mount_info("/mnt/file").unwrap();
        assert_eq!(info.path, "/mnt");
        
        // /mntdata/file should resolve to /mntdata
        let info = table.get_mount_info("/mntdata/file").unwrap();
        assert_eq!(info.path, "/mntdata");
    }

    #[test]
    fn test_deep_mount_hierarchy() {
        let mut table = MountTable::new();
        
        // Create deep hierarchy
        let paths = vec![
            "/",
            "/a",
            "/a/b",
            "/a/b/c",
            "/a/b/c/d",
            "/a/b/c/d/e",
        ];
        
        for (i, path) in paths.iter().enumerate() {
            table.mount(path, &format!("/dev/dev{}", i), "tmpfs", MountOptions::new()).unwrap();
        }
        
        // Test resolution at each level
        assert_eq!(table.get_mount_info("/file").unwrap().path, "/");
        assert_eq!(table.get_mount_info("/a/file").unwrap().path, "/a");
        assert_eq!(table.get_mount_info("/a/b/c/d/e/file").unwrap().path, "/a/b/c/d/e");
    }
}