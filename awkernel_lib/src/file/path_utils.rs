//! Path manipulation utilities
//!
//! This module provides common path manipulation functions used throughout
//! the filesystem implementation.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::format;

/// Normalize a path by resolving . and .. components
pub fn normalize_path(path: &str) -> String {
    let mut components = Vec::new();
    
    for component in path.split('/').filter(|s| !s.is_empty()) {
        match component {
            "." => {} // Skip current directory
            ".." => { components.pop(); } // Go up one level
            _ => components.push(component),
        }
    }
    
    if components.is_empty() {
        "/".to_string()
    } else {
        format!("/{}", components.join("/"))
    }
}

/// Check if a path is a subpath of another
pub fn is_subpath(parent: &str, child: &str) -> bool {
    let parent = normalize_path(parent);
    let child = normalize_path(child);
    
    // Special case: root is parent of everything except itself
    if parent == "/" {
        return true; // Everything is a subpath of root
    }
    
    child.starts_with(&parent) && 
    (child.len() == parent.len() || child.chars().nth(parent.len()) == Some('/'))
}

/// Get the relative path from parent to child
pub fn relative_path(parent: &str, child: &str) -> Option<String> {
    let parent = normalize_path(parent);
    let child = normalize_path(child);
    
    if !is_subpath(&parent, &child) {
        return None;
    }
    
    if parent == "/" {
        Some(child[1..].to_string())
    } else if child.len() > parent.len() + 1 {
        Some(child[parent.len() + 1..].to_string())
    } else {
        Some(String::new())
    }
}