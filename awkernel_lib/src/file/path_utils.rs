//! Path manipulation utilities
//!
//! This module provides common path manipulation functions used throughout
//! the filesystem implementation. These functions are based on the reliable
//! implementations from the PathLike trait.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::format;

/// Get the filename from a path (everything after the last '/')
/// Based on PathLike::filename_internal
pub fn filename(path: &str) -> String {
    let index = path.rfind('/').map(|x| x + 1).unwrap_or(0);
    path[index..].to_string()
}

/// Get the file extension from a path
/// Based on PathLike::extension_internal
pub fn extension(path: &str) -> Option<String> {
    let filename = filename(path);
    let mut parts = filename.rsplitn(2, '.');
    let after = parts.next();
    let before = parts.next();
    match before {
        None | Some("") => None,
        _ => after.map(|x| x.to_string()),
    }
}

/// Get the parent directory of a path
/// Based on PathLike::parent_internal
pub fn parent_path(path: &str) -> String {
    let index = path.rfind('/');
    index.map(|idx| path[..idx].to_string()).unwrap_or_default()
}

/// Join two paths together, handling absolute paths, relative paths, and . and .. components
/// Based on PathLike::join_internal
pub fn join_path(base_path: &str, path: &str) -> Result<String, String> {
    if path.is_empty() {
        return Ok(base_path.to_string());
    }
    
    let mut new_components: Vec<&str> = Vec::with_capacity(
        base_path.chars().filter(|c| *c == '/').count()
            + path.chars().filter(|c| *c == '/').count()
            + 1,
    );
    
    let mut base = if path.starts_with('/') {
        "".to_string()
    } else {
        base_path.to_string()
    };
    
    // Prevent paths from ending in slashes unless this is just the root directory.
    if path.len() > 1 && path.ends_with('/') {
        return Err(format!("Invalid path: {}", path));
    }
    
    for component in path.split('/') {
        if component == "." || component.is_empty() {
            continue;
        }
        if component == ".." {
            if !new_components.is_empty() {
                new_components.truncate(new_components.len() - 1);
            } else {
                base = parent_path(&base);
            }
        } else {
            new_components.push(component);
        }
    }
    
    let mut result = base;
    result.reserve(
        new_components.len()
            + new_components
                .iter()
                .fold(0, |accum, part| accum + part.len()),
    );
    
    for component in new_components {
        result.push('/');
        result.push_str(component);
    }
    
    Ok(result)
}

/// Normalize a path by resolving . and .. components
/// This is a simplified version that just calls join_path with root
pub fn normalize_path(path: &str) -> String {
    // If path is absolute, join with empty base, otherwise join with root
    let base = if path.starts_with('/') { "" } else { "/" };
    join_path(base, path).unwrap_or_else(|_| path.to_string())
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