//! To read a device tree blob, use `from_bytes`, which does not depend on the global allocator,
//! and use the local allocator provided by this module.
//! Therefore, a device tree can be read without initialization of the heap memory.
//!
//! # Example
//!
//! ```
//! use awkernel_lib::device_tree;
//! fn dtb_example(dtb: &[u8]) {
//!     let tree = device_tree::from_bytes(dtb).unwrap();
//! }
//! ```

pub mod device_tree;
pub mod error;
pub mod header;
pub mod node;
pub mod prop;
pub mod traits;
pub mod utils;

use self::{device_tree::DeviceTree, error::DeviceTreeError};
use crate::local_heap;
use core::{mem::MaybeUninit, ptr::write_volatile};

const DEVICE_TREE_MEMORY_SIZE: usize = 1024 * 1024 * 4;

static mut MEMORY_POOL: [MaybeUninit<u8>; DEVICE_TREE_MEMORY_SIZE] =
    [MaybeUninit::new(0); DEVICE_TREE_MEMORY_SIZE];
static mut LOCAL_TLSF: Option<local_heap::TLSF> = None;
static mut LOCAL_ALLOCATOR: Option<local_heap::LocalHeap> = None;
static mut DEVICE_TREE: Option<DeviceTree<local_heap::LocalHeap<'static>>> = None;

/// Read a device tree blog.
pub fn from_bytes(
    bytes: &'static [u8],
) -> Result<&'static DeviceTree<'static, local_heap::LocalHeap<'static>>, DeviceTreeError> {
    if let Some(tree) = unsafe { &DEVICE_TREE } {
        return Ok(tree);
    }

    let allocator = unsafe { get_allocator() };

    let tree = DeviceTree::from_bytes(bytes, allocator.clone())?;

    unsafe {
        DEVICE_TREE = Some(tree);
        Ok(DEVICE_TREE.as_ref().unwrap())
    }
}

unsafe fn get_allocator() -> &'static mut local_heap::LocalHeap<'static> {
    if let Some(allocator) = &mut LOCAL_ALLOCATOR {
        return allocator;
    }

    let tlsf = local_heap::TLSF::new(&mut MEMORY_POOL);

    write_volatile(&mut LOCAL_TLSF, Some(tlsf));

    let ref_tlsf = LOCAL_TLSF.as_mut().unwrap();
    let allocator = local_heap::LocalHeap::new(ref_tlsf);

    write_volatile(&mut LOCAL_ALLOCATOR, Some(allocator));

    LOCAL_ALLOCATOR.as_mut().unwrap()
}
