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
use crate::{
    console::{
        unsafe_print_hex_u128, unsafe_print_hex_u32, unsafe_print_hex_u64, unsafe_print_hex_u96,
        unsafe_puts,
    },
    local_heap,
};
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

/// Print device tree nodes without the global allocator.
///
/// # Safety
///
/// This function do not acquire lock to print `data`,
/// and should be called for critical errors or booting.
pub unsafe fn print_device_tree_node(
    node: &node::DeviceTreeNode<'static, local_heap::LocalHeap>,
    depth: usize,
) {
    fn print_white_spaces(depth: usize) {
        for _ in 0..depth {
            unsafe { unsafe_puts("    ") };
        }
    }

    unsafe fn print_address(address: utils::Addr) {
        match address {
            utils::Addr::Zero => unsafe_puts("0"),
            utils::Addr::U32(num) => unsafe_print_hex_u32(num as u32),
            utils::Addr::U64(num) => unsafe_print_hex_u64(num),
            utils::Addr::U96(num) => unsafe_print_hex_u96(num),
            utils::Addr::U128(num) => unsafe_print_hex_u128(num),
        }
    }

    unsafe {
        print_white_spaces(depth);
        unsafe_puts("\"");
        unsafe_puts(node.name());
        unsafe_puts("\"\n");
    }

    for prop in node.props() {
        unsafe {
            print_white_spaces(depth + 1);
            unsafe_puts(prop.name());

            match prop.value() {
                prop::PropertyValue::Address(x, y) => {
                    unsafe_puts(": <<0x");
                    print_address(*x);
                    unsafe_puts(", 0x");
                    print_address(*y);
                    unsafe_puts(">>\n");
                }
                prop::PropertyValue::Addresses(addrs) => {
                    unsafe_puts(": <<\n");
                    for (addr, size) in addrs {
                        print_white_spaces(depth + 2);

                        unsafe_puts("(0x");
                        print_address(*addr);
                        unsafe_puts(", 0x");
                        print_address(*size);
                        unsafe_puts("),\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts(">>\n");
                }
                prop::PropertyValue::String(s) => {
                    unsafe_puts(": \"");
                    unsafe_puts(s);
                    unsafe_puts("\"\n");
                }
                prop::PropertyValue::Integer(n) => {
                    unsafe_puts(": 0x");
                    unsafe_print_hex_u64(*n);
                    unsafe_puts("\n");
                }
                prop::PropertyValue::Integers(v) => {
                    unsafe_puts(": [\n");
                    for n in v.iter() {
                        print_white_spaces(depth + 2);
                        unsafe_puts("0x");
                        unsafe_print_hex_u64(*n);
                        unsafe_puts(",\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts("]\n");
                }
                prop::PropertyValue::PHandle(h) => {
                    unsafe_puts(": 0x");
                    unsafe_print_hex_u32(*h);
                    unsafe_puts("\n");
                }
                prop::PropertyValue::Ranges(ranges) => {
                    unsafe_puts(": [\n");

                    for r in ranges {
                        print_white_spaces(depth + 2);

                        unsafe_puts("(0x");
                        print_address(r.range.0);
                        unsafe_puts(", ");

                        unsafe_puts("0x");
                        print_address(r.range.1);
                        unsafe_puts(", ");

                        unsafe_puts("0x");
                        print_address(r.range.2);
                        unsafe_puts("),\n");
                    }

                    print_white_spaces(depth + 1);
                    unsafe_puts("]\n");
                }
                prop::PropertyValue::Strings(strs) => {
                    unsafe_puts(": [\n");
                    for s in strs.iter() {
                        print_white_spaces(depth + 2);
                        unsafe_puts("\"");
                        unsafe_puts(s);
                        unsafe_puts("\",\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts("]\n");
                }
                prop::PropertyValue::Unknown => {
                    unsafe_puts("unknown\n");
                }
                prop::PropertyValue::None => {
                    unsafe_puts("none\n");
                }
            }
        }
    }

    for node in node.nodes() {
        print_device_tree_node(node, depth + 1);
    }
}
