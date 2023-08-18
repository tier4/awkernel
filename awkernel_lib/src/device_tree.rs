//! To read a device tree blob, use `from_bytes`, which does not depend on the global allocator,
//! and use the local allocator provided by this module.
//! Therefore, a device tree can be read without initialization of the heap memory.
//!
//! # Example
//!
//! ```
//! use awkernel_lib::device_tree;
//!
//! fn dtb_example1(dtb: &'static [u8]) {
//!     let tree = device_tree::from_bytes(dtb).unwrap();
//! }
//!
//! fn dtb_example2(dtb_addr: usize) {
//!     let tree = device_tree::from_address(dtb_addr).unwrap();
//! }
//! ```

pub mod error;
pub mod header;
pub mod node;
pub mod prop;
pub mod traits;
pub mod utils;

use self::{
    error::{DeviceTreeError, Result},
    header::DeviceTreeHeader,
    node::DeviceTreeNode,
    traits::HasNamedChildNode,
};
use crate::{
    console::{
        unsafe_print_hex_u128, unsafe_print_hex_u32, unsafe_print_hex_u64, unsafe_print_hex_u96,
        unsafe_puts,
    },
    local_heap,
};
use alloc::{collections::VecDeque, vec::Vec};
use core::{
    alloc::Allocator,
    fmt::{Display, Formatter},
    {mem::MaybeUninit, ptr::write_volatile},
};
use utils::safe_index;

const DEVICE_TREE_MEMORY_SIZE: usize = 1024 * 1024 * 4;

static mut MEMORY_POOL: [MaybeUninit<u8>; DEVICE_TREE_MEMORY_SIZE] =
    [MaybeUninit::new(0); DEVICE_TREE_MEMORY_SIZE];
static mut LOCAL_TLSF: Option<local_heap::TLSF> = None;
static mut LOCAL_ALLOCATOR: Option<local_heap::LocalHeap> = None;
static mut DEVICE_TREE: Option<DeviceTree<local_heap::LocalHeap<'static>>> = None;

/// Read a device tree blob.
pub fn from_bytes(
    bytes: &'static [u8],
) -> Result<&'static DeviceTree<'static, local_heap::LocalHeap<'static>>> {
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

/// Read a device tree blob from the address.
pub fn from_address(
    addr: usize,
) -> Result<&'static DeviceTree<'static, local_heap::LocalHeap<'static>>> {
    if let Some(tree) = unsafe { &DEVICE_TREE } {
        return Ok(tree);
    }

    let allocator = unsafe { get_allocator() };

    let tree = DeviceTree::from_address(addr, allocator.clone())?;

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

pub struct DeviceTree<'a, A: Allocator + Clone> {
    header: DeviceTreeHeader,
    root: DeviceTreeNode<'a, A>,
    allocator: A,
}

impl<'a, A: Allocator + Clone> DeviceTree<'a, A> {
    /// Checks if the magic number of the device tree is valid
    fn check_magic(magic: &[u8]) -> Result<()> {
        if magic != [0xd0, 0x0d, 0xfe, 0xed] {
            Err(DeviceTreeError::InvalidMagicNumber)
        } else {
            Ok(())
        }
    }

    /// Constructs a device tree from bytes
    pub fn from_bytes(data: &'a [u8], allocator: A) -> Result<Self> {
        Self::check_magic(&data[0..4])?;
        let header = DeviceTreeHeader::from_bytes(data)?;

        let root = DeviceTreeNode::from_bytes(
            data,
            &header,
            header.off_dt_struct as usize,
            InheritedValues::new(allocator.clone()),
            InheritedValues::new(allocator.clone()),
            allocator.clone(),
        )?;

        Ok(Self {
            header,
            root,
            allocator,
        })
    }

    /// Constructs a device tree from a specific address in memory
    pub fn from_address(addr: usize, allocator: A) -> Result<Self> {
        let header_bytes = unsafe { core::slice::from_raw_parts(addr as *const u8, 40) };
        Self::check_magic(&header_bytes[0..4])?;
        let header = DeviceTreeHeader::from_bytes(header_bytes)?;
        let data =
            unsafe { core::slice::from_raw_parts(addr as *const u8, header.total_size as usize) };
        Self::from_bytes(data, allocator)
    }

    pub fn magic(&self) -> usize {
        self.header.magic as usize
    }

    pub fn total_size(&self) -> usize {
        self.header.total_size as usize
    }

    pub fn off_dt_struct(&self) -> usize {
        self.header.off_dt_struct as usize
    }

    pub fn off_dt_strings(&self) -> usize {
        self.header.off_dt_strings as usize
    }

    pub fn off_mem_reserved(&self) -> usize {
        self.header.off_mem_reserved as usize
    }

    pub fn version(&self) -> usize {
        self.header.version as usize
    }

    pub fn last_comp_version(&self) -> usize {
        self.header.last_comp_version as usize
    }

    pub fn boot_cpu_id(&self) -> usize {
        self.header.boot_cpu_id as usize
    }

    pub fn size_dt_strings(&self) -> usize {
        self.header.size_dt_strings as usize
    }

    pub fn size_dt_struct(&self) -> usize {
        self.header.size_dt_struct as usize
    }

    pub fn root(&self) -> &DeviceTreeNode<'a, A> {
        &self.root
    }

    /// `num_cpus` is a function that counts the number of CPU nodes in a device tree.
    ///
    /// Specifically, this function searches for a child named "cpus" under the root of the device tree,
    /// and then counts the number of its children nodes whose names start with "cpu@".
    ///
    /// # Returns
    ///
    /// * `Result<usize>`: This function returns the number of CPUs in the form of a `Result<usize>`.
    ///   If it successfully counts the CPUs, it returns `Ok(num)`, where `num` is the number of CPUs.
    ///   If it fails to find the "cpus" child under the root, it returns `Err(DeviceTreeError::InvalidSemantics)`.
    ///
    /// # Errors
    ///
    /// This function returns an error of type `DeviceTreeError::InvalidSemantics` if no child named "cpus"
    /// can be found under the root of the device tree.
    pub fn num_cpus(&self) -> Result<usize> {
        let cpus = self
            .root()
            .find_child("cpus")
            .ok_or(DeviceTreeError::InvalidSemantics)?;

        let num = cpus.nodes().iter().fold(0, |acc, node| {
            if node.name().starts_with("cpu@") {
                acc + 1
            } else {
                acc
            }
        });

        Ok(num)
    }
}

/// Iterates over nodes in a device tree
pub struct DeviceTreeNodeIter<'a, A: Allocator + Clone> {
    queue: VecDeque<&'a DeviceTreeNode<'a, A>, A>,
}

impl<'a, A: Allocator + Clone> Iterator for DeviceTreeNodeIter<'a, A> {
    type Item = &'a DeviceTreeNode<'a, A>;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.queue.pop_front();
        match res {
            Some(node) if node.has_children() => {
                for i in node.nodes() {
                    self.queue.push_back(i);
                }
            }
            _ => {}
        }
        res
    }
}

impl<'a, A: Allocator + Clone> Display for DeviceTree<'a, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "{}", self.root)
    }
}

impl<'a, A: Allocator + Clone> IntoIterator for &'a DeviceTree<'a, A> {
    type Item = &'a DeviceTreeNode<'a, A>;
    type IntoIter = DeviceTreeNodeIter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        let mut queue = VecDeque::new_in(self.allocator.clone());
        queue.push_back(self.root());

        DeviceTreeNodeIter { queue }
    }
}

#[derive(Clone)]
pub(super) struct InheritedValues<'a, A: Allocator + Clone>(Vec<(&'a str, u64), A>);

impl<'a, A: Allocator + Clone> InheritedValues<'a, A> {
    /// Constructs a new InheritedValues instance
    pub const fn new(alloc: A) -> InheritedValues<'a, A> {
        InheritedValues(Vec::new_in(alloc))
    }

    /// Finds a value in the inherited values by its name
    pub fn find(&self, name: &str) -> Option<u64> {
        for i in &self.0 {
            if i.0 == name {
                return Some(i.1);
            }
        }
        None
    }

    /// Updates a value in the inherited values
    pub fn update(&mut self, name: &'a str, value: u64) -> Result<()> {
        let mut dirty = false;
        for i in 0..self.0.len() {
            if safe_index(&self.0, i)?.0 == name {
                self.0[i].1 = value;
                dirty = true;
                break;
            }
        }
        if !dirty {
            self.0.push((name, value));
        }

        Ok(())
    }
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
        unsafe_puts("\"\r\n");
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
                    unsafe_puts(">>\r\n");
                }
                prop::PropertyValue::Addresses(addrs) => {
                    unsafe_puts(": <<\r\n");
                    for (addr, size) in addrs {
                        print_white_spaces(depth + 2);

                        unsafe_puts("(0x");
                        print_address(*addr);
                        unsafe_puts(", 0x");
                        print_address(*size);
                        unsafe_puts("),\r\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts(">>\r\n");
                }
                prop::PropertyValue::String(s) => {
                    unsafe_puts(": \"");
                    unsafe_puts(s);
                    unsafe_puts("\"\r\n");
                }
                prop::PropertyValue::Integer(n) => {
                    unsafe_puts(": 0x");
                    unsafe_print_hex_u64(*n);
                    unsafe_puts("\r\n");
                }
                prop::PropertyValue::Integers(v) => {
                    unsafe_puts(": [\r\n");
                    for n in v.iter() {
                        print_white_spaces(depth + 2);
                        unsafe_puts("0x");
                        unsafe_print_hex_u64(*n);
                        unsafe_puts(",\r\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts("]\r\n");
                }
                prop::PropertyValue::PHandle(h) => {
                    unsafe_puts(": 0x");
                    unsafe_print_hex_u32(*h);
                    unsafe_puts("\r\n");
                }
                prop::PropertyValue::Ranges(ranges) => {
                    unsafe_puts(": [\r\n");

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
                        unsafe_puts("),\r\n");
                    }

                    print_white_spaces(depth + 1);
                    unsafe_puts("]\r\n");
                }
                prop::PropertyValue::Strings(strs) => {
                    unsafe_puts(": [\r\n");
                    for s in strs.iter() {
                        print_white_spaces(depth + 2);
                        unsafe_puts("\"");
                        unsafe_puts(s);
                        unsafe_puts("\",\r\n");
                    }
                    print_white_spaces(depth + 1);
                    unsafe_puts("]\r\n");
                }
                prop::PropertyValue::Unknown => {
                    unsafe_puts("unknown\r\n");
                }
                prop::PropertyValue::None => {
                    unsafe_puts("none\r\n");
                }
            }
        }
    }

    for node in node.nodes() {
        print_device_tree_node(node, depth + 1);
    }
}
