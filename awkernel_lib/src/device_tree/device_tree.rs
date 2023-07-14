use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::fmt::{Display, Formatter};

use super::utils::safe_index;
use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::node::DeviceTreeNode;
use crate::device_tree::traits::HasNamedChildNode;

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
