use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{Display, Formatter};

use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::node::DeviceTreeNode;
use crate::device_tree::traits::HasNamedChildNode;


pub struct DeviceTree<'a> {
    header: DeviceTreeHeader,
    root: DeviceTreeNode<'a>,
}

impl<'a> DeviceTree<'a> {
    pub fn from_bytes(data: &'a [u8]) -> Result<Self> {
        let magic = &data[0..4];
        if magic != [0xd0, 0x0d, 0xfe, 0xed] {
            return Err(DeviceTreeError::InvalidMagicNumber);
        }

        let header = DeviceTreeHeader::from_bytes(data)?;

        let root = DeviceTreeNode::from_bytes(
            data,
            &header,
            header.off_dt_struct as usize,
            InheritedValues::new(),
            InheritedValues::new(),
        )?;

        Ok(Self { header, root })
    }

    pub fn from_address(addr: usize) -> Result<Self> {
        let header_bytes = unsafe { core::slice::from_raw_parts(addr as *const u8, 40) };
        let magic = &header_bytes[0..4];
        if magic != [0xd0, 0x0d, 0xfe, 0xed] {
            return Err(DeviceTreeError::InvalidMagicNumber);
        }
        let header = DeviceTreeHeader::from_bytes(header_bytes)?;
        let data =
            unsafe { core::slice::from_raw_parts(addr as *const u8, header.total_size as usize) };
        Self::from_bytes(data)
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


    pub fn root(&self) -> &DeviceTreeNode {
        &self.root
    }
}


pub struct DeviceTreeNodeIter<'a> {
    queue: VecDeque<&'a DeviceTreeNode<'a>>,
}

impl<'a> Iterator for DeviceTreeNodeIter<'a> {
    type Item = &'a DeviceTreeNode<'a>;

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

impl<'a> Display for DeviceTree<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "{}", self.root)
    }
}

impl<'a> IntoIterator for &'a DeviceTree<'a> {
    type Item = &'a DeviceTreeNode<'a>;
    type IntoIter = DeviceTreeNodeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        DeviceTreeNodeIter {
            queue: VecDeque::from([self.root()]),
        }
    }
}

#[derive(Clone)]
pub(crate) struct InheritedValues<'a>(Vec<(&'a str, u64)>);

impl<'a> InheritedValues<'a> {
    pub const fn new() -> InheritedValues<'a> {
        InheritedValues(vec![])
    }

    pub fn find(&self, name: &str) -> Option<u64> {
        for i in &self.0 {
            if i.0 == name {
                return Some(i.1);
            }
        }
        None
    }

    pub fn update(&mut self, name: &'a str, value: u64) {
        let mut dirty = false;
        for i in 0..self.0.len() {
            if self.0[i].0 == name {
                self.0[i].1 = value;
                dirty = true;
                break;
            }
        }
        if !dirty {
            self.0.push((name, value));
        }
    }
}
