use core::alloc::Allocator;
use core::fmt::{Display, Formatter, Write};

use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::prop::{NodeProperty, PropertyValue};
use crate::device_tree::traits::HasNamedChildNode;
use crate::device_tree::utils::{align_size, locate_block, read_aligned_be_u32, read_aligned_name};
use crate::device_tree::InheritedValues;

use super::utils::Addr;

#[cfg(not(feature = "std"))]
use alloc::{string::String, vec::Vec};

type VecNodeProp<'a, A> = Vec<NodeProperty<'a, A>, A>;
type VecDevTreeNode<'a, A> = Vec<DeviceTreeNode<'a, A>, A>;

/// Represents a node in the device tree
pub struct DeviceTreeNode<'a, A: Allocator + Clone> {
    pub(super) block_count: usize,
    name: &'a str,
    props: VecNodeProp<'a, A>,
    nodes: VecDevTreeNode<'a, A>,
}

impl<'a, A: Allocator + Clone> DeviceTreeNode<'a, A> {
    /// Construct a DeviceTreeNode from raw bytes
    pub(super) fn from_bytes(
        data: &'a [u8],
        header: &DeviceTreeHeader,
        start: usize,
        inherited: InheritedValues<'a, A>,
        owned: InheritedValues<'a, A>,
        allocator: A,
    ) -> Result<Self> {
        let block_start = align_size(start);

        let begin_node = read_aligned_be_u32(data, block_start)?;

        if begin_node != 0x1 {
            return Err(DeviceTreeError::InvalidToken);
        }

        let name =
            read_aligned_name(data, block_start + 1).ok_or(DeviceTreeError::ParsingFailed)?;

        let (props, nodes, block_count) = parse_properties_and_nodes(
            data,
            header,
            block_start,
            name,
            inherited,
            owned,
            allocator,
        )?;

        Ok(Self {
            block_count,
            name,
            props,
            nodes,
        })
    }

    pub fn name(&self) -> &'a str {
        self.name
    }

    pub fn props(&self) -> &[NodeProperty<'a, A>] {
        &self.props
    }

    pub fn nodes(&self) -> &[Self] {
        &self.nodes
    }

    pub fn get_arrayed_node(&'a self, abs_path: &str) -> Result<ArrayedNode<'a, A>> {
        let mut result = ArrayedNode::new();
        let mut node = self;

        let mut path_it = abs_path.split('/');
        let first = path_it.next().ok_or(DeviceTreeError::InvalidSemantics)?;

        if !first.is_empty() {
            return Err(DeviceTreeError::InvalidSemantics);
        }

        result.push(node)?;

        for p in path_it {
            node = node
                .nodes()
                .iter()
                .find(|n| n.name() == p)
                .ok_or(DeviceTreeError::InvalidSemantics)?;
            result.push(node)?;
        }

        Ok(result)
    }

    pub fn get_property(&'a self, property: &str) -> Option<&'a NodeProperty<'a, A>> {
        self.props().iter().find(|p| p.name() == property)
    }

    /// Check if the node is compatible with the given names
    pub fn compatible(&self, names: &[&str]) -> bool {
        let Some(prop) = self.get_property("compatible") else {
            return false;
        };

        match prop.value() {
            PropertyValue::String(s) => names.iter().any(|n| n == s),
            PropertyValue::Strings(v) => {
                for name in names {
                    if v.iter().any(|s| s == name) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Get the node by phandle.
    pub fn get_node_by_phandle(&'a self, phandle: u32) -> Option<&'a DeviceTreeNode<'a, A>> {
        for node in self.nodes() {
            if let Some(prop) = node.get_property("phandle") {
                match prop.value() {
                    PropertyValue::Integer(v) => {
                        if *v as u32 == phandle {
                            return Some(node);
                        }
                    }
                    PropertyValue::PHandle(v) => {
                        if *v == phandle {
                            return Some(node);
                        }
                    }
                    _ => {}
                }
            }

            if let Some(n) = node.get_node_by_phandle(phandle) {
                return Some(n);
            }
        }

        None
    }
}

/// Parse properties and nodes
fn parse_properties_and_nodes<'a, A: Allocator + Clone>(
    data: &'a [u8],
    header: &DeviceTreeHeader,
    block_start: usize,
    name: &'a str,
    inherited: InheritedValues<'a, A>,
    mut owned: InheritedValues<'a, A>,
    allocator: A,
) -> Result<(VecNodeProp<'a, A>, VecDevTreeNode<'a, A>, usize)> {
    let mut props = Vec::<NodeProperty<'a, A>, A>::new_in(allocator.clone());
    let mut nodes = Vec::<DeviceTreeNode<'a, A>, A>::new_in(allocator.clone());

    let name_blocks = if align_size(name.len() + 1) == 0 {
        1
    } else {
        align_size(name.len() + 1)
    };

    let mut current_block = block_start + name_blocks + 1;

    while let Ok(token) = read_aligned_be_u32(data, current_block) {
        match token {
            0x3 => {
                let prop = NodeProperty::from_bytes(
                    data,
                    header,
                    locate_block(current_block),
                    &inherited,
                    &owned,
                    allocator.clone(),
                )
                .map_err(|_| DeviceTreeError::ParsingFailed)?;

                current_block += prop.block_count;
                if nodes.is_empty() {
                    if let PropertyValue::Integer(v) = prop.value() {
                        owned.update(prop.name(), *v)?;
                    }
                }
                props.push(prop);
            }
            0x1 => {
                let node = DeviceTreeNode::from_bytes(
                    data,
                    header,
                    locate_block(current_block),
                    owned.clone(),
                    owned.clone(),
                    allocator.clone(),
                )
                .map_err(|_| DeviceTreeError::ParsingFailed)?;

                current_block += node.block_count;
                nodes.push(node);
            }
            0x2 | 0x9 => {
                current_block += 1;
                break;
            }
            _ => current_block += 1,
        };
    }

    let block_count = current_block - block_start;
    Ok((props, nodes, block_count))
}

impl<'a, A: Allocator + Clone> Display for DeviceTreeNode<'a, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "{} {{", self.name)?;

        for i in &self.props {
            writeln!(f, "\t{}", i)?;
        }

        for i in &self.nodes {
            let mut buffer = String::new();
            write!(buffer, "\t{}", i)?;
            let mut first_line = true;
            for j in buffer.split('\n') {
                if !first_line {
                    write!(f, "\t")?;
                } else {
                    first_line = false;
                }
                writeln!(f, "{}", j)?;
            }
        }
        write!(f, "}};")
    }
}

/// Check if a node has children
impl<'a, A: Allocator + Clone> HasNamedChildNode<A> for DeviceTreeNode<'a, A> {
    fn has_children(&self) -> bool {
        !self.nodes().is_empty()
    }

    fn find_child(&self, name: &str) -> Option<&Self> {
        let mut option: Option<&Self> = None;
        for i in &self.nodes {
            if i.name() == name {
                option = Some(i);
                break;
            }
        }
        option
    }
}

const ARRAYED_NODE_SIZE: usize = 8;

#[derive(Clone)]
pub struct ArrayedNode<'a, A: Allocator + Clone> {
    array: [Option<&'a DeviceTreeNode<'a, A>>; ARRAYED_NODE_SIZE],
    index: usize,
}

impl<'a, A: Allocator + Clone> Default for ArrayedNode<'a, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, A: Allocator + Clone> ArrayedNode<'a, A> {
    pub fn new() -> Self {
        ArrayedNode {
            array: [None; ARRAYED_NODE_SIZE],
            index: 0,
        }
    }

    /// Push a node.
    pub fn push(&mut self, node: &'a DeviceTreeNode<'a, A>) -> Result<()> {
        if self.index >= ARRAYED_NODE_SIZE {
            return Err(DeviceTreeError::NotEnoughLength);
        }

        self.array[self.index] = Some(node);
        self.index += 1;

        Ok(())
    }

    /// Get the leaf node.
    pub fn get_leaf_node(&self) -> Option<&'a DeviceTreeNode<'a, A>> {
        for node in self.array.iter().rev() {
            if node.is_some() {
                return Some(node.unwrap());
            }
        }

        None
    }

    /// Get the base address of the device.
    /// The base address is calculated by using the ranges of the parent nodes.
    ///
    /// For example, `device@0`'s `reg` is `<0x0 0x1000>`, and the parent node has a ranges
    /// of `<0x0 0x40000000 0x1000>` as follows.
    /// This function will return `0x40001000` as the base address.
    ///
    /// ```plain
    /// / {
    ///     #address-cells = <1>;
    ///     #size-cells = <1>;
    ///
    ///     soc {
    ///         #address-cells = <1>;
    ///         #size-cells = <1>;
    ///         compatible = "simple-bus";
    ///         ranges = <0x0 0x40000000 0x1000>;
    ///
    ///         device@0 {
    ///             compatible = "vendor,device";
    ///             reg = <0x0 0x1000>;
    ///         };
    ///     };
    /// };
    /// ```
    pub fn get_address(&self, index: usize) -> Result<u128> {
        let mut leaf = None;
        let mut base_addr = 0;
        'node: for node in self.array.iter().rev() {
            if node.is_some() {
                // Find the leaf node and its base address.
                if leaf.is_none() {
                    let tail = node.as_ref().unwrap();
                    let reg = tail
                        .props()
                        .iter()
                        .find(|prop| prop.name() == "reg")
                        .ok_or(DeviceTreeError::InvalidSemantics)?;

                    match reg.value() {
                        PropertyValue::Address(base, _len) => {
                            if index != 0 {
                                return Err(DeviceTreeError::NotFound);
                            }
                            base_addr = base.to_u128();
                        }
                        PropertyValue::Addresses(v) => {
                            let (base, _len) = v.get(index).ok_or(DeviceTreeError::NotFound)?;
                            base_addr = base.to_u128();
                        }
                        _ => return Err(DeviceTreeError::InvalidSemantics),
                    }

                    leaf = Some(tail);
                } else {
                    let n = node.as_ref().unwrap();
                    if let Some(ranges) = n.get_property("ranges") {
                        match ranges.value() {
                            PropertyValue::Ranges(rgs) => {
                                // `base_addr` must be in the ranges,
                                // and it will be mapped by the ranges.
                                for range in rgs {
                                    if let Some(addr) = range.map_to(Addr::U128(base_addr)) {
                                        base_addr = addr;
                                        continue 'node;
                                    }
                                }

                                // Invalid address.
                                return Err(DeviceTreeError::MemoryAccessFailed);
                            }
                            PropertyValue::None => (),
                            _ => return Err(DeviceTreeError::InvalidSemantics), // Must be ranges.
                        }
                    }
                }
            }
        }

        Ok(base_addr)
    }
}
