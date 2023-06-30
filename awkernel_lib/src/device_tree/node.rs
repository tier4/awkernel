use alloc::string::String;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::fmt::{Display, Formatter, Write};

use crate::device_tree::device_tree::InheritedValues;
use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::prop::{NodeProperty, PropertyValue};
use crate::device_tree::traits::HasNamedChildNode;
use crate::device_tree::utils::{align_size, locate_block, read_aligned_be_u32, read_aligned_name};

/// Represents a node in the device tree
pub struct DeviceTreeNode<'a, A: Allocator + Clone> {
    pub(crate) block_count: usize,
    name: &'a str,
    props: Vec<NodeProperty<'a, A>, A>,
    nodes: Vec<DeviceTreeNode<'a, A>, A>,
}

impl<'a, A: Allocator + Clone> DeviceTreeNode<'a, A> {
    /// Construct a DeviceTreeNode from raw bytes
    pub(crate) fn from_bytes(
        data: &'a [u8],
        header: &DeviceTreeHeader,
        start: usize,
        inherited: InheritedValues<'a>,
        owned: InheritedValues<'a>,
        allocator: A,
    ) -> Result<Self> {
        let block_start = align_size(start);

        let begin_node =
            read_aligned_be_u32(data, block_start).ok_or(DeviceTreeError::ParsingFailed)?;

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
}

/// Parse properties and nodes
fn parse_properties_and_nodes<'a, A: Allocator + Clone>(
    data: &'a [u8],
    header: &DeviceTreeHeader,
    block_start: usize,
    name: &'a str,
    inherited: InheritedValues<'a>,
    mut owned: InheritedValues<'a>,
    allocator: A,
) -> Result<(
    Vec<NodeProperty<'a, A>, A>,
    Vec<DeviceTreeNode<'a, A>, A>,
    usize,
)> {
    let mut props = Vec::<NodeProperty<'a, A>, A>::new_in(allocator.clone());
    let mut nodes = Vec::<DeviceTreeNode<'a, A>, A>::new_in(allocator.clone());

    let name_blocks = if align_size(name.len() + 1) == 0 {
        1
    } else {
        align_size(name.len() + 1)
    };

    let mut current_block = block_start + name_blocks + 1;

    while let Some(token) = read_aligned_be_u32(data, current_block) {
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
                        owned.update(prop.name(), *v);
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
        if let Err(err) = writeln!(f, "{} {{", self.name) {
            return Err(err);
        }
        for i in &self.props {
            if let Err(err) = writeln!(f, "\t{}", i) {
                return Err(err);
            }
        }
        for i in &self.nodes {
            let mut buffer = String::new();
            if let Err(err) = write!(buffer, "\t{}", i) {
                return Err(err);
            }
            let mut first_line = true;
            for j in buffer.split('\n') {
                if !first_line {
                    if let Err(err) = write!(f, "\t") {
                        return Err(err);
                    }
                } else {
                    first_line = false;
                }
                if let Err(err) = writeln!(f, "{}", j) {
                    return Err(err);
                }
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
