use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::{Display, Formatter, Write};

use crate::device_tree::utils::{align_size, locate_block, read_aligned_be_u32, read_aligned_name};
use crate::device_tree::device_tree::InheritedValues;
use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::prop::{NodeProperty, PropertyValue};
use crate::device_tree::traits::HasNamedChildNode;

pub struct DeviceTreeNode<'a> {
    pub(crate) block_count: usize,
    name: &'a str,
    props: Vec<NodeProperty<'a>>,
    nodes: Vec<DeviceTreeNode<'a>>,
}

impl<'a> DeviceTreeNode<'a> {
    pub(crate) fn from_bytes(
        data: &'a [u8],
        header: &DeviceTreeHeader,
        start: usize,
        inherited: InheritedValues<'a>,
        mut owned: InheritedValues<'a>,
    ) -> Result<Self> {
        let block_start = align_size(start);
        if let Some(begin_node) = read_aligned_be_u32(data, block_start) {
            if begin_node == 0x1 {
                if let Some(name) = read_aligned_name(data, block_start + 1) {
                    let mut props = Vec::<NodeProperty>::new();
                    let mut nodes = Vec::<DeviceTreeNode>::new();
                    let name_blocks = if align_size(name.len() + 1) == 0 {
                        1
                    } else {
                        align_size(name.len() + 1)
                    };

                    let mut current_block = block_start + name_blocks + 1;

                    while let Some(token) = read_aligned_be_u32(data, current_block) {
                        match token {
                            0x3 => {
                                if let Ok(prop) = NodeProperty::from_bytes(
                                    data,
                                    header,
                                    locate_block(current_block),
                                    &inherited,
                                    &owned,
                                ) {
                                    current_block += prop.block_count;
                                    if nodes.is_empty() {
                                        if let PropertyValue::Integer(v) = prop.value() {
                                            owned.update(prop.name(), *v);
                                        }
                                    }
                                    props.push(prop);
                                } else {
                                    return Err(DeviceTreeError::ParsingFailed);
                                }
                            }
                            0x1 => {
                                if let Ok(node) = DeviceTreeNode::from_bytes(
                                    data,
                                    header,
                                    locate_block(current_block),
                                    owned.clone(),
                                    owned.clone(),
                                ) {
                                    current_block += node.block_count;
                                    nodes.push(node);
                                } else {
                                    return Err(DeviceTreeError::ParsingFailed);
                                }
                            }
                            0x2 | 0x9 => {
                                current_block += 1;
                                break;
                            }
                            _ => current_block += 1,
                        };
                    }
                    Ok(Self {
                        block_count: current_block - block_start,
                        name,
                        props,
                        nodes,
                    })
                } else {
                    Err(DeviceTreeError::ParsingFailed)
                }
            } else {
                Err(DeviceTreeError::InvalidToken)
            }
        } else {
            Err(DeviceTreeError::ParsingFailed)
        }
    }

    pub fn name(&self) -> &'a str {
        self.name
    }

    pub fn props(&self) -> &[NodeProperty<'a>] {
        &self.props
    }

    pub fn nodes(&self) -> &[DeviceTreeNode<'a>] {
        &self.nodes
    }
}

impl<'a> Display for DeviceTreeNode<'a> {
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

impl<'a> HasNamedChildNode for DeviceTreeNode<'a> {
    fn has_children(&self) -> bool {
        !self.nodes().is_empty()
    }

    fn find_child(&self, name: &str) -> Option<&DeviceTreeNode> {
        let mut option: Option<&DeviceTreeNode> = None;
        for i in &self.nodes {
            if i.name() == name {
                option = Some(i);
                break;
            }
        }
        option
    }
}

