use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::fmt::{Display, Formatter};

use crate::device_tree::error::DeviceTreeError::{NotEnoughLength, ParsingFailed};
use crate::device_tree::error::Result;
use crate::device_tree::header::DeviceTreeHeader;
use crate::device_tree::utils::{
    align_block, align_size, locate_block, read_aligned_be_number, read_aligned_be_u32,
    read_aligned_sized_strings, read_name, BLOCK_SIZE,
};
use crate::device_tree::InheritedValues;

use super::utils::{safe_index, Addr};

pub struct Range {
    pub range: (Addr, Addr, Addr),
}

impl Range {
    pub fn map_to(&self, addr: Addr) -> Option<u128> {
        fn to_u128(addr: Addr) -> u128 {
            match addr {
                Addr::Zero => 0,
                Addr::U32(a) | Addr::U64(a) => a as u128,
                Addr::U96(a) | Addr::U128(a) => a,
            }
        }

        let src = to_u128(addr);
        let from_addr = to_u128(self.range.0);
        let to_addr = to_u128(self.range.1);
        let size = to_u128(self.range.2);

        if (from_addr..(from_addr + size)).contains(&src) {
            Some(src - from_addr + to_addr)
        } else {
            None
        }
    }
}

/// Enum representing different possible property values in a Device Tree
pub enum PropertyValue<'a, A: Allocator + Clone> {
    None,
    Integer(u64),
    Integers(Vec<u64, A>),
    PHandle(u32),
    String(&'a str),
    Strings(Vec<&'a str, A>),
    Address(Addr, Addr),
    Addresses(Vec<(Addr, Addr), A>),
    Ranges(Vec<Range, A>),
    Unknown,
}

/// Implements the Display trait for PropertyValue to allow it to be printed
impl<'a, A: Allocator + Clone> Display for PropertyValue<'a, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            PropertyValue::None => write!(f, ""),
            PropertyValue::Integer(it) => write!(f, "<{:#x}>", it),
            PropertyValue::Integers(it) => write!(
                f,
                "<{}>",
                it.iter()
                    .map(|x| format!("{:#x}", x))
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            PropertyValue::String(it) => write!(f, "\"{}\"", it),
            PropertyValue::Strings(it) => write!(f, "[\"{}\"]", it.join("\",\"")),
            PropertyValue::PHandle(it) => write!(f, "<{:#x}>", it),
            PropertyValue::Address(address, size) => write!(f, "<{} {}>", address, size),
            PropertyValue::Addresses(it) => write!(
                f,
                "<{}>",
                it.iter()
                    .map(|(address, size)| format!("{} {}", address, size))
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            PropertyValue::Ranges(it) => write!(
                f,
                "<{}>",
                it.iter()
                    .map(|r| format!("{} {} {}", r.range.0, r.range.1, r.range.2))
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            PropertyValue::Unknown => write!(f, ""),
        }
    }
}

/// A property of [crate::node::DeviceTreeNode]
pub struct NodeProperty<'a, A: Allocator + Clone> {
    pub(super) block_count: usize,
    name: &'a str,
    value: PropertyValue<'a, A>,
}

impl<'a, A: Allocator + Clone> NodeProperty<'a, A> {
    /// Creates a new NodeProperty instance from raw bytes
    pub(super) fn from_bytes(
        data: &'a [u8],
        header: &DeviceTreeHeader,
        start: usize,
        inherited: &InheritedValues<A>,
        owned: &InheritedValues<A>,
        allocator: A,
    ) -> Result<Self> {
        let prop_block_start = align_block(start);
        if let Ok(prop_val_size) = read_aligned_be_u32(data, prop_block_start + 1) {
            if let Ok(name_offset) = read_aligned_be_u32(data, prop_block_start + 2) {
                if let Some(name) = read_name(data, (header.off_dt_strings + name_offset) as usize)
                {
                    let value_index = prop_block_start + 3;
                    if prop_val_size > 0 {
                        let raw_value = &data
                            .get(
                                locate_block(value_index)
                                    ..(locate_block(value_index) + prop_val_size as usize),
                            )
                            .ok_or(ParsingFailed)?;
                        match NodeProperty::parse_value(
                            raw_value, name, inherited, owned, allocator,
                        ) {
                            Ok(value) => Ok(Self {
                                block_count: 3 + align_size(prop_val_size as usize),
                                name,
                                value,
                            }),
                            Err(err) => Err(err),
                        }
                    } else {
                        Ok(Self {
                            block_count: 3,
                            name,
                            value: PropertyValue::None,
                        })
                    }
                } else {
                    Err(NotEnoughLength)
                }
            } else {
                Err(NotEnoughLength)
            }
        } else {
            Err(NotEnoughLength)
        }
    }

    /// Parses a raw value into a PropertyValue
    pub(super) fn parse_value(
        raw_value: &'a [u8],
        name: &str,
        inherited: &InheritedValues<A>,
        owned: &InheritedValues<A>,
        allocator: A,
    ) -> Result<PropertyValue<'a, A>> {
        match name {
            "compatible" | "model" | "status" => {
                if let Some(strs) =
                    read_aligned_sized_strings(raw_value, 0, raw_value.len(), allocator)
                {
                    match strs.len() {
                        x if x > 1 => Ok(PropertyValue::Strings(strs)),
                        1 => Ok(PropertyValue::String(strs[0])),
                        _ => Ok(PropertyValue::String("")),
                    }
                } else {
                    Err(ParsingFailed)
                }
            }
            "phandle" | "virtual-reg" => {
                if let Ok(int) = read_aligned_be_u32(raw_value, 0) {
                    Ok(PropertyValue::Integer(int as u64))
                } else {
                    Err(ParsingFailed)
                }
            }
            "reg" => {
                let address_cells = match inherited.find("#address-cells") {
                    Some(v) => v as usize,
                    _ => 2,
                };
                let size_cells = match inherited.find("#size-cells") {
                    Some(v) => v as usize,
                    _ => 2,
                };

                let group_size = align_size(raw_value.len()) / (address_cells + size_cells);
                if group_size > 1 {
                    let mut regs = Vec::<_, A>::new_in(allocator);
                    for i in 0..group_size {
                        let group_index = i * (address_cells + size_cells);
                        let res = (
                            read_aligned_be_number(raw_value, group_index, address_cells)?,
                            read_aligned_be_number(
                                raw_value,
                                group_index + address_cells,
                                size_cells,
                            )?,
                        );
                        regs.push(res);
                    }
                    Ok(PropertyValue::Addresses(regs))
                } else {
                    Ok(PropertyValue::Address(
                        read_aligned_be_number(raw_value, 0, address_cells)?,
                        read_aligned_be_number(raw_value, address_cells, size_cells)?,
                    ))
                }
            }
            "ranges" | "dma-ranges" => {
                let child_cells = match owned.find("#address-cells") {
                    Some(v) => v as usize,
                    _ => 2,
                };
                let parent_cells = match inherited.find("#address-cells") {
                    Some(v) => v as usize,
                    _ => 2,
                };
                let size_cells = match owned.find("#size-cells") {
                    Some(v) => v as usize,
                    _ => 2,
                };
                let single_size = child_cells + parent_cells + size_cells;
                let group_size = align_size(raw_value.len()) / single_size;
                let mut rags = Vec::<_, A>::new_in(allocator);
                for i in 0..group_size {
                    let group_index = i * single_size;
                    let range = (
                        read_aligned_be_number(raw_value, group_index, child_cells)?,
                        read_aligned_be_number(raw_value, group_index + child_cells, parent_cells)?,
                        read_aligned_be_number(
                            raw_value,
                            group_index + child_cells + parent_cells,
                            size_cells,
                        )?,
                    );
                    rags.push(Range { range });
                }
                Ok(PropertyValue::Ranges(rags))
            }
            x if x.ends_with("-parent") => {
                if let Ok(int) = read_aligned_be_u32(raw_value, 0) {
                    Ok(PropertyValue::PHandle(int))
                } else {
                    Err(ParsingFailed)
                }
            }
            x if x.starts_with('#') && x.ends_with("cells") => {
                if let Ok(int) = read_aligned_be_u32(raw_value, 0) {
                    Ok(PropertyValue::Integer(int as u64))
                } else {
                    Err(ParsingFailed)
                }
            }
            _ => {
                let a = raw_value.len() % BLOCK_SIZE == 0;
                let b = *safe_index(raw_value, 0)? != b'\0'
                    && *safe_index(raw_value, raw_value.len() - 1)? == b'\0'
                    && raw_value.is_ascii();

                if !a || b {
                    if let Some(strs) =
                        read_aligned_sized_strings(raw_value, 0, raw_value.len(), allocator)
                    {
                        match strs.len() {
                            x if x > 1 => Ok(PropertyValue::Strings(strs)),
                            1 => Ok(PropertyValue::String(strs[0])),
                            _ => Ok(PropertyValue::String("")),
                        }
                    } else {
                        Err(ParsingFailed)
                    }
                } else {
                    let size = raw_value.len() / BLOCK_SIZE;
                    if size > 1 {
                        let mut res = Vec::<u64, A>::new_in(allocator);
                        for i in 0..size {
                            if let Ok(num) = read_aligned_be_u32(raw_value, i) {
                                res.push(num as u64);
                            } else {
                                return Err(ParsingFailed);
                            }
                        }
                        Ok(PropertyValue::Integers(res))
                    } else {
                        Ok(PropertyValue::Integer(
                            read_aligned_be_u32(raw_value, 0)? as u64
                        ))
                    }
                }
            }
        }
    }

    /// Returns the name of the NodeProperty
    pub fn name(&self) -> &'a str {
        self.name
    }

    /// Returns the PropertyValue of the NodeProperty
    pub fn value(&self) -> &PropertyValue<'a, A> {
        &self.value
    }
}

/// Implements the Display trait for NodeProperty to allow it to be printed
impl<'a, A: Allocator + Clone> Display for NodeProperty<'a, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match &self.value {
            PropertyValue::Unknown | PropertyValue::None => write!(f, "{};", self.name),
            other => write!(f, "{} = {};", self.name, other),
        }
    }
}
