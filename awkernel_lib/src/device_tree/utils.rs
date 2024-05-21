use super::error::{DeviceTreeError, Result};
use core::{alloc::Allocator, fmt::Display};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

pub(super) const BLOCK_SIZE: usize = 4;

/// Aligns the block index
pub(super) fn align_block(index: usize) -> usize {
    index / BLOCK_SIZE
}

/// Identifies the position of a block
pub(super) fn locate_block(index: usize) -> usize {
    index * BLOCK_SIZE
}

/// Aligns the size
pub(super) fn align_size(raw_size: usize) -> usize {
    (raw_size + BLOCK_SIZE - 1) / BLOCK_SIZE
}

pub(super) fn safe_index<T>(data: &[T], index: usize) -> Result<&T> {
    data.get(index).ok_or(DeviceTreeError::ParsingFailed)
}

/// Reads an aligned block
pub(super) fn read_aligned_block(data: &[u8], index: usize) -> Result<[u8; BLOCK_SIZE]> {
    let first = locate_block(index);
    if first + BLOCK_SIZE > data.len() {
        Err(DeviceTreeError::ParsingFailed)
    } else {
        Ok([
            *safe_index(data, first)?,
            *safe_index(data, first + 1)?,
            *safe_index(data, first + 2)?,
            *safe_index(data, first + 3)?,
        ])
    }
}

/// Reads an aligned big-endian u32
pub(super) fn read_aligned_be_u32(data: &[u8], index: usize) -> Result<u32> {
    read_aligned_block(data, index).map(u32::from_be_bytes)
}

#[derive(Debug, Clone, Copy)]
pub enum Addr {
    Zero,
    U32(u64),
    U64(u64),
    U96(u128),
    U128(u128),
}

impl Addr {
    pub fn to_u128(&self) -> u128 {
        match self {
            Addr::Zero => 0,
            Addr::U32(n) => *n as u128,
            Addr::U64(n) => *n as u128,
            Addr::U96(n) => *n,
            Addr::U128(n) => *n,
        }
    }
}

impl Display for Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Addr::Zero => write!(f, "0"),
            Addr::U32(n) => write!(f, "0x{n:08x}"),
            Addr::U64(n) => write!(f, "0x{n:016x}"),
            Addr::U96(n) => write!(f, "0x{n:024x}"),
            Addr::U128(n) => write!(f, "0x{n:032x}"),
        }
    }
}

/// Reads an aligned big-endian number
pub(super) fn read_aligned_be_number(data: &[u8], index: usize, block_size: usize) -> Result<Addr> {
    match block_size {
        0 => Ok(Addr::Zero),
        1 => {
            let num = read_aligned_be_u32(data, index)?;
            Ok(Addr::U32(num as u64))
        }
        2 => {
            if locate_block(index + block_size) > data.len() {
                let num = read_aligned_be_u32(data, index)?;
                Ok(Addr::U32(num as u64))
            } else {
                let bytes = &data
                    .get(locate_block(index)..locate_block(index + block_size))
                    .ok_or(DeviceTreeError::ParsingFailed)?;
                let num = u64::from_be_bytes([
                    *safe_index(bytes, 0)?,
                    *safe_index(bytes, 1)?,
                    *safe_index(bytes, 2)?,
                    *safe_index(bytes, 3)?,
                    *safe_index(bytes, 4)?,
                    *safe_index(bytes, 5)?,
                    *safe_index(bytes, 6)?,
                    *safe_index(bytes, 7)?,
                ]);
                Ok(Addr::U64(num))
            }
        }
        3 => {
            let bytes = &data
                .get(locate_block(index)..locate_block(index + block_size))
                .ok_or(DeviceTreeError::ParsingFailed)?;
            let num = u128::from_be_bytes([
                0,
                0,
                0,
                0,
                *safe_index(bytes, 0)?,
                *safe_index(bytes, 1)?,
                *safe_index(bytes, 2)?,
                *safe_index(bytes, 3)?,
                *safe_index(bytes, 4)?,
                *safe_index(bytes, 5)?,
                *safe_index(bytes, 6)?,
                *safe_index(bytes, 7)?,
                *safe_index(bytes, 8)?,
                *safe_index(bytes, 9)?,
                *safe_index(bytes, 10)?,
                *safe_index(bytes, 11)?,
            ]);
            Ok(Addr::U96(num))
        }
        4 => {
            let bytes = &data
                .get(locate_block(index)..locate_block(index + block_size))
                .ok_or(DeviceTreeError::ParsingFailed)?;
            let num = u128::from_be_bytes([
                *safe_index(bytes, 0)?,
                *safe_index(bytes, 1)?,
                *safe_index(bytes, 2)?,
                *safe_index(bytes, 3)?,
                *safe_index(bytes, 4)?,
                *safe_index(bytes, 5)?,
                *safe_index(bytes, 6)?,
                *safe_index(bytes, 7)?,
                *safe_index(bytes, 8)?,
                *safe_index(bytes, 9)?,
                *safe_index(bytes, 10)?,
                *safe_index(bytes, 11)?,
                *safe_index(bytes, 12)?,
                *safe_index(bytes, 13)?,
                *safe_index(bytes, 14)?,
                *safe_index(bytes, 15)?,
            ]);
            Ok(Addr::U128(num))
        }
        _ => Err(DeviceTreeError::NotEnoughLength),
    }
}

/// Reads a name
pub(super) fn read_name(data: &[u8], offset: usize) -> Option<&str> {
    let first = offset;
    if first > data.len() {
        None
    } else {
        let mut end = first;
        while *data.get(end)? != b'\0' {
            end += 1;
        }
        match core::str::from_utf8(data.get(first..end)?) {
            Ok(s) => Some(s),
            _ => None,
        }
    }
}

/// Reads an aligned name
pub(super) fn read_aligned_name(data: &[u8], index: usize) -> Option<&str> {
    read_name(data, locate_block(index))
}

/// Reads an aligned string with size
pub(super) fn read_aligned_sized_strings<A: Allocator>(
    data: &[u8],
    index: usize,
    size: usize,
    allocator: A,
) -> Option<Vec<&str, A>> {
    let first = locate_block(index);
    if first + size > data.len() {
        None
    } else {
        let mut current = first;
        let mut last = current;
        let mut res = Vec::<&str, A>::new_in(allocator);
        while current < first + size {
            if *data.get(current)? == b'\0' {
                let value = core::str::from_utf8(data.get(last..current)?).ok()?;
                res.push(value);
                last = current + 1;
            }
            current += 1;
        }
        Some(res)
    }
}
