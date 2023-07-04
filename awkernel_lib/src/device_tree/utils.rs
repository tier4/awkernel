use super::error::{DeviceTreeError, Result};
use alloc::vec::Vec;
use core::alloc::Allocator;

pub(crate) const BLOCK_SIZE: usize = 4;

/// Aligns the block index
pub(crate) fn align_block(index: usize) -> usize {
    index / BLOCK_SIZE
}

/// Identifies the position of a block
pub(crate) fn locate_block(index: usize) -> usize {
    index * BLOCK_SIZE
}

/// Aligns the size
pub(crate) fn align_size(raw_size: usize) -> usize {
    (raw_size + BLOCK_SIZE - 1) / BLOCK_SIZE
}

pub(crate) fn safe_index<T>(data: &[T], index: usize) -> Result<&T> {
    data.get(index).ok_or(DeviceTreeError::ParsingFailed)
}

/// Reads an aligned block
pub(crate) fn read_aligned_block(data: &[u8], index: usize) -> Result<[u8; BLOCK_SIZE]> {
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
pub(crate) fn read_aligned_be_u32(data: &[u8], index: usize) -> Result<u32> {
    read_aligned_block(data, index).map(|block| u32::from_be_bytes(block))
}

/// Reads an aligned big-endian number
pub(crate) fn read_aligned_be_number(data: &[u8], index: usize, block_size: usize) -> Result<u128> {
    match block_size {
        0 => Ok(0),
        1 => read_aligned_be_u32(data, index).map(|res| res as u128),
        2 => {
            let bytes = &data[locate_block(index)..locate_block(index + block_size)];
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
            Ok(num as u128)
        }
        3 => {
            let bytes = &data[locate_block(index)..locate_block(index + block_size)];
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
                0,
                0,
                0,
                0,
            ]);
            Ok(num as u128)
        }
        4 => {
            let bytes = &data[locate_block(index)..locate_block(index + block_size)];
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
            Ok(num)
        }
        _ => Err(DeviceTreeError::NotEnoughLength),
    }
}

/// Reads a name
pub(crate) fn read_name(data: &[u8], offset: usize) -> Option<&str> {
    let first = offset;
    if first > data.len() {
        None
    } else {
        let mut end = first;
        while data[end] != '\0' as u8 {
            end = end + 1;
        }
        match core::str::from_utf8(&data[first..end]) {
            Ok(s) => Some(s),
            _ => None,
        }
    }
}

/// Reads an aligned name
pub(crate) fn read_aligned_name(data: &[u8], index: usize) -> Option<&str> {
    read_name(data, locate_block(index))
}

/// Reads an aligned string with size
pub(crate) fn read_aligned_sized_strings<A: Allocator>(
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
            if data[current] == b'\0' {
                let value = core::str::from_utf8(&data[last..current]).ok()?;
                res.push(value);
                last = current + 1;
            }
            current += 1;
        }
        Some(res)
    }
}
