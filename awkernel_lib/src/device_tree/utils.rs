use alloc::vec::Vec;

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

/// Reads an aligned block
pub(crate) fn read_aligned_block(data: &[u8], index: usize) -> Option<[u8; BLOCK_SIZE]> {
    let first = locate_block(index);
    if first + BLOCK_SIZE > data.len() {
        None
    } else {
        Some([
            data[first],
            data[first + 1],
            data[first + 2],
            data[first + 3],
        ])
    }
}

/// Reads an aligned big-endian u32
pub(crate) fn read_aligned_be_u32(data: &[u8], index: usize) -> Option<u32> {
    read_aligned_block(data, index).map(|block| u32::from_be_bytes(block))
}

/// Reads an aligned big-endian number
pub(crate) fn read_aligned_be_number(data: &[u8], index: usize, block_size: usize) -> Option<u64> {
    match block_size {
        0 => Some(0),
        1 => read_aligned_be_u32(data, index).map(|res| res as u64),
        2 => {
            let bytes = &data[locate_block(index)..locate_block(index + block_size)];
            let num = u64::from_be_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
            ]);
            Some(num)
        }
        _ => None,
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
pub(crate) fn read_aligned_sized_strings(
    data: &[u8],
    index: usize,
    size: usize,
) -> Option<Vec<&str>> {
    let first = locate_block(index);
    if first + size > data.len() {
        None
    } else {
        let mut current = first;
        let mut last = current;
        let mut res = Vec::<&str>::new();
        while current < first + size {
            if data[current] == b'\0' {
                let value = core::str::from_utf8(&data[last..current]).unwrap();
                res.push(value);
                last = current + 1;
            }
            current += 1;
        }
        Some(res)
    }
}
