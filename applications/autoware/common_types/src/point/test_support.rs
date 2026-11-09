//! Utility functions for testing point cloud handling.

use alloc::{vec, vec::Vec};

use crate::{
    point::{FieldDatatype, PointCloud, PointField},
    Header,
};

pub(super) fn message(
    width: u32,
    height: u32,
    point_step: u32,
    row_step: u32,
    fields: Vec<PointField>,
    data: Vec<u8>,
) -> PointCloud {
    PointCloud {
        header: Header {
            frame_id: "lidar",
            timestamp: 0,
        },
        width,
        height,
        fields,
        is_bigendian: cfg!(target_endian = "big"),
        point_step,
        row_step,
        data,
        is_dense: true,
    }
}

/// Two rows of two points: an unaligned three-value u16 vector and a u8 label,
/// with three bytes of row padding. Values are encoded in native byte order.
pub(super) fn projected_cloud() -> PointCloud {
    let fields = vec![
        PointField::new("vector", 1, FieldDatatype::Uint16, 3),
        PointField::new("label", 7, FieldDatatype::Uint8, 1),
    ];
    let mut data = Vec::new();
    for (index, base) in [0_u16, 10, 100, 110].into_iter().enumerate() {
        data.push(0xAA);
        for value in [base + 1, base + 2, base + 3] {
            data.extend_from_slice(&value.to_ne_bytes());
        }
        data.push(u8::try_from(base).unwrap());
        if index % 2 == 1 {
            data.extend_from_slice(&[0xCC; 3]);
        }
    }
    message(2, 2, 8, 19, fields, data)
}
