pub use crate::{
    point_field::{self, PointField, PointFieldError, PointFieldValue, TypedPointField},
    Header,
};
use alloc::vec::Vec;
use core::ops::Range;

/// Errors that can occur when constructing point clouds or accessing their points.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PointCloudError {
    UnsupportedEndianness,
    InvalidRowStep {
        step: usize,
        min: usize,
    },
    FieldOutOfBounds {
        name: &'static str,
        offset_start: usize,
        offset_end: usize,
        point_step: usize,
    },
    InvalidDataSize {
        size: usize,
        min: usize,
    },
    RowOutOfBounds {
        index: usize,
        height: usize,
    },
    ColumnOutOfBounds {
        index: usize,
        width: usize,
    },
    IndexOutOfBounds {
        index: usize,
        count: usize,
    },
    InvalidData,
    Overflow,
}

impl core::fmt::Display for PointCloudError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedEndianness => write!(f, "Point cloud endianness is not native"),
            Self::InvalidRowStep { step, min } => write!(
                f,
                "Row step {step} is smaller than the minimum row size {min}"
            ),
            Self::FieldOutOfBounds { name, offset_start, offset_end, point_step } => write!(
                f,
                "Field {name} with byte range {offset_start}..{offset_end} exceeds point step {point_step}"
            ),
            Self::InvalidDataSize { size, min } => {
                write!(f, "Data size {size} is smaller than the minimum size {min}")
            }
            Self::Overflow => write!(f, "Point cloud size overflows usize"),
            Self::RowOutOfBounds { index, height } => {
                write!(f, "Row {index} is outside cloud height {height}")
            }
            Self::ColumnOutOfBounds { index, width } => {
                write!(f, "Column {index} is outside cloud width {width}")
            }
            Self::IndexOutOfBounds { index, count } => {
                write!(f, "Point index {index} is outside cloud point count {count}")
            }
            Self::InvalidData => write!(f, "Point cloud data does not match its layout"),
        }
    }
}

impl core::error::Error for PointCloudError {}

pub type Result<T> = core::result::Result<T, PointCloudError>;

/// This message holds a collection of N-dimensional points, which may contain additional
/// information such as normals, intensity, etc. The point data is stored as a binary blob,
/// its layout described by the contents of the "fields" array.
///
/// # Layout
///
/// [`Self::try_new`] validates every field and requires native byte order.
/// ROS metadata remains stored as `u32`; numeric getters return `usize`.
/// Layout metadata and buffer lengths cannot be mutated after construction.
/// Row padding and trailing bytes are allowed, but are never yielded as points.
///
/// # Using `PointCloud` as message
///
/// While you can send a `PointCloud` as a message, it is recommended to wrap it under
/// an `Arc<PointCloud>` to ensure shared ownership and avoid unnecessary copies.
#[derive(Clone)]
pub struct PointCloud {
    /// Time of sensor data acquisition, and the coordinate frame ID (for 3D points).
    header: Header,
    /// Height of the point cloud. If the cloud is unordered, height is 1.
    height: u32,
    /// Width of the point cloud. If the cloud is unordered, width is the length of the point cloud.
    width: u32,
    /// Describes the channels and their layout in the binary data blob.
    fields: Vec<PointField>,
    /// Is the data big-endian?
    ///
    /// At this point, we only support native endianness.
    is_bigendian: bool,
    /// Length of a point in bytes.
    point_step: u32,
    /// Length of a row in bytes.
    row_step: u32,
    /// At least `row_step * height` bytes, including row padding and trailing bytes.
    data: Vec<u8>,
    /// True if there are no invalid points.
    is_dense: bool,
}

impl PointCloud {
    /// Constructs a cloud from ROS-style metadata without copying its buffers.
    ///
    /// # Requirements
    ///
    /// - Requires native endianness.
    /// - `usize` arithmetic must not overflow.
    /// - `row_step >= width * point_step`.
    /// - `data.len() >= row_step * height`
    /// - All point fields must fit within `point_step`.
    ///
    /// # Notes
    ///
    /// - Overlaps, duplicate names, and zero-count fields (including at the end of a point) are permitted.
    /// - Zero strides are permitted when layout checks pass.
    /// - Indexed zero-byte points return empty slices; point iteration terminates immediately.
    #[expect(
        clippy::too_many_arguments,
        reason = "single validation boundary takes the nine ROS PointCloud2 message fields"
    )]
    pub fn try_new(
        header: Header,
        height: u32,
        width: u32,
        fields: Vec<PointField>,
        is_bigendian: bool,
        point_step: u32,
        row_step: u32,
        data: Vec<u8>,
        is_dense: bool,
    ) -> Result<Self> {
        if is_bigendian != cfg!(target_endian = "big") {
            // TODO: Implement support for non-native endianness if required.
            return Err(PointCloudError::UnsupportedEndianness);
        }
        let width_usize = width as usize;
        let height_usize = height as usize;
        let point_step_usize = point_step as usize;
        let row_step_usize = row_step as usize;
        width_usize
            .checked_mul(height_usize)
            .ok_or(PointCloudError::Overflow)?;
        let min_row_step = width_usize
            .checked_mul(point_step_usize)
            .ok_or(PointCloudError::Overflow)?;
        let min_size = row_step_usize
            .checked_mul(height_usize)
            .ok_or(PointCloudError::Overflow)?;
        if row_step_usize < min_row_step {
            return Err(PointCloudError::InvalidRowStep {
                step: row_step_usize,
                min: min_row_step,
            });
        }
        if data.len() < min_size {
            return Err(PointCloudError::InvalidDataSize {
                size: data.len(),
                min: min_size,
            });
        }
        for field in &fields {
            let offset_end = field.end();
            if offset_end > point_step_usize {
                return Err(PointCloudError::FieldOutOfBounds {
                    name: field.name(),
                    offset_start: field.offset(),
                    offset_end,
                    point_step: point_step_usize,
                });
            }
        }
        Ok(Self {
            header,
            height,
            width,
            fields,
            is_bigendian,
            point_step,
            row_step,
            data,
            is_dense,
        })
    }

    /// Returns a reference to the header of the point cloud.
    #[inline]
    pub const fn header(&self) -> &Header {
        &self.header
    }

    /// Returns a mutable reference to the header of the point cloud.
    #[inline]
    pub const fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    /// Returns the height of the point cloud.
    #[inline]
    pub const fn height(&self) -> usize {
        self.height as usize
    }

    /// Returns the width of the point cloud.
    #[inline]
    pub const fn width(&self) -> usize {
        self.width as usize
    }

    /// Returns a slice of the point cloud's fields.
    #[inline]
    pub fn fields(&self) -> &[PointField] {
        &self.fields
    }

    /// Returns whether the point cloud is stored in big-endian byte order.
    #[inline]
    pub const fn is_bigendian(&self) -> bool {
        self.is_bigendian
    }

    /// Returns the size of a single point in bytes.
    #[inline]
    pub const fn point_step(&self) -> usize {
        self.point_step as usize
    }

    /// Returns the size of a single row in bytes.
    #[inline]
    pub const fn row_step(&self) -> usize {
        self.row_step as usize
    }

    /// Returns a slice of the point cloud's raw data.
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Returns a mutable slice of the point cloud's raw data.
    #[inline]
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    /// Returns whether the point cloud is dense (i.e., contains no invalid points).
    #[inline]
    pub const fn is_dense(&self) -> bool {
        self.is_dense
    }

    /// Returns the total number of points in the point cloud.
    #[inline]
    pub const fn point_count(&self) -> usize {
        self.width() * self.height()
    }

    /// Returns the row and column of a point given its row-major index.
    #[inline]
    const fn point_coordinates(&self, index: usize) -> Result<(usize, usize)> {
        if index >= self.point_count() {
            return Err(PointCloudError::IndexOutOfBounds {
                index,
                count: self.point_count(),
            });
        }
        let width = self.width();
        let row = index / width;
        let col = index % width;
        Ok((row, col))
    }

    /// Returns the byte range of a point given its row and column.
    const fn point_range(&self, row: usize, col: usize) -> Result<Range<usize>> {
        if row >= self.height() {
            return Err(PointCloudError::RowOutOfBounds {
                index: row,
                height: self.height(),
            });
        }
        if col >= self.width() {
            return Err(PointCloudError::ColumnOutOfBounds {
                index: col,
                width: self.width(),
            });
        }
        let row_offset = row * self.row_step();
        let col_offset = col * self.point_step();
        let start = row_offset + col_offset;
        let end = start + self.point_step();
        Ok(start..end)
    }

    /// Returns the first typed field matching both `name` and `T`'s datatype.
    ///
    /// Same-name fields with another datatype are skipped. Returns
    /// [`PointFieldError::FieldNotFound`] if no matching descriptor exists.
    pub fn get_field<T: PointFieldValue>(
        &self,
        name: &'static str,
    ) -> point_field::Result<TypedPointField<T>> {
        let field = self
            .fields
            .iter()
            .find(|field| field.name() == name && field.datatype() == T::DATATYPE)
            .copied()
            .ok_or(PointFieldError::FieldNotFound(name))?;
        TypedPointField::try_new(field)
    }

    /// Borrows one complete point by zero-based row and column.
    pub fn point_at(&self, row: usize, col: usize) -> Result<&[u8]> {
        self.data
            .get(self.point_range(row, col)?)
            .ok_or(PointCloudError::InvalidData)
    }

    /// Borrows one complete point by row-major index, excluding row padding.
    pub fn point(&self, index: usize) -> Result<&[u8]> {
        let (row, col) = self.point_coordinates(index)?;
        self.point_at(row, col)
    }

    /// Exclusively borrows a point by zero-based row and column.
    pub fn point_at_mut(&mut self, row: usize, col: usize) -> Result<&mut [u8]> {
        let range = self.point_range(row, col)?;
        self.data.get_mut(range).ok_or(PointCloudError::InvalidData)
    }

    /// Exclusively borrows a point by row-major index.
    pub fn point_mut(&mut self, index: usize) -> Result<&mut [u8]> {
        let (row, col) = self.point_coordinates(index)?;
        self.point_at_mut(row, col)
    }

    /// Iterates over complete point bytes in row-major order.
    ///
    /// - Empty clouds terminate immediately, including zero-width padded rows.
    /// - Zero-byte points terminate immediately without yielding any bytes.
    /// - Skips all row padding and trailing bytes.
    pub fn iter_points(&self) -> impl Iterator<Item = &[u8]> {
        let point_step = self.point_step();
        let row_step = self.row_step();
        let width = self.width();
        let height = self.height();
        let point_count = self.point_count();
        (point_step != 0 && row_step != 0)
            .then(|| {
                self.data
                    .chunks_exact(row_step)
                    .take(height)
                    .flat_map(move |row| row.chunks_exact(point_step).take(width))
                    .take(point_count)
            })
            .into_iter()
            .flatten()
    }

    /// Iterates over disjoint mutable point bytes in row-major order.
    ///
    /// Same padding guarantees as [`Self::iter_points`].
    pub fn iter_points_mut(&mut self) -> impl Iterator<Item = &mut [u8]> {
        let point_step = self.point_step();
        let row_step = self.row_step();
        let width = self.width();
        let height = self.height();
        let point_count = self.point_count();
        (point_step != 0 && row_step != 0)
            .then(|| {
                self.data
                    .chunks_exact_mut(row_step)
                    .take(height)
                    .flat_map(move |row| row.chunks_exact_mut(point_step).take(width))
                    .take(point_count)
            })
            .into_iter()
            .flatten()
    }
}

impl core::fmt::Debug for PointCloud {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PointCloud")
            .field("header", &self.header)
            .field("height", &self.height)
            .field("width", &self.width)
            .field("fields", &self.fields)
            .field("is_bigendian", &self.is_bigendian)
            .field("point_step", &self.point_step)
            .field("row_step", &self.row_step)
            // Skipping the actual data for brevity in debug output
            .field("is_dense", &self.is_dense)
            .finish()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::point_field::FieldDatatype;
    use alloc::vec;

    fn cloud(
        width: u32,
        height: u32,
        point_step: u32,
        row_step: u32,
        fields: Vec<PointField>,
        data: Vec<u8>,
    ) -> Result<PointCloud> {
        PointCloud::try_new(
            Header {
                frame_id: "lidar",
                timestamp: 123,
            },
            height,
            width,
            fields,
            cfg!(target_endian = "big"),
            point_step,
            row_step,
            data,
            true,
        )
    }

    /// Two rows of two unaligned vectors with labels, three bytes of row padding,
    /// and more than a complete row of trailing bytes.
    fn padded_cloud() -> PointCloud {
        let fields = vec![
            PointField::try_new("vector", 1, FieldDatatype::Uint16, 3).unwrap(),
            PointField::try_new("label", 7, FieldDatatype::Uint8, 1).unwrap(),
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
        data.extend_from_slice(&[0xDD; 21]);
        cloud(2, 2, 8, 19, fields, data).unwrap()
    }

    #[test]
    fn getters_and_clone_preserve_metadata_and_validated_access() {
        let mut cloud = padded_cloud();
        let width: usize = cloud.width();
        let height: usize = cloud.height();
        let point_step: usize = cloud.point_step();
        let row_step: usize = cloud.row_step();
        assert_eq!((width, height), (2, 2));
        assert_eq!((point_step, row_step), (8, 19));
        assert_eq!(cloud.point_count(), 4);
        assert_eq!(cloud.fields().len(), 2);
        assert_eq!(cloud.fields()[0].name(), "vector");
        assert_eq!(cloud.is_bigendian(), cfg!(target_endian = "big"));
        assert!(cloud.is_dense());
        assert_eq!(cloud.header().frame_id, "lidar");
        assert_eq!(cloud.header().timestamp, 123);
        cloud.header_mut().frame_id = "map";
        cloud.header_mut().timestamp = 456;
        cloud.data_mut()[7] = 42;
        let clone = cloud.clone();
        assert_eq!(clone.header().frame_id, "map");
        assert_eq!(clone.header().timestamp, 456);
        assert_eq!(clone.point_count(), cloud.point_count());
        assert_eq!(clone.fields(), cloud.fields());
        assert_eq!(clone.data(), cloud.data());
        assert_eq!(clone.point(0).unwrap()[7], 42);
        cloud.data_mut()[7] = 9;
        assert_eq!(clone.point(0).unwrap()[7], 42);
    }

    #[test]
    fn points_and_coordinates_match_iteration_across_padded_rows() {
        let cloud = padded_cloud();
        let vector = TypedPointField::<u16>::try_new(cloud.fields()[0]).unwrap();
        let label = TypedPointField::<u8>::try_new(cloud.fields()[1]).unwrap();
        let mut points = cloud.iter_points();
        for (index, base) in [0_u16, 10, 100, 110].into_iter().enumerate() {
            let point = points.next().unwrap();
            assert_eq!(point.len(), 8);
            assert!(core::ptr::eq(point, cloud.point(index).unwrap()));
            assert!(core::ptr::eq(
                point,
                cloud.point_at(index / 2, index % 2).unwrap()
            ));
            assert_eq!(
                vector.iter(point).unwrap().collect::<Vec<_>>(),
                vec![base + 1, base + 2, base + 3]
            );
            assert_eq!(label.try_read(point, 0), Ok(u8::try_from(base).unwrap()));
            assert_eq!(
                cloud.fields()[0].iter(point).unwrap().count(),
                vector.count()
            );
        }
        assert!(points.next().is_none());
        assert!(points.next().is_none());
    }

    #[test]
    fn mutable_point_access_and_proxies_preserve_neighbors_and_padding() {
        let mut cloud = padded_cloud();
        let vector = TypedPointField::<u16>::try_new(cloud.fields()[0]).unwrap();
        let label = TypedPointField::<u8>::try_new(cloud.fields()[1]).unwrap();
        let original = cloud.data().to_vec();
        label.try_write(cloud.point_mut(0).unwrap(), 0, 42).unwrap();
        vector
            .try_write(cloud.point_at_mut(1, 1).unwrap(), 2, 500)
            .unwrap();
        for (index, point) in cloud.iter_points_mut().enumerate() {
            for mut value in vector.iter_mut(point).unwrap() {
                let current = value.read().unwrap();
                value.write(current + 1000);
            }
            assert_eq!(point[0], 0xAA);
            assert_eq!(point[7], [42, 10, 100, 110][index]);
        }
        assert_eq!(vector.try_read(cloud.point(0).unwrap(), 0), Ok(1001));
        assert_eq!(vector.try_read(cloud.point(3).unwrap(), 2), Ok(1500));
        assert_eq!(&cloud.data()[16..19], &original[16..19]);
        assert_eq!(&cloud.data()[35..], &original[35..]);
        // Yielded mutable points can coexist: they do not alias, even across rows.
        let mut iter = cloud.iter_points_mut();
        let first = iter.next().unwrap();
        let second = iter.next().unwrap();
        let third = iter.next().unwrap();
        first[0] = 1;
        second[0] = 2;
        third[0] = 3;
        assert_eq!((first[0], second[0], third[0]), (1, 2, 3));
    }

    #[test]
    fn trailing_bytes_are_allowed_but_never_yielded_as_points() {
        // The old exact-size rejection was stale: construction intentionally
        // accepts both incomplete and whole extra rows after the declared cloud.
        for extra in [0, 1, 3, 4, 5, 12] {
            let mut data = vec![1, 2, 3, 4];
            data.extend(core::iter::repeat_n(0xEE, extra));
            let mut cloud = cloud(2, 2, 1, 2, vec![], data.clone()).unwrap();
            assert_eq!(cloud.data(), data);
            assert_eq!(
                cloud.iter_points().collect::<Vec<_>>(),
                vec![&[1][..], &[2][..], &[3][..], &[4][..]]
            );
            for point in cloud.iter_points_mut() {
                point[0] = 9;
            }
            assert_eq!(&cloud.data()[4..], &data[4..]);
            assert_eq!(cloud.iter_points().count(), 4);
        }
    }

    #[test]
    fn complete_point_sized_row_padding_is_also_skipped() {
        let mut cloud = cloud(1, 2, 2, 8, vec![], (0..20).collect()).unwrap();
        assert_eq!(
            cloud.iter_points().collect::<Vec<_>>(),
            vec![&[0, 1][..], &[8, 9][..]]
        );
        for point in cloud.iter_points_mut() {
            point.fill(42);
        }
        assert_eq!(cloud.point(1).unwrap(), &[42, 42]);
        assert_eq!(&cloud.data()[2..8], &[2, 3, 4, 5, 6, 7]);
        assert_eq!(
            &cloud.data()[10..],
            &[10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
        );
    }

    #[test]
    fn empty_clouds_have_no_points_even_with_padding_and_trailing_bytes() {
        for (width, height, data_len) in [(1, 0, 7), (2, 0, 21)] {
            let field = PointField::try_new("value", 1, FieldDatatype::Uint16, 1).unwrap();
            let mut cloud = cloud(width, height, 4, 8, vec![field], vec![0xAA; data_len]).unwrap();
            let original = cloud.data().to_vec();
            assert_eq!(cloud.point_count(), 0);
            assert_eq!(cloud.iter_points().count(), 0);
            assert_eq!(cloud.iter_points_mut().count(), 0);
            assert_eq!(
                cloud.point(0),
                Err(PointCloudError::IndexOutOfBounds { index: 0, count: 0 })
            );
            assert_eq!(
                cloud.point_mut(0),
                Err(PointCloudError::IndexOutOfBounds { index: 0, count: 0 })
            );
            assert_eq!(cloud.data(), original);
        }
    }

    #[test]
    fn invalid_indices_return_typed_errors_without_mutation() {
        let mut cloud = padded_cloud();
        let original = cloud.data().to_vec();
        for index in [4, usize::MAX] {
            let expected = PointCloudError::IndexOutOfBounds {
                index,
                count: cloud.point_count(),
            };
            assert_eq!(cloud.point(index), Err(expected.clone()));
            assert_eq!(cloud.point_mut(index), Err(expected));
        }
        for index in [2, usize::MAX] {
            let row_error = PointCloudError::RowOutOfBounds { index, height: 2 };
            let col_error = PointCloudError::ColumnOutOfBounds { index, width: 2 };
            assert_eq!(cloud.point_at(index, 0), Err(row_error.clone()));
            assert_eq!(cloud.point_at_mut(index, 0), Err(row_error));
            assert_eq!(cloud.point_at(0, index), Err(col_error.clone()));
            assert_eq!(cloud.point_at_mut(0, index), Err(col_error));
        }
        assert_eq!(cloud.data(), original);
    }

    #[test]
    fn zero_byte_points_support_indexing_but_iteration_terminates_immediately() {
        for row_step in [0, 3] {
            for fields in [
                vec![],
                vec![PointField::try_new("empty", 0, FieldDatatype::Float32, 0).unwrap()],
            ] {
                let mut cloud = cloud(2, 3, 0, row_step, fields, vec![0xaa; 12]).unwrap();
                assert_eq!(cloud.point_count(), 6);
                let mut points = cloud.iter_points();
                assert!(points.next().is_none());
                assert!(points.next().is_none());
                drop(points);
                let points = cloud.iter_points_mut().collect::<Vec<_>>();
                assert!(points.is_empty());
                drop(points);
                for index in 0..6 {
                    assert_eq!(cloud.point(index).unwrap(), &[]);
                    assert!(cloud.point_mut(index).unwrap().is_empty());
                }
                assert_eq!(cloud.point_at(2, 1).unwrap(), &[]);
                assert!(cloud.point_at_mut(2, 1).unwrap().is_empty());
                assert_eq!(cloud.data(), &[0xaa; 12]);
            }
        }
        let field = PointField::try_new("x", 0, FieldDatatype::Float32, 1).unwrap();
        assert!(matches!(
            cloud(2, 3, 0, 0, vec![field], vec![]),
            Err(PointCloudError::FieldOutOfBounds { .. })
        ));
    }

    #[test]
    fn zero_width_clouds_are_empty_and_never_yield_padding_as_points() {
        for (height, point_step, row_step, data_len) in
            [(0, 0, 0, 3), (3, 0, 0, 3), (3, 4, 0, 3), (3, 4, 8, 24)]
        {
            let mut cloud = cloud(
                0,
                height,
                point_step,
                row_step,
                vec![],
                vec![0xaa; data_len],
            )
            .unwrap();
            let original = cloud.data().to_vec();
            assert_eq!(cloud.point_count(), 0);
            assert_eq!(cloud.iter_points().count(), 0);
            assert_eq!(cloud.iter_points_mut().count(), 0);
            assert_eq!(
                cloud.point(0),
                Err(PointCloudError::IndexOutOfBounds { index: 0, count: 0 })
            );
            assert_eq!(
                cloud.point_mut(usize::MAX),
                Err(PointCloudError::IndexOutOfBounds {
                    index: usize::MAX,
                    count: 0
                })
            );
            let point_at_error = if height == 0 {
                PointCloudError::RowOutOfBounds {
                    index: 0,
                    height: cloud.height(),
                }
            } else {
                PointCloudError::ColumnOutOfBounds { index: 0, width: 0 }
            };
            assert_eq!(cloud.point_at(0, 0), Err(point_at_error.clone()));
            assert_eq!(cloud.point_at_mut(0, 0), Err(point_at_error));
            assert_eq!(cloud.data(), original);
        }
    }

    #[test]
    fn zero_row_stride_supports_empty_zero_byte_clouds() {
        for (width, height, point_step) in [(1, 0, 0), (2, 0, 0)] {
            let mut cloud = cloud(width, height, point_step, 0, vec![], vec![0xaa; 3]).unwrap();
            assert_eq!(cloud.point_count(), 0);
            assert_eq!(cloud.iter_points().count(), 0);
            assert_eq!(cloud.iter_points_mut().count(), 0);
            assert_eq!(cloud.data(), &[0xaa; 3]);
        }
    }

    #[test]
    fn construction_rejects_short_rows_and_short_data() {
        for (width, height, point_step, row_step, size, error) in [
            (
                1,
                1,
                1,
                0,
                0,
                PointCloudError::InvalidRowStep { step: 0, min: 1 },
            ),
            (
                2,
                0,
                4,
                7,
                0,
                PointCloudError::InvalidRowStep { step: 7, min: 8 },
            ),
            (
                2,
                2,
                4,
                7,
                14,
                PointCloudError::InvalidRowStep { step: 7, min: 8 },
            ),
            (
                2,
                2,
                4,
                9,
                17,
                PointCloudError::InvalidDataSize { size: 17, min: 18 },
            ),
            (
                0,
                2,
                4,
                9,
                17,
                PointCloudError::InvalidDataSize { size: 17, min: 18 },
            ),
        ] {
            assert_eq!(
                cloud(width, height, point_step, row_step, vec![], vec![0; size]).err(),
                Some(error)
            );
        }
    }

    #[test]
    fn large_dimensions_do_not_wrap() {
        let result = cloud(u32::MAX, u32::MAX, 1, u32::MAX, vec![], vec![]);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(
            result.err(),
            Some(PointCloudError::InvalidDataSize {
                size: 0,
                min: usize::try_from(u32::MAX).unwrap().pow(2),
            })
        );
        #[cfg(target_pointer_width = "32")]
        assert_eq!(result.err(), Some(PointCloudError::Overflow));
        let result = cloud(u32::MAX, 0, u32::MAX, u32::MAX, vec![], vec![]);
        #[cfg(target_pointer_width = "64")]
        assert!(matches!(
            result,
            Err(PointCloudError::InvalidRowStep { .. })
        ));
        #[cfg(target_pointer_width = "32")]
        assert_eq!(result.err(), Some(PointCloudError::Overflow));
    }

    #[test]
    fn construction_checks_all_field_ranges_even_for_empty_clouds() {
        for height in [0, 1] {
            let good = PointField::try_new("value", 0, FieldDatatype::Uint8, 1).unwrap();
            for bad in [
                PointField::try_new("unused", 3, FieldDatatype::Uint16, 1).unwrap(),
                PointField::try_new("value", 4, FieldDatatype::Uint8, 1).unwrap(),
                PointField::try_new("empty", 5, FieldDatatype::Uint8, 0).unwrap(),
            ] {
                let expected = PointCloudError::FieldOutOfBounds {
                    name: bad.name(),
                    offset_start: bad.offset(),
                    offset_end: bad.range().end,
                    point_step: 4,
                };
                assert_eq!(
                    cloud(1, height, 4, 4, vec![good, bad], vec![0; 4]).err(),
                    Some(expected)
                );
            }
        }
    }

    #[test]
    fn native_endianness_is_required_even_without_points_or_fields() {
        for (width, height) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
            for fields in [
                vec![],
                vec![PointField::try_new("bad", 10, FieldDatatype::Float64, 1).unwrap()],
            ] {
                assert_eq!(
                    PointCloud::try_new(
                        Header {
                            frame_id: "",
                            timestamp: 0
                        },
                        height,
                        width,
                        fields,
                        !cfg!(target_endian = "big"),
                        4,
                        4,
                        vec![0; 4],
                        false,
                    )
                    .err(),
                    Some(PointCloudError::UnsupportedEndianness)
                );
            }
        }
    }

    #[test]
    fn overlaps_duplicate_names_and_empty_fields_use_direct_descriptors() {
        let fields = vec![
            PointField::try_new("value", 1, FieldDatatype::Uint16, 1).unwrap(),
            PointField::try_new("value", 2, FieldDatatype::Uint8, 1).unwrap(),
            PointField::try_new("empty", 4, FieldDatatype::Uint16, 0).unwrap(),
        ];
        let mut cloud = cloud(1, 1, 4, 4, fields.clone(), vec![0xAA; 4]).unwrap();
        assert_eq!(cloud.fields(), fields);
        let first = TypedPointField::<u16>::try_new(cloud.fields()[0]).unwrap();
        let overlap = TypedPointField::<u8>::try_new(cloud.fields()[1]).unwrap();
        let empty = TypedPointField::<u16>::try_new(cloud.fields()[2]).unwrap();
        let point = cloud.point_mut(0).unwrap();
        first.try_write(point, 0, 0x1234).unwrap();
        assert_eq!(overlap.try_read(point, 0), Ok(0x1234_u16.to_ne_bytes()[1]));
        overlap.try_write(point, 0, 42).unwrap();
        assert_eq!(point, &[0xAA, 0x1234_u16.to_ne_bytes()[0], 42, 0xAA]);
        assert_eq!(empty.iter(point).unwrap().count(), 0);
        assert_eq!(empty.iter_mut(point).unwrap().count(), 0);
        let original = point.to_vec();
        assert_eq!(
            empty.try_write(point, 0, 9),
            Err(PointFieldError::ValueOutOfBounds {
                name: "empty",
                index: 0,
                count: 0,
            })
        );
        assert_eq!(point, original);
    }

    #[test]
    fn all_scalar_datatypes_roundtrip_through_unaligned_cloud_points_and_proxies() {
        macro_rules! roundtrip {
            ($ty:ty, $datatype:ident, $initial:expr, $updated:expr) => {{
                let raw = PointField::try_new("value", 1, FieldDatatype::$datatype, 2).unwrap();
                let field = TypedPointField::<$ty>::try_new(raw).unwrap();
                let point_step = u32::try_from(2 + 2 * core::mem::size_of::<$ty>()).unwrap();
                let mut cloud = cloud(
                    1,
                    1,
                    point_step,
                    point_step,
                    vec![raw],
                    vec![0xAA; usize::try_from(point_step).unwrap()],
                )
                .unwrap();
                let point = cloud.point_mut(0).unwrap();
                field.try_write(point, 0, $initial).unwrap();
                field.try_write(point, 1, $initial).unwrap();
                for mut value in field.iter_mut(point).unwrap() {
                    assert_eq!(value.read().unwrap(), $initial);
                    value.write($updated);
                }
                assert_eq!(
                    field.iter(point).unwrap().collect::<Vec<_>>(),
                    vec![$updated; 2]
                );
                assert_eq!(field.try_read(point, 1), Ok($updated));
                assert_eq!(point[0], 0xAA);
                assert_eq!(point.last(), Some(&0xAA));
                let original = point.to_vec();
                assert!(field.try_write(point, 2, $initial).is_err());
                assert_eq!(point, original);
            }};
        }
        roundtrip!(i8, Int8, -12_i8, -34_i8);
        roundtrip!(u8, Uint8, 12_u8, 34_u8);
        roundtrip!(i16, Int16, -1234_i16, -2345_i16);
        roundtrip!(u16, Uint16, 1234_u16, 2345_u16);
        roundtrip!(i32, Int32, -123456_i32, -234567_i32);
        roundtrip!(u32, Uint32, 123456_u32, 234567_u32);
        roundtrip!(f32, Float32, 1.25_f32, -2.5_f32);
        roundtrip!(f64, Float64, 1.25_f64, -2.5_f64);
    }

    #[test]
    fn field_accessor_matches_name_and_type_and_keeps_first_match() {
        let mut cloud = cloud(
            1,
            1,
            8,
            8,
            vec![
                PointField::try_new("x", 0, FieldDatatype::Uint8, 1).unwrap(),
                PointField::try_new("other", 0, FieldDatatype::Float32, 1).unwrap(),
                PointField::try_new("x", 1, FieldDatatype::Float32, 1).unwrap(),
                PointField::try_new("x", 4, FieldDatatype::Float32, 1).unwrap(),
            ],
            vec![0; 8],
        )
        .unwrap();
        let x = cloud.get_field::<f32>("x").unwrap();
        assert_eq!(x.offset(), 1);
        x.try_write(cloud.point_mut(0).unwrap(), 0, 3.5).unwrap();
        assert_eq!(
            x.try_read(cloud.point(0).unwrap(), 0).unwrap().to_bits(),
            3.5f32.to_bits()
        );
        assert_eq!(cloud.get_field::<u8>("x").unwrap().offset(), 0);
        for name in ["x", "missing"] {
            assert_eq!(
                cloud.get_field::<u16>(name).err(),
                Some(PointFieldError::FieldNotFound(name))
            );
        }
    }

    #[test]
    fn typed_descriptors_validate_types_and_external_point_buffers_directly() {
        let cloud = padded_cloud();
        assert_eq!(
            TypedPointField::<u8>::try_new(cloud.fields()[0]).err(),
            Some(PointFieldError::DatatypeMismatch {
                name: "vector",
                expected: FieldDatatype::Uint8,
                actual: FieldDatatype::Uint16,
            })
        );
        let vector = TypedPointField::<u16>::try_new(cloud.fields()[0]).unwrap();
        let mut external = [0xAA; 8];
        vector.try_write(&mut external, 1, 500).unwrap();
        assert_eq!(vector.try_read(&external, 1), Ok(500));
        assert_eq!(&external[3..5], &500_u16.to_ne_bytes());
        for size in [0, 1, 6] {
            let mut short = vec![0xAA; size];
            let original = short.clone();
            assert!(matches!(
                vector.iter(&short),
                Err(PointFieldError::InvalidLength)
            ));
            assert!(matches!(
                vector.iter_mut(&mut short),
                Err(PointFieldError::InvalidLength)
            ));
            assert_eq!(
                vector.try_write(&mut short, 2, 9),
                Err(PointFieldError::InvalidLength)
            );
            assert_eq!(short, original);
        }
    }
}
