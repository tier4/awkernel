use core::{
    marker::PhantomData,
    ops::{Deref, Range},
    slice::{ChunksExact, ChunksExactMut},
};

/// Errors that can occur when working with point fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PointFieldError {
    InvalidLength,
    FieldNotFound(&'static str),
    DatatypeMismatch {
        name: &'static str,
        expected: FieldDatatype,
        actual: FieldDatatype,
    },
    FieldOutOfBounds {
        name: &'static str,
        offset_start: usize,
        offset_end: usize,
        point_step: usize,
    },
    ValueOutOfBounds {
        name: &'static str,
        index: usize,
        count: usize,
    },
    Overflow,
}

impl core::fmt::Display for PointFieldError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidLength => write!(f, "Invalid length for point field"),
            Self::FieldNotFound(name) => write!(f, "Field {name} not found"),
            Self::DatatypeMismatch {
                name,
                expected,
                actual,
            } => write!(
                f,
                "Field {name} has datatype {actual:?}, expected {expected:?}"
            ),
            Self::FieldOutOfBounds {
                name,
                offset_start,
                offset_end,
                point_step,
            } => write!(
                f,
                "Field {name} at offset range {offset_start}-{offset_end} exceeds the point step {point_step}"
            ),
            Self::ValueOutOfBounds { name, index, count } => write!(
                f,
                "Value {index} of field {name} is outside its {count} values"
            ),
            Self::Overflow => write!(f, "Point field offset overflows usize"),
        }
    }
}

impl core::error::Error for PointFieldError {}

pub type Result<T> = core::result::Result<T, PointFieldError>;

/// Represents the datatype of a point field in a point cloud.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldDatatype {
    Int8 = 1,
    Uint8 = 2,
    Int16 = 3,
    Uint16 = 4,
    Int32 = 5,
    Uint32 = 6,
    Float32 = 7,
    Float64 = 8,
}

impl FieldDatatype {
    pub const fn size(self) -> usize {
        match self {
            Self::Int8 | Self::Uint8 => 1,
            Self::Int16 | Self::Uint16 => 2,
            Self::Int32 | Self::Uint32 | Self::Float32 => 4,
            Self::Float64 => 8,
        }
    }
}

/// Reads and writes scalar values stored in a [`PointField`].
pub trait PointFieldValue: Copy + sealed::Sealed {
    /// The matching `sensor_msgs::msg::PointField` datatype.
    const DATATYPE: FieldDatatype;
    /// Size of the value in bytes.
    const SIZE: usize;
    /// Encoded native-endian bytes.
    type Bytes: AsRef<[u8]>;

    /// Decodes a native-endian value; returns an error if `bytes.len() != SIZE`.
    fn try_from_slice(bytes: &[u8]) -> Result<Self>;

    /// Decodes a little-endian value; returns an error if `bytes.len() != SIZE`.
    fn try_from_le_slice(bytes: &[u8]) -> Result<Self>;

    /// Decodes a big-endian value; returns an error if `bytes.len() != SIZE`.
    fn try_from_be_slice(bytes: &[u8]) -> Result<Self>;

    /// Encodes the value as native-endian bytes.
    fn to_bytes(self) -> Self::Bytes;

    /// Encodes the value as little-endian bytes.
    fn to_le_bytes(self) -> Self::Bytes;

    /// Encodes the value as big-endian bytes.
    fn to_be_bytes(self) -> Self::Bytes;
}

macro_rules! impl_point_field_value {
    ($($ty:ty => $datatype:ident),* $(,)?) => {$(
        impl sealed::Sealed for $ty {}

        impl PointFieldValue for $ty {
            const DATATYPE: FieldDatatype = FieldDatatype::$datatype;
            const SIZE: usize = core::mem::size_of::<$ty>();
            type Bytes = [u8; core::mem::size_of::<$ty>()];

            #[inline]
            fn try_from_slice(bytes: &[u8]) -> Result<Self> {
                bytes.try_into().map(<$ty>::from_ne_bytes).map_err(|_| PointFieldError::InvalidLength)
            }

            #[inline]
            fn try_from_le_slice(bytes: &[u8]) -> Result<Self> {
                bytes.try_into().map(<$ty>::from_le_bytes).map_err(|_| PointFieldError::InvalidLength)
            }

            #[inline]
            fn try_from_be_slice(bytes: &[u8]) -> Result<Self> {
                bytes.try_into().map(<$ty>::from_be_bytes).map_err(|_| PointFieldError::InvalidLength)
            }

            #[inline]
            fn to_bytes(self) -> Self::Bytes {
                <$ty>::to_ne_bytes(self)
            }

            #[inline]
            fn to_le_bytes(self) -> Self::Bytes {
                <$ty>::to_le_bytes(self)
            }

            #[inline]
            fn to_be_bytes(self) -> Self::Bytes {
                <$ty>::to_be_bytes(self)
            }
        }
    )*};
}

impl_point_field_value! {
    i8 => Int8,
    u8 => Uint8,
    i16 => Int16,
    u16 => Uint16,
    i32 => Int32,
    u32 => Uint32,
    f32 => Float32,
    f64 => Float64,
}

/// Describes a single field (channel) in a point cloud.
///
/// In contrast with ROS's `sensor_msgs::msg::PointField`, this struct uses private fields and provides accessor methods.
/// Also, accessors for numeric values translate from `u32` to `usize`, as this is more idiomatic in Rust for indexing and sizing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PointField {
    /// Common `PointField` names are x, y, z, intensity, rgb, rgba.
    name: &'static str,
    /// Offset from the start of the point struct.
    offset: u32,
    /// Datatype of the field.
    datatype: FieldDatatype,
    /// How many elements in the field.
    count: u32,
}

impl PointField {
    /// Creates a new `PointField` with the given name, offset, datatype, and count.
    pub const fn try_new(
        name: &'static str,
        offset: u32,
        datatype: FieldDatatype,
        count: u32,
    ) -> Result<Self> {
        let size = match (count as usize).checked_mul(datatype.size()) {
            Some(size) => size,
            None => return Err(PointFieldError::Overflow),
        };
        match (offset as usize).checked_add(size) {
            None => Err(PointFieldError::Overflow),
            Some(_) => Ok(Self {
                name,
                offset,
                datatype,
                count,
            }),
        }
    }

    /// Returns the name of the field.
    #[inline]
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// Returns the offset of the field within the point struct.
    #[inline]
    pub const fn offset(&self) -> usize {
        self.offset as _
    }

    /// Returns the datatype of the field.
    #[inline]
    pub const fn datatype(&self) -> FieldDatatype {
        self.datatype
    }

    /// Returns the number of elements in the field.
    #[inline]
    pub const fn count(&self) -> usize {
        self.count as _
    }

    /// Returns the size of a single element in the field in bytes.
    #[inline]
    pub const fn val_size(&self) -> usize {
        self.datatype.size()
    }

    /// Returns the starting byte offset of a value within the point.
    #[inline]
    pub const fn val_start(&self, index: usize) -> Result<usize> {
        if index >= self.count() {
            return Err(PointFieldError::ValueOutOfBounds {
                name: self.name,
                index,
                count: self.count(),
            });
        }
        Ok(self.offset() + index * self.val_size())
    }

    /// Returns the exclusive ending byte offset of a value within the point.
    #[inline]
    pub const fn val_end(&self, index: usize) -> Result<usize> {
        match self.val_range(index) {
            Ok(range) => Ok(range.end),
            Err(error) => Err(error),
        }
    }

    /// Returns the byte range of a single element in the field within the point struct.
    ///
    /// Returns an error if `index` is outside the field.
    #[inline]
    pub const fn val_range(&self, index: usize) -> Result<Range<usize>> {
        match self.val_start(index) {
            Ok(start) => {
                let end = start + self.val_size();
                Ok(start..end)
            }
            Err(error) => Err(error),
        }
    }

    /// Returns the total size of the field in bytes.
    #[inline]
    pub const fn size(&self) -> usize {
        self.count() * self.val_size()
    }

    /// Returns the starting byte offset of the field within the point.
    #[inline]
    pub const fn start(&self) -> usize {
        self.offset()
    }

    /// Returns the exclusive ending byte offset of the field within the point.
    #[inline]
    pub const fn end(&self) -> usize {
        self.start() + self.size()
    }

    /// Returns the byte range of the field within the point struct.
    #[inline]
    pub const fn range(&self) -> Range<usize> {
        self.start()..self.end()
    }

    /// Iterates over the byte slices of the field's values within a point.
    ///
    /// Returns an error if the complete field does not fit.
    pub fn iter<'a>(&self, point: &'a [u8]) -> Result<ChunksExact<'a, u8>> {
        let values = point
            .get(self.range())
            .ok_or(PointFieldError::InvalidLength)?;
        Ok(values.chunks_exact(self.val_size()))
    }

    /// Iterates over mutable byte slices of the field's values within a point.
    ///
    /// Returns an error if the complete field does not fit.
    pub fn iter_mut<'a>(&self, point: &'a mut [u8]) -> Result<ChunksExactMut<'a, u8>> {
        let values = point
            .get_mut(self.range())
            .ok_or(PointFieldError::InvalidLength)?;
        Ok(values.chunks_exact_mut(self.val_size()))
    }
}

/// A point-field descriptor checked against its scalar value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypedPointField<T> {
    point_field: PointField,
    value: PhantomData<T>,
}

impl<T: PointFieldValue> TypedPointField<T> {
    /// Validates that the field's datatype matches `T`.
    pub fn try_new(point_field: PointField) -> Result<Self> {
        if point_field.datatype != T::DATATYPE {
            return Err(PointFieldError::DatatypeMismatch {
                name: point_field.name,
                expected: T::DATATYPE,
                actual: point_field.datatype,
            });
        }

        Ok(Self {
            point_field,
            value: PhantomData,
        })
    }

    /// Reads one value from a complete point slice in native byte order.
    pub fn try_read(&self, point: &[u8], index: usize) -> Result<T> {
        let bytes = point
            .get(self.val_range(index)?)
            .ok_or(PointFieldError::InvalidLength)?;
        T::try_from_slice(bytes)
    }

    /// Writes one value into a complete point slice in native byte order.
    pub fn try_write(&self, point: &mut [u8], index: usize, value: T) -> Result<()> {
        let bytes = point
            .get_mut(self.val_range(index)?)
            .ok_or(PointFieldError::InvalidLength)?;
        let encoded = value.to_bytes();
        let encoded = encoded.as_ref();
        if bytes.len() != encoded.len() {
            return Err(PointFieldError::InvalidLength);
        }
        bytes.copy_from_slice(encoded);
        Ok(())
    }

    /// Validates the complete field range and iterates over its native-endian values.
    ///
    /// Returns an error if the range does not fit. Iteration stops at the first decoding error.
    pub fn iter<'a>(&self, point: &'a [u8]) -> Result<impl Iterator<Item = T> + 'a> {
        Ok(self
            .point_field
            .iter(point)?
            .map_while(|bytes| T::try_from_slice(bytes).ok())
            .fuse())
    }

    /// Validates the complete field range and iterates over its writable values.
    ///
    /// Returns an error if the range does not fit. Iteration stops at the first decoding error.
    pub fn iter_mut<'a>(
        &self,
        point: &'a mut [u8],
    ) -> Result<impl Iterator<Item = PointFieldValueMut<'a, T>> + 'a> {
        Ok(self
            .point_field
            .iter_mut(point)?
            .map_while(|bytes| {
                T::try_from_slice(bytes)
                    .ok()
                    .map(|_| PointFieldValueMut::new(bytes))
            })
            .fuse())
    }
}

impl<T> Deref for TypedPointField<T> {
    type Target = PointField;

    fn deref(&self) -> &Self::Target {
        &self.point_field
    }
}

impl<T> From<TypedPointField<T>> for PointField {
    fn from(typed: TypedPointField<T>) -> Self {
        typed.point_field
    }
}

impl<T: PointFieldValue> TryFrom<PointField> for TypedPointField<T> {
    type Error = PointFieldError;

    fn try_from(field: PointField) -> Result<Self> {
        Self::try_new(field)
    }
}

/// A writable value in a point field, backed by possibly unaligned bytes.
#[derive(Debug)]
pub struct PointFieldValueMut<'a, T> {
    bytes: &'a mut [u8],
    value: PhantomData<T>,
}

impl<'a, T: PointFieldValue> PointFieldValueMut<'a, T> {
    pub(super) fn new(bytes: &'a mut [u8]) -> Self {
        Self {
            bytes,
            value: PhantomData,
        }
    }

    /// Reads the value in native byte order.
    pub fn read(&self) -> Result<T> {
        T::try_from_slice(self.bytes)
    }

    /// Writes the value in native byte order.
    pub fn write(&mut self, value: T) {
        for (target, source) in self.bytes.iter_mut().zip(value.to_bytes().as_ref()) {
            *target = *source;
        }
    }
}

mod sealed {
    pub trait Sealed {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn point_field_value_encodes_and_decodes_values() {
        let encoded = <f32 as PointFieldValue>::to_bytes(3.5);
        assert_eq!(
            <f32 as PointFieldValue>::try_from_slice(encoded.as_ref()).unwrap(),
            3.5
        );
        assert_eq!(<f32 as PointFieldValue>::DATATYPE, FieldDatatype::Float32);
        assert_eq!(<f32 as PointFieldValue>::SIZE, 4);
    }

    #[test]
    fn typed_field_validates_datatype() {
        const FIELD: Result<PointField> =
            PointField::try_new("values", 1, FieldDatatype::Uint16, 2);
        let typed = TypedPointField::<u16>::try_new(FIELD.unwrap()).unwrap();
        assert_eq!(typed.name(), "values");
        assert_eq!(
            TypedPointField::<i16>::try_new(FIELD.unwrap()).err(),
            Some(PointFieldError::DatatypeMismatch {
                name: "values",
                expected: FieldDatatype::Int16,
                actual: FieldDatatype::Uint16,
            })
        );
    }

    #[test]
    fn typed_field_reads_and_writes_unaligned_point_values() {
        let field = TypedPointField::<u16>::try_new(
            PointField::try_new("values", 1, FieldDatatype::Uint16, 2).unwrap(),
        )
        .unwrap();
        let mut point = [0xaa, 0x11, 0x22, 0x33, 0x44, 0xbb];
        assert_eq!(
            field.try_read(&point, 0),
            Ok(u16::from_ne_bytes([0x11, 0x22]))
        );
        assert_eq!(
            field.try_read(&point, 1),
            Ok(u16::from_ne_bytes([0x33, 0x44]))
        );

        field.try_write(&mut point, 1, 0x1234).unwrap();
        let encoded = 0x1234u16.to_ne_bytes();
        assert_eq!(point, [0xaa, 0x11, 0x22, encoded[0], encoded[1], 0xbb]);
        assert_eq!(field.try_read(&point, 1), Ok(0x1234));
    }

    #[test]
    fn typed_field_rejects_invalid_access_without_mutating_bytes() {
        let field = TypedPointField::<u16>::try_new(
            PointField::try_new("values", 1, FieldDatatype::Uint16, 2).unwrap(),
        )
        .unwrap();
        let mut point = [0xaa, 0x11, 0x22, 0x33];
        let original = point;
        assert_eq!(
            field.try_read(&point, 1),
            Err(PointFieldError::InvalidLength)
        );
        assert_eq!(
            field.try_write(&mut point, 1, 42),
            Err(PointFieldError::InvalidLength)
        );
        assert_eq!(point, original);

        let out_of_bounds = PointFieldError::ValueOutOfBounds {
            name: "values",
            index: 2,
            count: 2,
        };
        assert_eq!(field.try_read(&point, 2), Err(out_of_bounds));
        assert_eq!(field.try_write(&mut point, 2, 42), Err(out_of_bounds));
        assert_eq!(point, original);

        let empty = TypedPointField::<u16>::try_new(
            PointField::try_new("empty", 1, FieldDatatype::Uint16, 0).unwrap(),
        )
        .unwrap();
        assert_eq!(
            empty.try_read(&point, 0),
            Err(PointFieldError::ValueOutOfBounds {
                name: "empty",
                index: 0,
                count: 0,
            })
        );
    }

    #[test]
    fn point_field_iterators_borrow_value_chunks() {
        let field = PointField::try_new("values", 1, FieldDatatype::Uint16, 2).unwrap();
        let mut point = [0xaa, 0x11, 0x22, 0x33, 0x44, 0xbb];
        assert_eq!(
            field.iter(&point).unwrap().collect::<alloc::vec::Vec<_>>(),
            [&[0x11, 0x22][..], &[0x33, 0x44][..]]
        );

        let mut values = field.iter_mut(&mut point).unwrap();
        let first = values.next().unwrap();
        let second = values.next().unwrap();
        assert!(values.next().is_none());
        first.copy_from_slice(&[0x55, 0x66]);
        second.copy_from_slice(&[0x77, 0x88]);
        drop(values);
        assert_eq!(point, [0xaa, 0x55, 0x66, 0x77, 0x88, 0xbb]);

        let original = point;
        assert!(matches!(
            field.iter(&point[..4]),
            Err(PointFieldError::InvalidLength)
        ));
        assert!(matches!(
            field.iter_mut(&mut point[..4]),
            Err(PointFieldError::InvalidLength)
        ));
        assert_eq!(point, original);

        let empty = PointField::try_new("empty", 6, FieldDatatype::Uint16, 0).unwrap();
        assert_eq!(empty.iter(&point).unwrap().count(), 0);
        assert_eq!(empty.iter_mut(&mut point).unwrap().count(), 0);
    }

    #[test]
    fn typed_field_iterators_read_and_write_unaligned_values() {
        let field = TypedPointField::<u16>::try_new(
            PointField::try_new("values", 1, FieldDatatype::Uint16, 2).unwrap(),
        )
        .unwrap();
        let mut point = [0xaa, 0x11, 0x22, 0x33, 0x44, 0xbb, 0xcc];
        assert_eq!(
            field.iter(&point).unwrap().collect::<alloc::vec::Vec<_>>(),
            [
                u16::from_ne_bytes([0x11, 0x22]),
                u16::from_ne_bytes([0x33, 0x44])
            ]
        );
        assert_eq!(field.iter(&point[..5]).unwrap().count(), 2);

        let mut values = field.iter_mut(&mut point).unwrap();
        let mut first = values.next().unwrap();
        let mut second = values.next().unwrap();
        assert!(values.next().is_none());
        assert_eq!(first.read(), Ok(u16::from_ne_bytes([0x11, 0x22])));
        first.write(0x1234);
        second.write(0x5678);
        drop(values);
        let a = 0x1234u16.to_ne_bytes();
        let b = 0x5678u16.to_ne_bytes();
        assert_eq!(point, [0xaa, a[0], a[1], b[0], b[1], 0xbb, 0xcc]);
    }

    #[test]
    fn typed_field_iterators_reject_incomplete_fields_without_mutation() {
        let field = TypedPointField::<u16>::try_new(
            PointField::try_new("values", 1, FieldDatatype::Uint16, 3).unwrap(),
        )
        .unwrap();
        let original = [0xaa, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66];
        for len in [0, 1, 3, 5, 6] {
            let mut point = original;
            assert!(matches!(
                field.iter(&point[..len]),
                Err(PointFieldError::InvalidLength)
            ));
            assert!(matches!(
                field.iter_mut(&mut point[..len]),
                Err(PointFieldError::InvalidLength)
            ));
            assert_eq!(point, original);
        }
    }

    #[test]
    fn typed_field_iterators_handle_empty_and_missing_data() {
        let empty = TypedPointField::<u16>::try_new(
            PointField::try_new("empty", 2, FieldDatatype::Uint16, 0).unwrap(),
        )
        .unwrap();
        let missing = TypedPointField::<u16>::try_new(
            PointField::try_new("missing", 3, FieldDatatype::Uint16, 1).unwrap(),
        )
        .unwrap();
        let mut point = [0xaa, 0xbb];
        assert_eq!(empty.iter(&point).unwrap().next(), None);
        assert!(empty.iter_mut(&mut point).unwrap().next().is_none());
        assert!(matches!(
            missing.iter(&point),
            Err(PointFieldError::InvalidLength)
        ));
        assert!(matches!(
            missing.iter_mut(&mut point),
            Err(PointFieldError::InvalidLength)
        ));
        assert_eq!(point, [0xaa, 0xbb]);
    }

    #[test]
    fn point_field_constructor_is_const_and_preserves_value_ranges() {
        const FIELD: Result<PointField> =
            PointField::try_new("vector", 1, FieldDatatype::Uint16, 3);
        let field = FIELD.unwrap();
        assert_eq!(field.range(), 1..7);
        assert_eq!((field.start(), field.end()), (1, 7));
        assert_eq!(field.val_range(0), Ok(1..3));
        assert_eq!(field.val_range(2), Ok(5..7));
        assert_eq!(field.val_start(0), Ok(1));
        assert_eq!(field.val_end(0), Ok(3));
        assert_eq!(field.val_start(2), Ok(5));
        assert_eq!(field.val_end(2), Ok(7));
        for index in [3, usize::MAX] {
            let error = PointFieldError::ValueOutOfBounds {
                name: "vector",
                index,
                count: 3,
            };
            assert_eq!(field.val_start(index), Err(error));
            assert_eq!(field.val_end(index), Err(error));
        }
        assert_eq!(
            field.val_range(3),
            Err(PointFieldError::ValueOutOfBounds {
                name: "vector",
                index: 3,
                count: 3,
            })
        );
        assert_eq!(
            field.val_range(usize::MAX),
            Err(PointFieldError::ValueOutOfBounds {
                name: "vector",
                index: usize::MAX,
                count: 3,
            })
        );
        let empty = PointField::try_new("empty", 7, FieldDatatype::Uint16, 0).unwrap();
        assert_eq!(empty.range(), 7..7);
        assert_eq!((empty.start(), empty.end()), (7, 7));
        let error = PointFieldError::ValueOutOfBounds {
            name: "empty",
            index: 0,
            count: 0,
        };
        assert_eq!(empty.val_start(0), Err(error));
        assert_eq!(empty.val_end(0), Err(error));
        assert_eq!(
            empty.val_range(0),
            Err(PointFieldError::ValueOutOfBounds {
                name: "empty",
                index: 0,
                count: 0,
            })
        );
    }

    #[test]
    fn point_relative_ranges_allow_mutating_disjoint_fields() {
        let first = PointField::try_new("first", 1, FieldDatatype::Uint8, 3).unwrap();
        let second = PointField::try_new("second", 4, FieldDatatype::Uint8, 2).unwrap();
        let mut point = [0; 7];
        let [first_data, second_data] = point
            .get_disjoint_mut([first.range(), second.range()])
            .unwrap();
        first_data[1] = 1;
        second_data.fill(2);
        assert_eq!(point, [0, 0, 1, 0, 2, 2, 0]);

        let overlapping = PointField::try_new("overlap", 3, FieldDatatype::Uint8, 2).unwrap();
        assert!(point
            .get_disjoint_mut([first.range(), overlapping.range()])
            .is_err());
    }

    #[cfg(target_pointer_width = "32")]
    #[test]
    fn point_field_constructor_rejects_range_overflow() {
        assert_eq!(
            PointField::try_new("overflow", u32::MAX, FieldDatatype::Uint8, 1),
            Err(PointFieldError::Overflow)
        );
        assert_eq!(
            PointField::try_new("overflow", 0, FieldDatatype::Float64, u32::MAX),
            Err(PointFieldError::Overflow)
        );
    }
}
