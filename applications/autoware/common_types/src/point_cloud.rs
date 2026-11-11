mod cloud;
mod field;
mod point;
mod selection;
#[cfg(test)]
mod test_support;

pub use cloud::{
    PointCloudAccessor, PointCloudReader, PointCloudWriter, TypedPointCloudAccessor,
    TypedPointCloudReader, TypedPointCloudWriter,
};
pub use field::{
    CheckedField, FieldAccessor, PointFieldValueMut, TypedCheckedField, TypedFieldAccessor,
};
pub use point::{PointAccessor, PointReader, PointWriter, TypedPointReader, TypedPointWriter};
pub use selection::{Field, FieldSelection};

use crate::Header;
use alloc::vec::Vec;

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
    fn from_ne_slice(bytes: &[u8]) -> Result<Self, PointFieldError>;

    /// Encodes the value as native-endian bytes.
    fn to_ne_bytes(self) -> Self::Bytes;
}

macro_rules! impl_point_field_value {
    ($($ty:ty => $datatype:ident),* $(,)?) => {$(
        impl sealed::Sealed for $ty {}

        impl PointFieldValue for $ty {
            const DATATYPE: FieldDatatype = FieldDatatype::$datatype;
            const SIZE: usize = core::mem::size_of::<$ty>();
            type Bytes = [u8; core::mem::size_of::<$ty>()];

            fn from_ne_slice(bytes: &[u8]) -> Result<Self, PointFieldError> {
                bytes.try_into().map(<$ty>::from_ne_bytes).map_err(|_| PointFieldError::InvalidLength)
            }

            fn to_ne_bytes(self) -> Self::Bytes {
                <$ty>::to_ne_bytes(self)
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
/// # Note
///
/// The `PointField` struct may contain an invalid layout, such as overlapping fields or incorrect offsets.
/// Use [`CheckedField`] for validated metadata without a statically
/// selected Rust value type, or [`TypedCheckedField`] for typed metadata proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PointField {
    /// Common `PointField` names are x, y, z, intensity, rgb, rgba.
    pub name: &'static str,
    /// Offset from the start of the point struct.
    pub offset: u32,
    /// Datatype of the field.
    pub datatype: FieldDatatype,
    /// How many elements in the field.
    pub count: u32,
}

impl PointField {
    /// Creates a new `PointField` with the given name, offset, datatype, and count.
    pub const fn new(name: &'static str, offset: u32, datatype: FieldDatatype, count: u32) -> Self {
        Self {
            name,
            offset,
            datatype,
            count,
        }
    }
}

/// This message holds a collection of N-dimensional points, which may contain additional
/// information such as normals, intensity, etc. The point data is stored as a binary blob,
/// its layout described by the contents of the "fields" array.
///
/// # Note
///
/// This is a plain message: all fields are public and may contain an invalid layout
/// or either byte order. Validated access requires native-endian data.
/// Borrow it through [`PointCloudReader`] or [`PointCloudWriter`] before access.
pub struct PointCloud {
    /// Time of sensor data acquisition, and the coordinate frame ID (for 3D points).
    pub header: Header,
    /// Height of the point cloud. If the cloud is unordered, height is 1.
    pub height: u32,
    /// Width of the point cloud. If the cloud is unordered, width is the length of the point cloud.
    pub width: u32,
    /// Describes the channels and their layout in the binary data blob.
    pub fields: Vec<PointField>,
    /// Is the data big-endian?
    ///
    /// Readers and writers require this to equal `cfg!(target_endian = "big")`,
    /// even for empty clouds or selections; they do not swap bytes.
    pub is_bigendian: bool,
    /// Length of a point in bytes.
    pub point_step: u32,
    /// Length of a row in bytes.
    pub row_step: u32,
    /// Actual point data, size is `row_step * height` bytes.
    pub data: Vec<u8>,
    /// True if there are no invalid points.
    pub is_dense: bool,
}

mod sealed {
    pub trait Sealed {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn point_field_value_encodes_and_decodes_values() {
        let encoded = <f32 as PointFieldValue>::to_ne_bytes(3.5);
        assert_eq!(
            <f32 as PointFieldValue>::from_ne_slice(encoded.as_ref()).unwrap(),
            3.5
        );
        assert_eq!(<f32 as PointFieldValue>::DATATYPE, FieldDatatype::Float32);
        assert_eq!(<f32 as PointFieldValue>::SIZE, 4);
    }
}

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

/// Errors that can occur when constructing point clouds or accessing their points.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PointCloudError {
    UnsupportedEndianness,
    ZeroPointStep,
    InvalidRowStep { step: usize, min: usize },
    InvalidField(PointFieldError),
    InvalidDataSize { size: usize, expected: usize },
    RowOutOfBounds { index: usize, height: usize },
    PointOutOfBounds { index: usize, count: usize },
    ColumnOutOfBounds { index: usize, width: usize },
    InvalidData,
    Overflow,
}

impl core::fmt::Display for PointCloudError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedEndianness => write!(f, "Point cloud endianness is not native"),
            Self::ZeroPointStep => write!(f, "Point step is zero"),
            Self::InvalidRowStep { step, min } => write!(
                f,
                "Row step {step} is smaller than the minimum row size {min}"
            ),
            Self::InvalidField(error) => write!(f, "Invalid point field: {error}"),
            Self::InvalidDataSize { size, expected } => write!(
                f,
                "Data size {size} does not match expected size {expected}",
            ),
            Self::Overflow => write!(f, "Point cloud size overflows usize"),
            Self::RowOutOfBounds { index, height } => {
                write!(f, "Row {index} is outside cloud height {height}")
            }
            Self::PointOutOfBounds { index, count } => {
                write!(f, "Point {index} is outside cloud of {count} points")
            }
            Self::ColumnOutOfBounds { index, width } => {
                write!(f, "Column {index} is outside cloud width {width}")
            }
            Self::InvalidData => write!(f, "Point cloud data does not match its layout"),
        }
    }
}

impl core::error::Error for PointCloudError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::InvalidField(error) => Some(error),
            _ => None,
        }
    }
}

impl From<PointFieldError> for PointCloudError {
    fn from(error: PointFieldError) -> Self {
        Self::InvalidField(error)
    }
}
