use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut, Range},
};

use super::{FieldDatatype, PointCloudError, PointField, PointFieldError, PointFieldValue};

/// Validated, machine-sized metadata for a point field.
///
/// Unlike [`PointField`], this represents a field after its offset, count, and
/// byte range have been checked against the containing point layout.
/// This metadata does not retain a statically selected Rust value type;
/// [`TypedCheckedField`] additionally retains that type proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedField {
    name: &'static str,
    datatype: FieldDatatype,
    count: usize,
    item_size: usize,
    offset_start: usize,
    offset_end: usize,
}

impl CheckedField {
    /// Validates a message descriptor and caches its machine-sized access metadata.
    pub(super) fn try_new(field: PointField, point_step: u32) -> Result<Self, PointFieldError> {
        let offset_start = field.offset as usize;
        let count = field.count as usize;
        let item_size = field.datatype.size();
        let point_step = point_step as usize;
        let field_size = count
            .checked_mul(item_size)
            .ok_or(PointFieldError::Overflow)?;
        let offset_end = offset_start
            .checked_add(field_size)
            .ok_or(PointFieldError::Overflow)?;
        if offset_end > point_step {
            return Err(PointFieldError::FieldOutOfBounds {
                name: field.name,
                offset_start,
                offset_end,
                point_step,
            });
        }

        Ok(Self {
            name: field.name,
            datatype: field.datatype,
            count,
            item_size,
            offset_start,
            offset_end,
        })
    }

    /// Returns the field name.
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// Returns the field datatype.
    pub const fn datatype(&self) -> FieldDatatype {
        self.datatype
    }

    /// Returns the number of values in the field.
    pub const fn count(&self) -> usize {
        self.count
    }

    /// Returns the size in bytes of each value.
    pub const fn item_size(&self) -> usize {
        self.item_size
    }

    /// Returns the inclusive start offset in the point.
    pub const fn offset_start(&self) -> usize {
        self.offset_start
    }

    /// Returns the exclusive end offset in the point.
    pub const fn offset_end(&self) -> usize {
        self.offset_end
    }

    /// Returns the byte range of the field within the point.
    pub const fn range(&self) -> Range<usize> {
        self.offset_start..self.offset_end
    }

    pub const fn value_range(&self, value: usize) -> Result<Range<usize>, PointFieldError> {
        if value >= self.count {
            return Err(PointFieldError::ValueOutOfBounds {
                name: self.name,
                index: value,
                count: self.count,
            });
        }
        let start = value * self.item_size;
        let end = start + self.item_size;
        Ok(start..end)
    }
}

/// Validated field metadata retaining proof of a selected Rust value type.
///
/// Dereferences to [`CheckedField`] for layout metadata. The metadata and
/// type witness are private, and construction is internal and checked, so
/// callers cannot forge the proof. Public only for selection associated types.
pub struct TypedCheckedField<T> {
    field: CheckedField,
    value: PhantomData<T>,
}

impl<T> Deref for TypedCheckedField<T> {
    type Target = CheckedField;
    fn deref(&self) -> &CheckedField {
        &self.field
    }
}

impl<T: PointFieldValue> TypedCheckedField<T> {
    pub(super) fn resolve(
        fields: &mut core::slice::Iter<'_, CheckedField>,
    ) -> Result<Self, PointCloudError> {
        let field = *fields.next().ok_or(PointCloudError::InvalidData)?;
        if field.datatype() != T::DATATYPE {
            return Err(PointFieldError::DatatypeMismatch {
                name: field.name(),
                expected: T::DATATYPE,
                actual: field.datatype(),
            }
            .into());
        }
        Ok(Self {
            field,
            value: PhantomData,
        })
    }

    pub(super) fn validate_value(&self, bytes: &[u8], value: usize) -> Result<(), PointCloudError> {
        let range = self.value_range(value)?;
        let bytes = bytes
            .get(self.field.range())
            .ok_or(PointCloudError::InvalidData)?;
        let bytes = bytes.get(range).ok_or(PointCloudError::InvalidData)?;
        if bytes.len() != T::SIZE {
            return Err(PointFieldError::InvalidLength.into());
        }
        Ok(())
    }

    pub(super) fn write_value(
        &self,
        bytes: &mut [u8],
        value: usize,
        replacement: T,
    ) -> Result<(), PointCloudError> {
        let range = self.value_range(value)?;
        let bytes = bytes
            .get_mut(self.field.range())
            .ok_or(PointCloudError::InvalidData)?;
        let target = bytes.get_mut(range).ok_or(PointCloudError::InvalidData)?;
        let encoded = replacement.to_ne_bytes();
        let encoded = encoded.as_ref();
        if target.len() != encoded.len() {
            return Err(PointFieldError::InvalidLength.into());
        }
        target.copy_from_slice(encoded);
        Ok(())
    }

    pub(super) fn validate_slice(&self, bytes: &[u8], values: &[T]) -> Result<(), PointCloudError> {
        if values.len() != self.field.count() {
            return Err(PointCloudError::InvalidData);
        }
        bytes
            .get(self.field.range())
            .ok_or(PointCloudError::InvalidData)?;
        for value_index in 0..values.len() {
            self.validate_value(bytes, value_index)?;
        }
        Ok(())
    }

    pub(super) fn write_slice(
        &self,
        bytes: &mut [u8],
        values: &[T],
    ) -> Result<(), PointCloudError> {
        for (value_index, &value) in values.iter().enumerate() {
            self.write_value(bytes, value_index, value)?;
        }
        Ok(())
    }

    pub(super) fn access<'a>(
        &'a self,
        bytes: &'a [u8],
    ) -> Result<TypedFieldAccessor<'a, &'a [u8], T>, PointCloudError> {
        let bytes = bytes
            .get(self.field.range())
            .ok_or(PointCloudError::InvalidData)?;
        Ok(TypedFieldAccessor {
            raw: FieldAccessor {
                field: &self.field,
                bytes,
            },
            _value: PhantomData,
        })
    }
}

/// A field backed by borrowed bytes, possibly unaligned.
///
/// Bytes retain their stored byte order. Cloud construction requires native
/// byte order; typed access reads and writes that order without swapping.
#[derive(Clone, Copy)]
pub struct FieldAccessor<'a, D> {
    pub(super) field: &'a CheckedField,
    pub(super) bytes: D,
}

impl<'a, D: AsRef<[u8]>> FieldAccessor<'a, D> {
    /// Returns all bytes of the field, including every consecutive value.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.bytes.as_ref()
    }

    /// Returns the byte slice corresponding to a single value within the field.
    #[inline]
    pub fn value_bytes(&self, value: usize) -> Result<&[u8], PointCloudError> {
        let range = self.value_range(value)?;
        self.bytes().get(range).ok_or(PointCloudError::InvalidData)
    }

    /// Checks the datatype once and converts this raw accessor to a typed one.
    pub fn into_typed<T: PointFieldValue>(
        self,
    ) -> Result<TypedFieldAccessor<'a, D, T>, PointCloudError> {
        if self.field.datatype() != T::DATATYPE {
            return Err(PointFieldError::DatatypeMismatch {
                name: self.field.name(),
                expected: T::DATATYPE,
                actual: self.field.datatype(),
            }
            .into());
        }
        if self.field.item_size() != T::SIZE {
            return Err(PointFieldError::InvalidLength.into());
        }
        Ok(TypedFieldAccessor {
            raw: self,
            _value: PhantomData,
        })
    }
}

impl<'a, D: AsRef<[u8]> + AsMut<[u8]>> FieldAccessor<'a, D> {
    /// Returns writable field bytes. The caller controls the encoded values.
    #[inline]
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        self.bytes.as_mut()
    }

    /// Returns the mutable byte slice corresponding to a single value within the field.
    #[inline]
    pub fn value_bytes_mut(&mut self, value: usize) -> Result<&mut [u8], PointCloudError> {
        let range = self.value_range(value)?;
        self.bytes_mut()
            .get_mut(range)
            .ok_or(PointCloudError::InvalidData)
    }
}

impl<'a, D: AsRef<[u8]>> Deref for FieldAccessor<'a, D> {
    type Target = CheckedField;

    fn deref(&self) -> &Self::Target {
        self.field
    }
}

/// Typed conversion over a resolved field; no further name or datatype lookups.
#[derive(Clone, Copy)]
pub struct TypedFieldAccessor<'a, D, T> {
    pub(super) raw: FieldAccessor<'a, D>,
    pub(super) _value: PhantomData<T>,
}

impl<'a, D: AsRef<[u8]> + 'a, T: PointFieldValue + 'a> TypedFieldAccessor<'a, D, T> {
    /// Decodes a single value in native byte order.
    pub fn value(&self, value: usize) -> Result<T, PointCloudError> {
        let bytes = self.value_bytes(value)?;
        T::from_ne_slice(bytes).map_err(PointCloudError::from)
    }

    /// Iterates over all values, decoding unaligned bytes in native order.
    pub fn values(self) -> impl ExactSizeIterator<Item = Result<T, PointCloudError>> + 'a {
        (0..self.count()).map(move |value| self.value(value))
    }
}

impl<'a, D: AsRef<[u8]> + AsMut<[u8]>, T: PointFieldValue> TypedFieldAccessor<'a, D, T> {
    /// Encodes one value in native byte order, preserving surrounding bytes.
    pub fn write_value(&mut self, value: usize, replacement: T) -> Result<(), PointCloudError> {
        let bytes = self.value_bytes_mut(value)?;
        let replacement = replacement.to_ne_bytes();
        let replacement = replacement.as_ref();
        if bytes.len() != replacement.len() {
            return Err(PointFieldError::InvalidLength.into());
        }
        bytes.copy_from_slice(replacement);
        Ok(())
    }

    pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = PointFieldValueMut<'_, T>> {
        self.raw
            .bytes_mut()
            .chunks_exact_mut(T::SIZE)
            .map(|bytes| PointFieldValueMut {
                bytes,
                _value: PhantomData,
            })
    }
}

impl<'a, D: AsRef<[u8]>, T: PointFieldValue> Deref for TypedFieldAccessor<'a, D, T> {
    type Target = FieldAccessor<'a, D>;

    fn deref(&self) -> &Self::Target {
        &self.raw
    }
}

impl<'a, D: AsRef<[u8]> + AsMut<[u8]>, T: PointFieldValue> DerefMut
    for TypedFieldAccessor<'a, D, T>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.raw
    }
}

/// A writable value in a point field, backed by possibly unaligned bytes.
#[derive(Debug)]
pub struct PointFieldValueMut<'a, T> {
    bytes: &'a mut [u8],
    _value: PhantomData<T>,
}

impl<T: PointFieldValue> PointFieldValueMut<'_, T> {
    /// Reads the value in native byte order.
    pub fn read(&self) -> Result<T, PointFieldError> {
        T::from_ne_slice(self.bytes)
    }

    /// Writes the value in native byte order.
    pub fn write(&mut self, value: T) {
        for (target, source) in self.bytes.iter_mut().zip(value.to_ne_bytes().as_ref()) {
            *target = *source;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::point_cloud::test_support::{point_cloud, projected_cloud};
    use crate::point_cloud::*;
    use alloc::{vec, vec::Vec};

    #[test]
    fn checked_fields_cache_message_metadata_and_datatype_sizes() {
        for (datatype, item_size) in [
            (FieldDatatype::Int8, 1),
            (FieldDatatype::Uint8, 1),
            (FieldDatatype::Int16, 2),
            (FieldDatatype::Uint16, 2),
            (FieldDatatype::Int32, 4),
            (FieldDatatype::Uint32, 4),
            (FieldDatatype::Float32, 4),
            (FieldDatatype::Float64, 8),
        ] {
            let offset: usize = 1;
            let count: usize = 3;
            let field = PointField {
                name: "values",
                offset: offset as u32,
                count: count as u32,
                datatype,
            };
            let resolved = CheckedField::try_new(field, 25).unwrap();
            assert_eq!(resolved.name(), field.name);
            assert_eq!(resolved.datatype(), datatype);
            assert_eq!(resolved.count(), count);
            assert_eq!(resolved.item_size(), item_size);
            assert_eq!(resolved.offset_start(), 1);
            assert_eq!(resolved.offset_end(), (offset + count * item_size));
            assert_eq!(resolved.range(), offset..(offset + count * item_size));
        }
    }

    #[test]
    fn checked_fields_check_complete_ranges_and_allow_empty_fields_at_end() {
        let mut field = PointField {
            name: "values",
            offset: 1,
            datatype: FieldDatatype::Uint16,
            count: 3,
        };
        assert_eq!(
            CheckedField::try_new(field, 6),
            Err(PointFieldError::FieldOutOfBounds {
                name: "values",
                offset_start: 1,
                offset_end: 7,
                point_step: 6,
            })
        );
        assert_eq!(CheckedField::try_new(field, 7).unwrap().offset_end(), 7);
        field.offset = 7;
        field.count = 0;
        let resolved = CheckedField::try_new(field, 7).unwrap();
        assert_eq!(resolved.offset_start(), 7);
        assert_eq!(resolved.offset_end(), 7);
        assert_eq!(resolved.range(), 7..7);
        assert_eq!(resolved.count(), 0);
        field.offset = 8;
        assert_eq!(
            CheckedField::try_new(field, 7),
            Err(PointFieldError::FieldOutOfBounds {
                name: "values",
                offset_start: 8,
                offset_end: 8,
                point_step: 7,
            })
        );
    }

    #[test]
    fn malformed_field_ranges_fail_without_mutating_typed_field_bytes() {
        let descriptor = PointField::new("values", 1, FieldDatatype::Uint16, 2);
        assert!(matches!(
            CheckedField::try_new(descriptor, 4),
            Err(PointFieldError::FieldOutOfBounds { .. })
        ));
        let resolved = CheckedField::try_new(descriptor, 5).unwrap();
        let mut bytes = [0xAA; 1];
        {
            let raw = FieldAccessor {
                field: &resolved,
                bytes: &mut bytes[..],
            };
            let mut typed = raw.into_typed::<u16>().unwrap();
            assert_eq!(typed.write_value(0, 42), Err(PointCloudError::InvalidData));
        }
        assert_eq!(bytes, [0xAA; 1]);
    }
    #[test]
    fn empty_and_overlapping_fields_support_sequential_access() {
        let mut cloud = point_cloud(
            1,
            1,
            4,
            4,
            vec![
                PointField::new("empty", 4, FieldDatatype::Uint16, 0),
                PointField::new("first", 0, FieldDatatype::Uint16, 1),
                PointField::new("alias", 0, FieldDatatype::Uint16, 1),
            ],
            vec![0xAA; 4],
        );
        let mut writer = PointCloudWriter::try_new(&mut cloud, None).unwrap();
        {
            let mut point = writer.point_mut(0).unwrap();
            let mut empty = point
                .field_mut("empty")
                .unwrap()
                .into_typed::<u16>()
                .unwrap();
            assert_eq!(empty.values_mut().len(), 0);
            assert!(matches!(
                empty.write_value(0, 1),
                Err(PointCloudError::InvalidField(
                    PointFieldError::ValueOutOfBounds {
                        name: "empty",
                        index: 0,
                        count: 0,
                    }
                ))
            ));
            point
                .field_mut("first")
                .unwrap()
                .into_typed::<u16>()
                .unwrap()
                .write_value(0, 42)
                .unwrap();
            assert_eq!(
                point
                    .field("alias")
                    .unwrap()
                    .into_typed::<u16>()
                    .unwrap()
                    .value(0),
                Ok(42)
            );
            assert!(point.field("empty").unwrap().bytes().is_empty());
        }
        let mut expected = 42_u16.to_ne_bytes().to_vec();
        expected.extend_from_slice(&[0xAA; 2]);
        assert_eq!(writer.data(), expected);
    }
    #[test]
    fn unaligned_native_values_iterate_and_mutate_without_touching_neighbors() {
        let mut cloud = projected_cloud();
        let mut writer = PointCloudWriter::try_new(&mut cloud, None).unwrap();
        let original = writer.data().to_vec();
        {
            let point = writer.point_at(1, 1).unwrap();
            let raw = point.field("vector").unwrap();
            assert_eq!(raw.bytes(), &original[28..34]);
            assert!(core::ptr::eq(
                raw.bytes().as_ptr(),
                writer.data().get(28..34).unwrap().as_ptr()
            ));
            let typed = raw.into_typed::<u16>().unwrap();
            assert_eq!(typed.value(0), Ok(111));
            assert!(matches!(
                typed.value(3),
                Err(PointCloudError::InvalidField(
                    PointFieldError::ValueOutOfBounds {
                        name: "vector",
                        index: 3,
                        count: 3
                    }
                ))
            ));
            assert_eq!(
                typed.values().collect::<Result<Vec<_>, _>>().unwrap(),
                vec![111, 112, 113]
            );
            assert!(matches!(
                point.field("vector").unwrap().into_typed::<u8>(),
                Err(PointCloudError::InvalidField(
                    PointFieldError::DatatypeMismatch { .. }
                ))
            ));
        }
        {
            let mut point = writer.point_at_mut(1, 1).unwrap();
            {
                let mut raw = point.field_mut("vector").unwrap();
                raw.bytes_mut()[0..2].copy_from_slice(&200_u16.to_ne_bytes());
                let mut typed = raw.into_typed::<u16>().unwrap();
                assert_eq!(typed.value(0), Ok(200));
                typed.write_value(1, 201).unwrap();
                for (mut value, expected) in typed.values_mut().zip([200_u16, 201, 113]) {
                    assert_eq!(value.read(), Ok(expected));
                    value.write(expected + 1);
                }
                let before_invalid_write = typed.raw.bytes().to_vec();
                assert!(matches!(
                    typed.write_value(3, 999),
                    Err(PointCloudError::InvalidField(
                        PointFieldError::ValueOutOfBounds {
                            name: "vector",
                            index: 3,
                            count: 3
                        }
                    ))
                ));
                assert_eq!(typed.raw.bytes(), before_invalid_write);
            }
        }
        let mut expected = original;
        for (offset, value) in [(28, 201_u16), (30, 202), (32, 114)] {
            expected[offset..offset + 2].copy_from_slice(&value.to_ne_bytes());
        }
        assert_eq!(writer.data(), expected);
        assert_eq!(writer.data().get(16..19), Some(&[0xCC; 3][..]));
        assert_eq!(writer.data().get(35..38), Some(&[0xCC; 3][..]));
    }
}
