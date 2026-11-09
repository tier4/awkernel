use super::{
    field::{CheckedField, FieldAccessor},
    selection::FieldSelection,
    PointCloudError, PointFieldError,
};

/// Read-only access to one point, retaining every field and value.
pub type PointReader<'a> = PointAccessor<'a, &'a [u8]>;

/// Writable access to one point, retaining every field and value.
pub type PointWriter<'a> = PointAccessor<'a, &'a mut [u8]>;

/// A borrowed point accessor with eagerly validated field byte ranges.
///
/// Construction borrows the reader's metadata without allocating. Duplicate names resolve
/// to the first field. Overlapping fields are allowed; writes can affect both fields.
pub struct PointAccessor<'a, D> {
    pub(super) bytes: D,
    pub(super) fields: &'a [CheckedField],
}

impl<'a, D: AsRef<[u8]>> PointAccessor<'a, D> {
    /// Helper function to find a checked field info by name.
    fn field_info(&self, name: &'static str) -> Result<&'a CheckedField, PointCloudError> {
        self.fields
            .iter()
            .find(|field| field.name() == name)
            .ok_or(PointFieldError::FieldNotFound(name).into())
    }

    /// Returns the packed bytes of this point, excluding any row padding.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.bytes.as_ref()
    }

    /// Borrows a field's complete raw bytes without copying.
    pub fn field<'b>(
        &'b self,
        name: &'static str,
    ) -> Result<FieldAccessor<'b, &'b [u8]>, PointCloudError> {
        let resolved = self.field_info(name)?;
        let bytes = self
            .bytes()
            .get(resolved.range())
            .ok_or(PointCloudError::InvalidData)?;
        Ok(FieldAccessor {
            field: resolved,
            bytes,
        })
    }
}

impl<'a, D: AsRef<[u8]> + AsMut<[u8]>> PointAccessor<'a, D> {
    /// Returns writable bytes for this point, excluding any row padding.
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        self.bytes.as_mut()
    }

    /// Exclusively borrows a resolved field's complete writable raw bytes.
    pub fn field_mut<'b>(
        &'b mut self,
        name: &'static str,
    ) -> Result<FieldAccessor<'b, &'b mut [u8]>, PointCloudError> {
        let resolved = self.field_info(name)?;
        let range = resolved.range();
        let bytes = self
            .bytes
            .as_mut()
            .get_mut(range)
            .ok_or(PointCloudError::InvalidData)?;
        Ok(FieldAccessor {
            field: resolved,
            bytes,
        })
    }
}

/// One borrowed point with a typed read tuple and complete raw point access.
pub struct TypedPointReader<'a, S: FieldSelection> {
    pub(super) raw: PointReader<'a>,
    pub(super) fields: S::Fields<'a>,
}

impl<'a, S: FieldSelection> TypedPointReader<'a, S> {
    /// Returns typed handles in selection order, retaining every field value.
    #[inline]
    pub fn fields(&self) -> S::Fields<'a> {
        self.fields
    }

    /// Returns the raw bytes of this point, excluding any row padding.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.raw.bytes()
    }

    /// Borrows a field's complete raw bytes without copying.
    #[inline]
    pub fn field(&self, name: &'static str) -> Result<FieldAccessor<'_, &[u8]>, PointCloudError> {
        self.raw.field(name)
    }
}

/// One mutably borrowed point with typed reads and validated tuple writes.
pub struct TypedPointWriter<'a, S: FieldSelection> {
    pub(super) raw: PointWriter<'a>,
    pub(super) checked: &'a S::Checked,
}

impl<S: FieldSelection> TypedPointWriter<'_, S> {
    /// Returns typed read handles in the original selection order.
    #[inline]
    pub fn fields(&self) -> Result<S::Fields<'_>, PointCloudError> {
        S::access(self.checked, self.raw.bytes)
    }

    #[inline]
    /// Returns the raw bytes of this point, excluding any row padding.
    pub fn bytes(&self) -> &[u8] {
        self.raw.bytes()
    }

    /// Writes the selected value at the same element index in every field.
    ///
    /// All selected indices and byte ranges are validated before the first
    /// write. Overlapping and repeated selections are applied left to right,
    /// so the last tuple element affecting a byte wins.
    #[inline]
    pub fn write_values(
        &mut self,
        element_index: usize,
        values: S::Values,
    ) -> Result<(), PointCloudError> {
        S::write_values(self.checked, self.raw.bytes, element_index, values)
    }

    /// Writes each selected field from a slice containing all values for this point.
    ///
    /// Each slice length must equal that field's `count()`. All lengths and byte
    /// ranges are validated before mutation. Complete fields are written in tuple
    /// selection order, so overlapping or repeated selections are last-wins.
    ///
    /// ```
    /// use common_types::point::{
    ///     Field, PointCloud, PointCloudError, PointCloudWriter,
    /// };
    ///
    /// fn set_first_point(cloud: &mut PointCloud) -> Result<(), PointCloudError> {
    ///     let mut writer = PointCloudWriter::try_new_typed(
    ///         cloud,
    ///         (Field::<u8>::new("bytes"), Field::<u16>::new("words")),
    ///     )?;
    ///     let byte_values: &[u8] = &[1, 2];
    ///     let word_values: &[u16] = &[0x1234];
    ///     writer.point_mut(0)?.write_fields((byte_values, word_values))?;
    ///     Ok(())
    /// }
    /// ```
    pub fn write_fields(&mut self, values: S::Slices<'_>) -> Result<(), PointCloudError> {
        S::write_fields(self.checked, &values, self.raw.bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::point::selection::typed_selection;
    use crate::point::test_support::{message, projected_cloud};
    use crate::point::*;
    use alloc::{vec, vec::Vec};

    #[test]
    fn malformed_field_ranges_fail_without_mutating_point_bytes() {
        let descriptor = PointField::new("values", 1, FieldDatatype::Uint16, 2);
        let resolved = [CheckedField::try_new(descriptor, 5).unwrap()];
        let mut bytes = [0xAA; 4];
        {
            let mut point = PointAccessor {
                bytes: &mut bytes[..],
                fields: &resolved,
            };
            assert_eq!(
                point.field("values").err(),
                Some(PointCloudError::InvalidData)
            );
            assert_eq!(
                point.field_mut("values").err(),
                Some(PointCloudError::InvalidData)
            );
            assert_eq!(
                point
                    .field_mut("values")
                    .and_then(|field| field.into_typed::<u16>())
                    .and_then(|mut field| field.write_value(0, 42)),
                Err(PointCloudError::InvalidData)
            );
        }
        assert_eq!(bytes, [0xAA; 4]);
    }
    #[test]
    fn point_handles_reuse_resolved_metadata() {
        let mut cloud = projected_cloud();
        let reader = PointCloudWriter::try_new(
            &mut cloud,
            Some(&[
                ("label", FieldDatatype::Uint8),
                ("vector", FieldDatatype::Uint16),
            ]),
        )
        .unwrap();
        let resolved = reader.fields().nth(1).unwrap();
        for index in 0..reader.point_count() {
            let point = reader.point(index).unwrap();
            assert!(core::ptr::eq(point.field_info("vector").unwrap(), resolved));
            let raw = point.field("vector").unwrap();
            assert!(core::ptr::eq(&*raw, resolved));
            assert!(core::ptr::eq(
                raw.into_typed::<u16>().unwrap().raw.field,
                resolved
            ));
        }
    }
    #[test]
    fn typed_point_write_fields_prevalidates_malformed_final_range() {
        let checked_fields = [
            CheckedField::try_new(PointField::new("first", 0, FieldDatatype::Uint8, 1), 4).unwrap(),
            CheckedField::try_new(PointField::new("last", 2, FieldDatatype::Uint16, 1), 4).unwrap(),
        ];
        let mut field_iter = checked_fields.iter();
        let checked =
            <(Field<u8>, Field<u16>) as typed_selection::Selection>::resolve(&mut field_iter)
                .unwrap();
        let mut bytes = [0xAA; 3];
        {
            let raw = PointAccessor {
                bytes: &mut bytes[..],
                fields: &checked_fields,
            };
            let mut writer: TypedPointWriter<'_, (Field<u8>, Field<u16>)> = TypedPointWriter {
                raw,
                checked: &checked,
            };
            assert_eq!(
                writer.write_fields((&[0x42], &[0x1234])),
                Err(PointCloudError::InvalidData)
            );
        }
        assert_eq!(bytes, [0xAA; 3]);
    }
    #[test]
    fn typed_point_write_fields_accepts_empty_whole_field_slices() {
        let mut cloud = message(
            1,
            1,
            4,
            4,
            vec![
                PointField::new("value", 0, FieldDatatype::Uint8, 1),
                PointField::new("empty", 4, FieldDatatype::Uint16, 0),
            ],
            vec![0xAA; 4],
        );
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (Field::<u8>::new("value"), Field::<u16>::new("empty")),
        )
        .unwrap();

        writer
            .point_mut(0)
            .unwrap()
            .write_fields((&[0x42], &[]))
            .unwrap();

        assert_eq!(writer.data(), &[0x42, 0xAA, 0xAA, 0xAA]);
    }
    #[test]
    fn typed_point_write_fields_apply_complete_overlapping_fields_in_tuple_order() {
        let mut cloud = message(
            1,
            1,
            3,
            3,
            vec![
                PointField::new("first", 0, FieldDatatype::Uint8, 2),
                PointField::new("shifted", 1, FieldDatatype::Uint8, 2),
            ],
            vec![0xAA; 3],
        );
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (Field::<u8>::new("first"), Field::<u8>::new("shifted")),
        )
        .unwrap();

        writer
            .point_mut(0)
            .unwrap()
            .write_fields((&[1, 2], &[9, 8]))
            .unwrap();

        assert_eq!(writer.data(), &[1, 9, 8]);
    }
    #[test]
    fn typed_point_write_fields_checks_lengths_and_orders_repeated_fields() {
        let mut cloud = message(
            1,
            1,
            4,
            4,
            vec![
                PointField::new("wide", 0, FieldDatatype::Uint8, 2),
                PointField::new("alias", 1, FieldDatatype::Uint8, 1),
            ],
            vec![0xAA; 4],
        );
        let original = cloud.data.clone();
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (
                Field::<u8>::new("wide"),
                Field::<u8>::new("alias"),
                Field::<u8>::new("wide"),
            ),
        )
        .unwrap();
        assert_eq!(
            writer
                .point_mut(0)
                .unwrap()
                .write_fields((&[1, 2], &[9], &[3])),
            Err(PointCloudError::InvalidData)
        );
        assert_eq!(writer.data(), original);
        writer
            .point_mut(0)
            .unwrap()
            .write_fields((&[1, 2], &[9], &[3, 4]))
            .unwrap();
        assert_eq!(writer.data(), &[3, 4, 0xAA, 0xAA]);
    }
    #[test]
    fn typed_point_writer_writes_mixed_fields_without_touching_padding_or_neighbors() {
        let mut cloud = message(
            2,
            2,
            8,
            18,
            vec![
                PointField::new("byte_values", 1, FieldDatatype::Uint8, 2),
                PointField::new("word_values", 3, FieldDatatype::Uint16, 2),
            ],
            vec![0xAA; 36],
        );
        let original = cloud.data.clone();
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (
                Field::<u8>::new("byte_values"),
                Field::<u16>::new("word_values"),
            ),
        )
        .unwrap();
        writer
            .point_at_mut(1, 1)
            .unwrap()
            .write_values(1, (0x42, 0x1234))
            .unwrap();
        let mut expected = original.clone();
        expected[28] = 0x42;
        expected[31..33].copy_from_slice(&0x1234_u16.to_ne_bytes());
        assert_eq!(writer.data(), expected);

        assert_eq!(
            writer
                .point_mut(3)
                .unwrap()
                .write_fields((&[0x41, 0x42], &[0x1233])),
            Err(PointCloudError::InvalidData)
        );
        assert_eq!(writer.data(), expected);
        writer
            .point_mut(3)
            .unwrap()
            .write_fields((&[0x41, 0x42], &[0x1233, 0x1234]))
            .unwrap();

        {
            let point = writer.point_mut(3).unwrap();
            let (byte_values, word_values) = point.fields().unwrap();
            assert_eq!(
                byte_values.values().collect::<Result<Vec<_>, _>>(),
                Ok(vec![0x41, 0x42])
            );
            assert_eq!(
                word_values.values().collect::<Result<Vec<_>, _>>(),
                Ok(vec![0x1233, 0x1234])
            );
        }

        let mut expected = original;
        expected[27] = 0x41;
        expected[28] = 0x42;
        expected[29..31].copy_from_slice(&0x1233_u16.to_ne_bytes());
        expected[31..33].copy_from_slice(&0x1234_u16.to_ne_bytes());
        assert_eq!(writer.data(), expected);
        assert_eq!(writer.data().get(16..18), Some(&[0xAA; 2][..]));
        assert_eq!(writer.data().get(34..36), Some(&[0xAA; 2][..]));
    }
    #[test]
    fn typed_writer_validates_every_value_before_mutating_and_orders_overlaps() {
        let mut cloud = message(
            1,
            1,
            4,
            4,
            vec![
                PointField::new("first", 0, FieldDatatype::Uint8, 2),
                PointField::new("last", 2, FieldDatatype::Uint16, 1),
            ],
            vec![1, 2, 3, 4],
        );
        let original = cloud.data.clone();
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (Field::<u8>::new("first"), Field::<u16>::new("last")),
        )
        .unwrap();
        assert!(matches!(
            writer.point_mut(0).unwrap().write_values(1, (9, 0x1234)),
            Err(PointCloudError::InvalidField(
                PointFieldError::ValueOutOfBounds {
                    name: "last",
                    index: 1,
                    count: 1,
                }
            ))
        ));
        assert_eq!(writer.data(), original);

        let mut empty = message(
            1,
            1,
            3,
            3,
            vec![
                PointField::new("first", 0, FieldDatatype::Uint8, 1),
                PointField::new("empty", 1, FieldDatatype::Uint16, 0),
            ],
            vec![4, 5, 6],
        );
        let original = empty.data.clone();
        let mut writer = PointCloudWriter::try_new_typed(
            &mut empty,
            (Field::<u8>::new("first"), Field::<u16>::new("empty")),
        )
        .unwrap();
        assert!(matches!(
            writer.point_mut(0).unwrap().write_values(0, (9, 10)),
            Err(PointCloudError::InvalidField(
                PointFieldError::ValueOutOfBounds {
                    name: "empty",
                    index: 0,
                    count: 0,
                }
            ))
        ));
        assert_eq!(writer.data(), original);

        let mut overlap = message(
            1,
            1,
            2,
            2,
            vec![
                PointField::new("wide", 0, FieldDatatype::Uint16, 1),
                PointField::new("byte", 1, FieldDatatype::Uint8, 1),
            ],
            vec![0, 0],
        );
        let mut writer = PointCloudWriter::try_new_typed(
            &mut overlap,
            (
                Field::<u16>::new("wide"),
                Field::<u8>::new("byte"),
                Field::<u16>::new("wide"),
            ),
        )
        .unwrap();
        writer
            .point_mut(0)
            .unwrap()
            .write_values(0, (0x1111, 0x22, 0x3344))
            .unwrap();
        assert_eq!(writer.data(), &0x3344_u16.to_ne_bytes());
    }
}
