use alloc::vec::Vec;
use core::{
    borrow::{Borrow, BorrowMut},
    ops::{Deref, DerefMut},
};

use super::{
    accessor::{PointAccessor, PointReader, PointWriter, TypedPointReader, TypedPointWriter},
    field::CheckedField,
    selection::FieldSelection,
    FieldDatatype, PointCloud, PointCloudError, PointFieldError,
};

/// Validated read-only borrowing of a public message.
pub type PointCloudReader<'a> = PointCloudAccessor<&'a PointCloud>;

/// Validated exclusive borrowing; only point bytes, never metadata, are writable.
pub type PointCloudWriter<'a> = PointCloudAccessor<&'a mut PointCloud>;

/// Owns resolved metadata for the selected fields.
///
/// The message remains borrowed for the lifetime of this object. The reader
/// does not expose mutable message metadata, so cached validation cannot be
/// invalidated. Overlapping fields are permitted, with exclusive reborrows
/// for writes. Only native-endian messages are accepted; typed conversions use
/// native endianness, not typed refs, and never swap bytes.
///
/// Pass `None` to resolve every field or `Some(&[(name, datatype), ...])` to
/// resolve only those fields and validate their types, in the requested order.
/// Points are accessed individually with
/// [`Self::point`] or [`Self::point_at`]:
///
/// ```
/// use common_types::point::{FieldDatatype, PointCloud, PointCloudError, PointCloudWriter};
///
/// fn update_first_normal(cloud: &mut PointCloud) -> Result<(), PointCloudError> {
///     let mut writer = PointCloudWriter::try_new(
///         cloud, Some(&[("normal", FieldDatatype::Float32)])
///     )?;
///     let mut point = writer.point_mut(0)?; // get first point of the cloud
///     let mut field = point.field_mut("normal")?; // get the "normal" field
///     let mut field = field.into_typed::<f32>()?; // convert to typed field
///     field.write_value(0, 1.0_f32)?; // write the value 1.0 to the first element of the field
///     Ok(())
/// }
/// ```
pub struct PointCloudAccessor<C> {
    cloud: C,
    point_step: usize,
    row_step: usize,
    width: usize,
    height: usize,
    point_count: usize,
    fields: Vec<CheckedField>,
}

impl<C: Borrow<PointCloud>> PointCloudAccessor<C> {
    /// Borrows a cloud after validating its row layout, data size, and selected fields.
    ///
    /// Requires `is_bigendian == cfg!(target_endian = "big")`. Unsupported byte
    /// order returns [`PointCloudError::UnsupportedEndianness`] before layout or
    /// field validation, including for empty clouds and empty selections.
    ///
    /// # Field Selection
    ///
    /// - `None` validates and resolves every field.
    /// - `Some(fields)` validates only the first descriptor matching each requested
    ///   name, including its expected datatype, in request order.
    /// - `Some(&[])` resolves no fields while retaining access to complete point bytes.
    /// - Missing names and datatype mismatches are errors; later descriptors with
    ///   the same name are not considered, even if their datatype matches.
    pub fn try_new(
        cloud: C,
        selections: Option<&[(&'static str, FieldDatatype)]>,
    ) -> Result<Self, PointCloudError> {
        let message = cloud.borrow();

        if message.is_bigendian != cfg!(target_endian = "big") {
            return Err(PointCloudError::UnsupportedEndianness);
        }

        let width = message.width as usize;
        let height = message.height as usize;
        let point_step = message.point_step as usize;
        let row_step = message.row_step as usize;

        // Check for valid point step
        if point_step == 0 {
            return Err(PointCloudError::ZeroPointStep);
        }

        // Compute useful derived values (checking for overflow)
        let point_count = width.checked_mul(height).ok_or(PointCloudError::Overflow)?;
        let min_row_step = width
            .checked_mul(point_step)
            .ok_or(PointCloudError::Overflow)?;
        let expected_size = row_step
            .checked_mul(height)
            .ok_or(PointCloudError::Overflow)?;

        // Check for valid row step (row padding allowed)
        if min_row_step > row_step {
            return Err(PointCloudError::InvalidRowStep {
                step: row_step,
                min: min_row_step,
            });
        }
        // Check for valid data size (must match exactly the expected size)
        if message.data.len() != expected_size {
            return Err(PointCloudError::InvalidDataSize {
                size: message.data.len(),
                expected: expected_size,
            });
        }

        let mut fields = Vec::new();
        match selections {
            Some(selections) => {
                for &(name, expected) in selections {
                    let field = message
                        .fields
                        .iter()
                        .find(|field| field.name == name)
                        .copied()
                        .ok_or(PointFieldError::FieldNotFound(name))?;
                    if field.datatype != expected {
                        return Err(PointFieldError::DatatypeMismatch {
                            name,
                            expected,
                            actual: field.datatype,
                        }
                        .into());
                    }
                    fields.push(CheckedField::try_new(field, message.point_step)?);
                }
            }
            None => {
                for &field in &message.fields {
                    fields.push(CheckedField::try_new(field, message.point_step)?);
                }
            }
        }
        Ok(Self {
            cloud,
            point_step,
            row_step,
            width,
            height,
            point_count,
            fields,
        })
    }

    /// Selects a typed tuple, validating only the selected fields.
    pub fn try_new_typed<S: FieldSelection>(
        cloud: C,
        selection: S,
    ) -> Result<TypedPointCloudAccessor<C, S>, PointCloudError> {
        let requests = selection.requests();
        let raw = Self::try_new(cloud, Some(requests.as_ref()))?;
        let checked = S::resolve(&mut raw.fields.iter())?;
        Ok(TypedPointCloudAccessor { raw, checked })
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &CheckedField> + '_ {
        self.fields.iter()
    }

    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.cloud.borrow().data
    }

    /// Returns the number of points, excluding row padding.
    #[must_use]
    pub const fn point_count(&self) -> usize {
        self.point_count
    }

    /// Helper function to calculate the starting byte offset of a point given its row and column.
    fn point_start(&self, row: usize, col: usize) -> Result<usize, PointCloudError> {
        if row >= self.height {
            return Err(PointCloudError::RowOutOfBounds {
                index: row,
                height: self.height,
            });
        }
        if col >= self.width {
            return Err(PointCloudError::ColumnOutOfBounds {
                index: col,
                width: self.width,
            });
        }
        let row_offset = row * self.row_step;
        let column_offset = col * self.point_step;

        Ok(row_offset + column_offset)
    }

    fn point_coordinates(&self, index: usize) -> Result<(usize, usize), PointCloudError> {
        let width = self.width;
        let count = self.point_count;
        if index >= count {
            return Err(PointCloudError::PointOutOfBounds { index, count });
        }
        let row = index / width;
        let column = index % width;
        Ok((row, column))
    }

    /// Borrows one point by its row-major index, reusing cached field layouts.
    pub fn point(&self, index: usize) -> Result<PointReader<'_>, PointCloudError> {
        let (row, col) = self.point_coordinates(index)?;
        self.point_at(row, col)
    }

    /// Borrows one point by its zero-based row and column.
    pub fn point_at(&self, row: usize, col: usize) -> Result<PointReader<'_>, PointCloudError> {
        let start = self.point_start(row, col)?;
        let end = start + self.point_step;
        let bytes = self
            .cloud
            .borrow()
            .data
            .get(start..end)
            .ok_or(PointCloudError::InvalidData)?;
        Ok(PointAccessor {
            bytes,
            fields: &self.fields,
        })
    }
}

impl<C: BorrowMut<PointCloud>> PointCloudAccessor<C> {
    /// Mutably borrows one point by its row-major index.
    pub fn point_mut(&mut self, index: usize) -> Result<PointWriter<'_>, PointCloudError> {
        let (row, col) = self.point_coordinates(index)?;
        self.point_at_mut(row, col)
    }

    /// Mutably borrows one point by its zero-based row and column.
    pub fn point_at_mut(
        &mut self,
        row: usize,
        col: usize,
    ) -> Result<PointWriter<'_>, PointCloudError> {
        let start = self.point_start(row, col)?;
        let end = start
            .checked_add(self.point_step)
            .ok_or(PointCloudError::Overflow)?;
        let bytes = self
            .cloud
            .borrow_mut()
            .data
            .get_mut(start..end)
            .ok_or(PointCloudError::InvalidData)?;
        Ok(PointAccessor {
            bytes,
            fields: &self.fields,
        })
    }
}

/// A read-only typed cloud accessor.
pub type TypedPointCloudReader<'a, S> = TypedPointCloudAccessor<&'a PointCloud, S>;

/// An exclusively borrowed typed cloud accessor.
pub type TypedPointCloudWriter<'a, S> = TypedPointCloudAccessor<&'a mut PointCloud, S>;

/// A cloud accessor with cached metadata retaining each selected Rust type.
///
/// Name, datatype, and layout validation happen at construction, not per point.
/// Overlapping and repeated selections are allowed; tuple writes validate every
/// selected value before changing bytes and apply writes in selection order.
pub struct TypedPointCloudAccessor<C, S: FieldSelection> {
    raw: PointCloudAccessor<C>,
    checked: S::Checked,
}

impl<C: Borrow<PointCloud>, S: FieldSelection> TypedPointCloudAccessor<C, S> {
    pub fn point(&self, index: usize) -> Result<TypedPointReader<'_, S>, PointCloudError> {
        let (row, col) = self.raw.point_coordinates(index)?;
        self.point_at(row, col)
    }

    pub fn point_at(
        &self,
        row: usize,
        col: usize,
    ) -> Result<TypedPointReader<'_, S>, PointCloudError> {
        let raw = self.raw.point_at(row, col)?;
        let fields = S::access(&self.checked, raw.bytes)?;
        Ok(TypedPointReader { raw, fields })
    }
}

impl<C: BorrowMut<PointCloud>, S: FieldSelection> TypedPointCloudAccessor<C, S> {
    pub fn point_mut(&mut self, index: usize) -> Result<TypedPointWriter<'_, S>, PointCloudError> {
        let raw = self.raw.point_mut(index)?;
        Ok(TypedPointWriter {
            raw,
            checked: &self.checked,
        })
    }

    pub fn point_at_mut(
        &mut self,
        row: usize,
        col: usize,
    ) -> Result<TypedPointWriter<'_, S>, PointCloudError> {
        let raw = self.raw.point_at_mut(row, col)?;
        Ok(TypedPointWriter {
            raw,
            checked: &self.checked,
        })
    }
}

impl<C, S: FieldSelection> Deref for TypedPointCloudAccessor<C, S> {
    type Target = PointCloudAccessor<C>;

    fn deref(&self) -> &Self::Target {
        &self.raw
    }
}

impl<C, S: FieldSelection> DerefMut for TypedPointCloudAccessor<C, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.raw
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::point::test_support::{message, projected_cloud};
    use crate::point::*;
    use alloc::{vec, vec::Vec};
    use core::borrow::Borrow;

    fn vector_at<C: Borrow<PointCloud>>(cloud: &PointCloudAccessor<C>, index: usize) -> Vec<u16> {
        cloud
            .point(index)
            .unwrap()
            .field("vector")
            .unwrap()
            .into_typed::<u16>()
            .unwrap()
            .values()
            .collect::<Result<Vec<_>, _>>()
            .unwrap()
    }

    #[test]
    fn point_handles_reuse_cloud_metadata() {
        let mut cloud = projected_cloud();
        let mut reader = PointCloudWriter::try_new(
            &mut cloud,
            Some(&[
                ("label", FieldDatatype::Uint8),
                ("vector", FieldDatatype::Uint16),
            ]),
        )
        .unwrap();
        let metadata = reader.fields.as_ptr();
        for index in 0..reader.point_count() {
            let point = reader.point(index).unwrap();
            assert_eq!(point.fields.as_ptr(), metadata);
        }
        let point = reader.point_mut(3).unwrap();
        assert_eq!(point.fields.as_ptr(), metadata);
    }

    #[test]
    fn typed_writer_reads_and_writes_points_across_padded_rows() {
        let mut cloud = projected_cloud();
        let mut writer = PointCloudWriter::try_new_typed(
            &mut cloud,
            (Field::<u8>::new("label"), Field::<u16>::new("vector")),
        )
        .unwrap();
        assert_eq!(writer.point_count(), 4);
        assert_eq!(writer.point(3).unwrap().fields().1.value(1), Ok(112));
        assert_eq!(writer.point_at(1, 1).unwrap().fields().0.value(0), Ok(110));
        writer
            .point_at_mut(1, 1)
            .unwrap()
            .write_values(0, (42, 500))
            .unwrap();
        let (label, vector) = writer.point(3).unwrap().fields();
        assert_eq!(label.value(0), Ok(42));
        assert_eq!(
            vector.values().collect::<Result<Vec<_>, _>>().unwrap(),
            vec![500, 112, 113]
        );
        assert!(matches!(
            writer.point(4),
            Err(PointCloudError::PointOutOfBounds { index: 4, count: 4 })
        ));
        assert!(matches!(
            writer.point_at(2, 0),
            Err(PointCloudError::RowOutOfBounds {
                index: 2,
                height: 2
            })
        ));
        assert_eq!(writer.data().get(35..38), Some(&[0xCC; 3][..]));
    }

    #[test]
    fn tuple_reads_complete_unaligned_fields_in_order_across_padded_rows() {
        let mut cloud = projected_cloud();
        // Invalid unselected metadata must not prevent typed selection.
        cloud
            .fields
            .push(PointField::new("unused", 8, FieldDatatype::Float64, 1));
        let original = cloud.data.clone();
        let reader = PointCloudReader::try_new_typed(
            &cloud,
            (Field::<u8>::new("label"), Field::<u16>::new("vector")),
        )
        .unwrap();
        assert_eq!(reader.point_count(), 4);
        assert_eq!(reader.data(), original);
        assert_eq!(
            reader.fields().map(CheckedField::name).collect::<Vec<_>>(),
            vec!["label", "vector"]
        );
        for (index, base) in [0_u16, 10, 100, 110].into_iter().enumerate() {
            let point = reader.point(index).unwrap();
            let (label, vector) = point.fields();
            assert_eq!(label.value(0), Ok(u8::try_from(base).unwrap()));
            assert_eq!(vector.count(), 3);
            assert_eq!(vector.bytes(), point.field("vector").unwrap().bytes());
            assert_eq!(
                vector.values().collect::<Result<Vec<_>, _>>().unwrap(),
                vec![base + 1, base + 2, base + 3]
            );
            let (_, at_vector) = reader.point_at(index / 2, index % 2).unwrap().fields();
            assert_eq!(at_vector.value(2), Ok(base + 3));
            assert_eq!(point.bytes().len(), 8);
            assert_eq!(
                vector.value(3),
                Err(PointCloudError::InvalidField(
                    PointFieldError::ValueOutOfBounds {
                        name: "vector",
                        index: 3,
                        count: 3,
                    }
                ))
            );
        }
        assert!(matches!(
            reader.point(4),
            Err(PointCloudError::PointOutOfBounds { .. })
        ));
        assert!(matches!(
            reader.point_at(2, 0),
            Err(PointCloudError::RowOutOfBounds { .. })
        ));
        assert!(matches!(
            reader.point_at(0, 2),
            Err(PointCloudError::ColumnOutOfBounds { .. })
        ));
        assert_eq!(cloud.data, original);
    }

    #[test]
    fn construction_requires_native_endianness_for_readers_and_writers() {
        let mut empty = projected_cloud();
        empty.height = 0;
        empty.data.clear();
        for mut cloud in [
            projected_cloud(),
            empty,
            message(0, 1, 8, 0, vec![], vec![]),
        ] {
            let fields: &[(&'static str, FieldDatatype)] = if cloud.fields.is_empty() {
                &[]
            } else {
                &[("vector", FieldDatatype::Uint16)]
            };
            for selection in [None, Some(fields), Some(&[][..])] {
                assert!(PointCloudReader::try_new(&cloud, selection).is_ok());
                assert!(PointCloudWriter::try_new(&mut cloud, selection).is_ok());
                cloud.is_bigendian = !cfg!(target_endian = "big");
                let original = cloud.data.clone();
                assert_eq!(
                    PointCloudReader::try_new(&cloud, selection).err(),
                    Some(PointCloudError::UnsupportedEndianness)
                );
                assert_eq!(
                    PointCloudWriter::try_new(&mut cloud, selection).err(),
                    Some(PointCloudError::UnsupportedEndianness)
                );
                assert_eq!(cloud.data, original);
                cloud.is_bigendian = cfg!(target_endian = "big");
            }
            cloud.is_bigendian = !cfg!(target_endian = "big");
            cloud
                .fields
                .push(PointField::new("invalid", 8, FieldDatatype::Uint16, 1));
            for selection in [None, Some(&[("missing", FieldDatatype::Uint8)][..])] {
                assert_eq!(
                    PointCloudReader::try_new(&cloud, selection).err(),
                    Some(PointCloudError::UnsupportedEndianness)
                );
                assert_eq!(
                    PointCloudWriter::try_new(&mut cloud, selection).err(),
                    Some(PointCloudError::UnsupportedEndianness)
                );
            }
        }
    }
    #[test]
    fn point_indices_and_coordinates_traverse_padded_rows_equivalently() {
        let cloud = projected_cloud();
        let reader = PointCloudReader::try_new(&cloud, None).unwrap();
        assert_eq!(reader.point_count(), 4);
        for (index, expected) in [
            vec![1, 2, 3],
            vec![11, 12, 13],
            vec![101, 102, 103],
            vec![111, 112, 113],
        ]
        .into_iter()
        .enumerate()
        {
            let by_index = reader.point(index).unwrap();
            let by_coordinates = reader.point_at(index / 2, index % 2).unwrap();
            assert_eq!(by_index.bytes(), by_coordinates.bytes());
            assert_eq!(vector_at(&reader, index), expected);
            assert_eq!(
                by_index
                    .field("label")
                    .unwrap()
                    .into_typed::<u8>()
                    .unwrap()
                    .value(0),
                Ok(u8::try_from([0_u16, 10, 100, 110][index]).unwrap())
            );
        }
        assert_eq!(reader.data().get(16..19), Some(&[0xCC; 3][..]));
        assert_eq!(reader.data().get(35..38), Some(&[0xCC; 3][..]));
        assert!(matches!(
            reader.point(4),
            Err(PointCloudError::PointOutOfBounds { index: 4, count: 4 })
        ));
        assert!(matches!(
            reader.point(usize::MAX),
            Err(PointCloudError::PointOutOfBounds {
                index: usize::MAX,
                count: 4
            })
        ));
        assert!(matches!(
            reader.point_at(2, 0),
            Err(PointCloudError::RowOutOfBounds {
                index: 2,
                height: 2
            })
        ));
        assert!(matches!(
            reader.point_at(0, 2),
            Err(PointCloudError::ColumnOutOfBounds { index: 2, width: 2 })
        ));
    }
    #[cfg(target_pointer_width = "32")]
    #[test]
    fn rejects_dimension_arithmetic_overflow() {
        let cloud = message(u32::MAX, u32::MAX, u32::MAX, u32::MAX, vec![], vec![]);
        assert_eq!(
            PointCloudReader::try_new(&cloud, None).err(),
            Some(PointCloudError::Overflow)
        );
    }
    #[test]
    fn validates_cloud_shape_and_zero_sized_dimensions() {
        let mut cloud = message(1, 1, 0, 0, vec![], vec![]);
        assert_eq!(
            PointCloudReader::try_new(&cloud, None).err(),
            Some(PointCloudError::ZeroPointStep)
        );

        cloud.point_step = 4;
        cloud.width = 2;
        cloud.row_step = 7;
        assert_eq!(
            PointCloudReader::try_new(&cloud, None).err(),
            Some(PointCloudError::InvalidRowStep { step: 7, min: 8 })
        );

        cloud.row_step = 8;
        cloud.data = vec![0; 7];
        assert_eq!(
            PointCloudReader::try_new(&cloud, None).err(),
            Some(PointCloudError::InvalidDataSize {
                size: 7,
                expected: 8,
            })
        );

        let zero_width = message(0, 2, 8, 3, vec![], vec![0; 6]);
        let reader = PointCloudReader::try_new(&zero_width, None).unwrap();
        assert_eq!(reader.point_count(), 0);
        assert!(matches!(
            reader.point(0),
            Err(PointCloudError::PointOutOfBounds { count: 0, .. })
        ));
        let zero_height = message(3, 0, 8, 24, vec![], vec![]);
        assert_eq!(
            PointCloudReader::try_new(&zero_height, None)
                .unwrap()
                .point_count(),
            0
        );
    }
}
