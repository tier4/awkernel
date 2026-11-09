use core::marker::PhantomData;

use super::{
    field::{CheckedField, TypedCheckedField, TypedFieldAccessor},
    FieldDatatype, PointCloudError, PointFieldValue,
};

/// A field name retaining its requested Rust scalar type.
///
/// Pass a tuple of these to [`super::PointCloudReader::try_new_typed`].
#[derive(Clone, Copy, Debug)]
pub struct Field<T: PointFieldValue> {
    name: &'static str,
    value: PhantomData<T>,
}

impl<T: PointFieldValue> Field<T> {
    #[must_use]
    pub const fn new(name: &'static str) -> Self {
        Self {
            name,
            value: PhantomData,
        }
    }
}

/// A sealed tuple selection of one through eight [`Field`] descriptors.
///
/// Supported scalar types are those implementing [`PointFieldValue`].
pub trait FieldSelection: typed_selection::Selection {}

pub(super) mod typed_selection {
    use super::*;

    pub trait Selection {
        type Requests: AsRef<[(&'static str, FieldDatatype)]>;
        type Checked;
        type Fields<'a>: Copy;
        type Values;
        type Slices<'a>
        where
            Self: 'a;

        fn requests(&self) -> Self::Requests;
        fn resolve(
            fields: &mut core::slice::Iter<'_, CheckedField>,
        ) -> Result<Self::Checked, PointCloudError>;
        fn access<'a>(
            checked: &'a Self::Checked,
            bytes: &'a [u8],
        ) -> Result<Self::Fields<'a>, PointCloudError>;
        fn write_values(
            checked: &Self::Checked,
            bytes: &mut [u8],
            value: usize,
            values: Self::Values,
        ) -> Result<(), PointCloudError>;
        fn write_fields(
            checked: &Self::Checked,
            values: &Self::Slices<'_>,
            bytes: &mut [u8],
        ) -> Result<(), PointCloudError>;
    }

    macro_rules! tuples {
        ($($ty:ident : $index:tt),+ $(,)?) => {
            impl<$($ty: PointFieldValue),+> FieldSelection for ($(Field<$ty>,)+) {}

            impl<$($ty: PointFieldValue),+> Selection for ($(Field<$ty>,)+) {
                type Requests = [(&'static str, FieldDatatype); tuples!(@count $($ty),+)];
                type Checked = ($(TypedCheckedField<$ty>,)+);
                type Fields<'a> = ($(TypedFieldAccessor<'a, &'a [u8], $ty>,)+);
                type Values = ($($ty,)+);
                type Slices<'a> = ($(&'a [$ty],)+) where Self: 'a;

                fn requests(&self) -> Self::Requests {
                    [$( (self.$index.name, $ty::DATATYPE), )+]
                }

                fn resolve(
                    fields: &mut core::slice::Iter<'_, CheckedField>,
                ) -> Result<Self::Checked, PointCloudError> {
                    Ok(($(TypedCheckedField::<$ty>::resolve(fields)?,)+))
                }

                fn access<'a>(
                    checked: &'a Self::Checked,
                    bytes: &'a [u8],
                ) -> Result<Self::Fields<'a>, PointCloudError> {
                    Ok(($(checked.$index.access(bytes)?,)+))
                }

                fn write_values(
                    checked: &Self::Checked,
                    bytes: &mut [u8],
                    value: usize,
                    values: Self::Values,
                ) -> Result<(), PointCloudError> {
                    $(checked.$index.validate_value(bytes, value)?;)+
                    $(checked.$index.write_value(bytes, value, values.$index)?;)+
                    Ok(())
                }

                fn write_fields(
                    checked: &Self::Checked,
                    values: &Self::Slices<'_>,
                    bytes: &mut [u8],
                ) -> Result<(), PointCloudError> {
                    $(checked.$index.validate_slice(bytes, values.$index)?;)+
                    $(checked.$index.write_slice(bytes, values.$index)?;)+
                    Ok(())
                }
            }
        };
        (@count $($ty:ident),+) => { <[()]>::len(&[$(tuples!(@unit $ty)),+]) };
        (@unit $ty:ident) => { () };
    }

    tuples!(A: 0);
    tuples!(A: 0, B: 1);
    tuples!(A: 0, B: 1, C: 2);
    tuples!(A: 0, B: 1, C: 2, D: 3);
    tuples!(A: 0, B: 1, C: 2, D: 3, E: 4);
    tuples!(A: 0, B: 1, C: 2, D: 3, E: 4, F: 5);
    tuples!(A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6);
    tuples!(A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::point::test_support::{message, projected_cloud};
    use crate::point::*;
    use alloc::{vec, vec::Vec};

    #[test]
    fn eight_field_tuple_decodes_every_supported_primitive() {
        let mut data = vec![0xAA];
        data.extend_from_slice(&(-3_i8).to_ne_bytes());
        data.extend_from_slice(&4_u8.to_ne_bytes());
        data.extend_from_slice(&(-300_i16).to_ne_bytes());
        data.extend_from_slice(&400_u16.to_ne_bytes());
        data.extend_from_slice(&(-50_000_i32).to_ne_bytes());
        data.extend_from_slice(&60_000_u32.to_ne_bytes());
        data.extend_from_slice(&1.25_f32.to_ne_bytes());
        data.extend_from_slice(&2.5_f64.to_ne_bytes());
        let cloud = message(
            1,
            1,
            27,
            27,
            vec![
                PointField::new("a", 1, FieldDatatype::Int8, 1),
                PointField::new("b", 2, FieldDatatype::Uint8, 1),
                PointField::new("c", 3, FieldDatatype::Int16, 1),
                PointField::new("d", 5, FieldDatatype::Uint16, 1),
                PointField::new("e", 7, FieldDatatype::Int32, 1),
                PointField::new("f", 11, FieldDatatype::Uint32, 1),
                PointField::new("g", 15, FieldDatatype::Float32, 1),
                PointField::new("h", 19, FieldDatatype::Float64, 1),
            ],
            data,
        );
        let reader = PointCloudReader::try_new_typed(
            &cloud,
            (
                Field::<i8>::new("a"),
                Field::<u8>::new("b"),
                Field::<i16>::new("c"),
                Field::<u16>::new("d"),
                Field::<i32>::new("e"),
                Field::<u32>::new("f"),
                Field::<f32>::new("g"),
                Field::<f64>::new("h"),
            ),
        )
        .unwrap();
        let (a, b, c, d, e, f, g, h) = reader.point(0).unwrap().fields();
        assert_eq!(a.value(0), Ok(-3));
        assert_eq!(b.value(0), Ok(4));
        assert_eq!(c.value(0), Ok(-300));
        assert_eq!(d.value(0), Ok(400));
        assert_eq!(e.value(0), Ok(-50_000));
        assert_eq!(f.value(0), Ok(60_000));
        assert_eq!(g.value(0), Ok(1.25));
        assert_eq!(h.value(0), Ok(2.5));
    }
    #[test]
    fn selected_duplicate_name_uses_first_descriptor() {
        let cloud = message(
            1,
            1,
            2,
            2,
            vec![
                PointField::new("duplicate", 0, FieldDatatype::Uint8, 1),
                PointField::new("duplicate", 1, FieldDatatype::Uint16, 1),
            ],
            vec![7, 9],
        );
        assert!(matches!(
            PointCloudReader::try_new(&cloud, None),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldOutOfBounds {
                    name: "duplicate",
                    ..
                }
            ))
        ));
        let selected =
            PointCloudReader::try_new(&cloud, Some(&[("duplicate", FieldDatatype::Uint8)]))
                .unwrap();
        assert_eq!(
            selected
                .point(0)
                .unwrap()
                .field("duplicate")
                .unwrap()
                .into_typed::<u8>()
                .unwrap()
                .value(0),
            Ok(7)
        );
        let mut cloud = cloud;
        cloud.fields[1].offset = 0;
        assert_eq!(
            PointCloudReader::try_new(&cloud, Some(&[("duplicate", FieldDatatype::Uint16)])).err(),
            Some(PointCloudError::InvalidField(
                PointFieldError::DatatypeMismatch {
                    name: "duplicate",
                    expected: FieldDatatype::Uint16,
                    actual: FieldDatatype::Uint8,
                }
            ))
        );
    }
    #[test]
    fn selections_validate_requested_fields_and_preserve_order_and_bytes() {
        let mut cloud = message(
            1,
            1,
            4,
            4,
            vec![
                PointField::new("x", 0, FieldDatatype::Uint8, 1),
                PointField::new("y", 1, FieldDatatype::Uint8, 1),
                PointField::new("unused", 3, FieldDatatype::Uint16, 1),
            ],
            vec![7, 9, 0xAA, 0xBB],
        );
        assert!(matches!(
            PointCloudReader::try_new(&cloud, None),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldOutOfBounds { name: "unused", .. }
            ))
        ));
        assert!(matches!(
            PointCloudWriter::try_new(&mut cloud, None),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldOutOfBounds { name: "unused", .. }
            ))
        ));
        assert!(matches!(
            PointCloudReader::try_new(&cloud, Some(&[("unused", FieldDatatype::Uint16)])),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldOutOfBounds { name: "unused", .. }
            ))
        ));

        let selected = PointCloudReader::try_new(
            &cloud,
            Some(&[
                ("y", FieldDatatype::Uint8),
                ("x", FieldDatatype::Uint8),
                ("y", FieldDatatype::Uint8),
            ]),
        )
        .unwrap();
        assert_eq!(
            selected
                .fields()
                .map(CheckedField::name)
                .collect::<Vec<_>>(),
            vec!["y", "x", "y"]
        );
        let point = selected.point(0).unwrap();
        assert_eq!(point.bytes(), &[7, 9, 0xAA, 0xBB]);
        assert_eq!(
            point
                .field("y")
                .unwrap()
                .into_typed::<u8>()
                .unwrap()
                .value(0),
            Ok(9)
        );
        assert!(matches!(
            PointCloudReader::try_new(&cloud, Some(&[("missing", FieldDatatype::Uint8)])),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldNotFound("missing")
            ))
        ));

        let empty = PointCloudReader::try_new(&cloud, Some(&[])).unwrap();
        assert_eq!(empty.fields().len(), 0);
        assert_eq!(empty.point(0).unwrap().bytes(), &[7, 9, 0xAA, 0xBB]);
        assert!(matches!(
            empty.point(0).unwrap().field("x"),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldNotFound("x")
            ))
        ));
        cloud.data.pop();
        assert_eq!(
            PointCloudReader::try_new(&cloud, Some(&[])).err(),
            Some(PointCloudError::InvalidDataSize {
                size: 3,
                expected: 4,
            })
        );

        cloud.height = 0;
        cloud.data.clear();
        assert!(matches!(
            PointCloudReader::try_new(&cloud, None),
            Err(PointCloudError::InvalidField(_))
        ));
        assert!(PointCloudReader::try_new(&cloud, Some(&[])).is_ok());
    }
    #[test]
    fn tuple_duplicates_overlap_and_zero_counts_are_read_only() {
        let mut cloud = message(
            1,
            1,
            2,
            2,
            vec![
                PointField::new("x", 0, FieldDatatype::Uint8, 1),
                PointField::new("x", 1, FieldDatatype::Uint16, 1),
                PointField::new("overlap", 0, FieldDatatype::Uint8, 1),
                PointField::new("empty", 2, FieldDatatype::Uint16, 0),
            ],
            vec![7, 9],
        );
        let reader = PointCloudReader::try_new_typed(
            &cloud,
            (
                Field::<u8>::new("x"),
                Field::<u8>::new("x"),
                Field::<u8>::new("overlap"),
                Field::<u16>::new("empty"),
            ),
        )
        .unwrap();
        let (x, repeated, overlap, empty) = reader.point(0).unwrap().fields();
        assert_eq!(
            (x.value(0), repeated.value(0), overlap.value(0)),
            (Ok(7), Ok(7), Ok(7))
        );
        assert_eq!(empty.values().len(), 0);
        assert!(matches!(
            empty.value(0),
            Err(PointCloudError::InvalidField(
                PointFieldError::ValueOutOfBounds {
                    name: "empty",
                    index: 0,
                    count: 0,
                }
            ))
        ));
        assert_eq!(
            PointCloudReader::try_new_typed(&cloud, (Field::<u16>::new("x"),)).err(),
            Some(
                PointFieldError::DatatypeMismatch {
                    name: "x",
                    expected: FieldDatatype::Uint16,
                    actual: FieldDatatype::Uint8,
                }
                .into()
            )
        );
        assert_eq!(cloud.data, vec![7, 9]);
        // Existing sequential writes remain valid even with overlapping fields.
        let mut writer = PointCloudWriter::try_new(
            &mut cloud,
            Some(&[
                ("x", FieldDatatype::Uint8),
                ("overlap", FieldDatatype::Uint8),
            ]),
        )
        .unwrap();
        let mut point = writer.point_mut(0).unwrap();
        point
            .field_mut("x")
            .unwrap()
            .into_typed::<u8>()
            .unwrap()
            .write_value(0, 8)
            .unwrap();
        point
            .field_mut("overlap")
            .unwrap()
            .into_typed::<u8>()
            .unwrap()
            .write_value(0, 10)
            .unwrap();
        assert_eq!(cloud.data, vec![10, 9]);
    }
    #[test]
    fn tuple_validates_missing_mismatched_layout_and_endian_even_without_points() {
        for height in [2, 0] {
            let mut cloud = projected_cloud();
            cloud.height = height;
            if height == 0 {
                cloud.data.clear();
            }
            let original = cloud.data.clone();
            let valid =
                PointCloudReader::try_new_typed(&cloud, (Field::<u16>::new("vector"),)).unwrap();
            assert_eq!(valid.point_count(), usize::try_from(height).unwrap() * 2);
            if height == 0 {
                assert!(matches!(
                    valid.point(0),
                    Err(PointCloudError::PointOutOfBounds { count: 0, .. })
                ));
            }
            assert_eq!(
                PointCloudReader::try_new_typed(&cloud, (Field::<f32>::new("vector"),)).err(),
                Some(
                    PointFieldError::DatatypeMismatch {
                        name: "vector",
                        expected: FieldDatatype::Float32,
                        actual: FieldDatatype::Uint16,
                    }
                    .into()
                )
            );
            assert_eq!(
                PointCloudReader::try_new_typed(&cloud, (Field::<u8>::new("missing"),)).err(),
                Some(PointFieldError::FieldNotFound("missing").into())
            );
            cloud
                .fields
                .push(PointField::new("bad", 8, FieldDatatype::Uint8, 1));
            assert!(matches!(
                PointCloudReader::try_new_typed(&cloud, (Field::<u8>::new("bad"),)),
                Err(PointCloudError::InvalidField(
                    PointFieldError::FieldOutOfBounds { .. }
                ))
            ));
            cloud.is_bigendian = !cfg!(target_endian = "big");
            assert_eq!(
                PointCloudReader::try_new_typed(&cloud, (Field::<u8>::new("missing"),)).err(),
                Some(PointCloudError::UnsupportedEndianness)
            );
            assert_eq!(cloud.data, original);
            cloud.is_bigendian = cfg!(target_endian = "big");
            cloud.data.push(0);
            assert!(matches!(
                PointCloudReader::try_new_typed(&cloud, (Field::<u16>::new("vector"),)),
                Err(PointCloudError::InvalidDataSize { .. })
            ));
        }
    }
    #[test]
    fn typed_selections_reject_mismatches_for_readers_and_writers_even_when_empty() {
        let selection = [
            ("label", FieldDatatype::Uint8),
            ("vector", FieldDatatype::Float32),
        ];
        let expected = PointCloudError::InvalidField(PointFieldError::DatatypeMismatch {
            name: "vector",
            expected: FieldDatatype::Float32,
            actual: FieldDatatype::Uint16,
        });
        for height in [2, 0] {
            let mut cloud = projected_cloud();
            cloud.height = height;
            if height == 0 {
                cloud.data.clear();
            }
            let original = cloud.data.clone();
            assert_eq!(
                PointCloudReader::try_new(&cloud, Some(&selection)).err(),
                Some(expected.clone())
            );
            assert_eq!(
                PointCloudWriter::try_new(&mut cloud, Some(&selection)).err(),
                Some(expected.clone())
            );
            assert_eq!(cloud.data, original);
        }
    }
    #[test]
    fn typed_writer_checks_wrong_types_for_empty_clouds() {
        let mut cloud = message(
            1,
            0,
            4,
            4,
            vec![PointField::new("value", 0, FieldDatatype::Uint16, 1)],
            vec![],
        );
        assert_eq!(
            PointCloudWriter::try_new_typed(&mut cloud, (Field::<u8>::new("value"),)).err(),
            Some(
                PointFieldError::DatatypeMismatch {
                    name: "value",
                    expected: FieldDatatype::Uint8,
                    actual: FieldDatatype::Uint16,
                }
                .into()
            )
        );
        assert!(cloud.data.is_empty());
    }
}
