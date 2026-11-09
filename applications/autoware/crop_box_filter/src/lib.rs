//! Port of ROS2 Autoware crop box filter to Awkernel.
//!
//! ## Reference Implementation
//!
//! This port is based on the [Autoware v1.18.0 counterpart](https://github.com/autowarefoundation/autoware_core/blob/1.8.0/sensing/autoware_crop_box_filter/src/crop_box_filter.cpp).
//!
//! ## Differences from ROS2 Autoware
//!
//! Unless explicitly mentioned, there are no functional differences with the original implementation.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use common_types::{
    geometry::{Polygon, PolygonStamped},
    point_cloud::{Field, PointCloud, PointCloudError, PointCloudReader, PointFieldError},
    transform::TransformStamped,
    Header, Matrix4, Vector3, Vector4,
};

/// Errors related to the crop box filter.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CropBoxFilterError {
    /// The crop box parameters are invalid.
    InvalidCropBoxParam,
    /// The requested coordinate field is missing or has an invalid layout.
    PointField(PointFieldError),
    /// The output cloud could not be constructed or its input cloud could not be accessed.
    PointCloud(PointCloudError),
    /// The bytes of a point lie outside the cloud data.
    PointOutOfBounds { point_index: usize },
}

impl From<PointFieldError> for CropBoxFilterError {
    fn from(error: PointFieldError) -> Self {
        Self::PointField(error)
    }
}

impl From<PointCloudError> for CropBoxFilterError {
    fn from(error: PointCloudError) -> Self {
        match error {
            PointCloudError::InvalidField(error) => Self::PointField(error),
            error => Self::PointCloud(error),
        }
    }
}

impl core::fmt::Display for CropBoxFilterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidCropBoxParam => write!(f, "Invalid crop box parameters"),
            Self::PointField(error) => write!(f, "{error}"),
            Self::PointCloud(error) => write!(f, "{error}"),
            Self::PointOutOfBounds { point_index } => {
                write!(f, "Point {point_index} lies outside the cloud data")
            }
        }
    }
}

impl core::error::Error for CropBoxFilterError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::PointField(error) => Some(error),
            Self::PointCloud(error) => Some(error),
            _ => None,
        }
    }
}

pub type Result<T> = core::result::Result<T, CropBoxFilterError>;

/// Parameters for the crop box filter, defining the minimum and maximum coordinates along each axis.
///
/// The original Autoware struct can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.hpp#L41).
///
/// # Differences from the original Autoware struct
///
/// The original struct uses public fields, whereas this Rust version uses private fields with a constructor for validation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct CropBoxParam {
    min_x: f32,
    max_x: f32,
    min_y: f32,
    max_y: f32,
    min_z: f32,
    max_z: f32,
}

impl CropBoxParam {
    /// Creates a new `CropBoxParam` with the given minimum and maximum coordinates.
    ///
    /// Returns an error if the minimum coordinates are greater than the maximum coordinates.
    pub const fn try_new(
        min_x: f32,
        max_x: f32,
        min_y: f32,
        max_y: f32,
        min_z: f32,
        max_z: f32,
    ) -> Result<Self> {
        if min_x > max_x || min_y > max_y || min_z > max_z {
            return Err(CropBoxFilterError::InvalidCropBoxParam);
        }

        Ok(Self {
            min_x,
            max_x,
            min_y,
            max_y,
            min_z,
            max_z,
        })
    }

    /// Generates a polygon representing the crop box.
    pub fn polygon(&self) -> Polygon {
        let x1 = self.max_x;
        let x2 = self.min_x;
        let x3 = self.min_x;
        let x4 = self.max_x;

        let y1 = self.max_y;
        let y2 = self.max_y;
        let y3 = self.min_y;
        let y4 = self.min_y;

        let z1 = self.min_z;
        let z2 = self.max_z;

        let mut points = Vec::with_capacity(16);

        points.push(Vector3::new(x1, y1, z1));
        points.push(Vector3::new(x2, y2, z1));
        points.push(Vector3::new(x3, y3, z1));
        points.push(Vector3::new(x4, y4, z1));
        points.push(Vector3::new(x1, y1, z1));

        points.push(Vector3::new(x1, y1, z2));

        points.push(Vector3::new(x2, y2, z2));
        points.push(Vector3::new(x2, y2, z1));
        points.push(Vector3::new(x2, y2, z2));

        points.push(Vector3::new(x3, y3, z2));
        points.push(Vector3::new(x3, y3, z1));
        points.push(Vector3::new(x3, y3, z2));

        points.push(Vector3::new(x4, y4, z2));
        points.push(Vector3::new(x4, y4, z1));
        points.push(Vector3::new(x4, y4, z2));

        points.push(Vector3::new(x1, y1, z2));
        Polygon { points }
    }
}

/// Generates a stamped polygon representing the crop box with the given parameters.
///
/// The original Autoware function can be found [here]([`generate_crop_box_polygon`](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.cpp#L82)).
#[inline]
pub fn generate_crop_box_polygon(
    param: &CropBoxParam,
    frame_id: &'static str,
    timestamp: u64,
) -> PolygonStamped {
    param.polygon().into_stamped(Header {
        frame_id,
        timestamp,
    })
}

/// Configuration for the crop box filter.
///
/// The original Autoware struct can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.hpp#L51)
pub struct CropBoxFilterConfig {
    /// The parameters defining the crop box.
    pub param: CropBoxParam,
    /// Whether to keep points outside the crop box instead of inside.
    pub keep_outside_box: bool,
    /// Optional transform to apply to the point cloud before filtering.
    pub preprocess_transform: Option<TransformStamped>,
    /// Optional transform to apply to the point cloud after filtering.
    pub postprocess_transform: Option<TransformStamped>,
}

/// Result of the crop box filter.
///
/// The original Autoware struct can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.hpp#L59)
pub struct CropBoxFilterResult {
    pub point_cloud: PointCloud,
    pub skipped_nan_count: usize,
}

/// Crop box filter that applies the configured transforms and keeps points inside or outside the box.
///
/// The original Autoware class can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.hpp#L65)
pub struct CropBoxFilter {
    config: CropBoxFilterConfig,
    eigen_transform_preprocess: Matrix4<f32>, // TODO use Isometry3<f32> instead of Matrix4<f32>
    eigen_transform_postprocess: Matrix4<f32>, // TODO use Isometry3<f32> instead of Matrix4<f32>
    output_frame_id: Option<&'static str>,
}

impl CropBoxFilter {
    /// Creates a new crop box filter with the given configuration.
    ///
    /// The original Autoware constructor can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.cpp#L135)
    pub fn new(config: CropBoxFilterConfig) -> Self {
        let mut output_frame_id = None;
        let mut eigen_transform_preprocess = Matrix4::identity();
        let mut eigen_transform_postprocess = Matrix4::identity();

        // TODO: store `Isometry3<f32>` to avoid the full 4x4 multiply and keep the rigid-transform invariant.
        if let Some(transform) = &config.preprocess_transform {
            eigen_transform_preprocess = transform.to_isometry().to_homogeneous().cast::<f32>();
            output_frame_id = Some(transform.header.frame_id);
        }
        // TODO: store `Isometry3<f32>` to avoid the full 4x4 multiply and keep the rigid-transform invariant.
        if let Some(transform) = &config.postprocess_transform {
            eigen_transform_postprocess = transform.to_isometry().to_homogeneous().cast::<f32>();
            output_frame_id = Some(transform.header.frame_id);
        }

        Self {
            config,
            eigen_transform_preprocess,
            eigen_transform_postprocess,
            output_frame_id,
        }
    }

    /// Keeps the points inside (or outside) the box and applies the transforms.
    ///
    /// The original Autoware function can be found [here](https://github.com/autowarefoundation/autoware_core/blob/16045061a9c10da468b60e190b8fab02110fa501/sensing/autoware_crop_box_filter/src/crop_box_filter.cpp#L149)
    ///
    /// Follows Autoware's C++ `CropBoxFilter::filter`.
    /// Coordinates are read from each point using the first value of each x/y/z
    /// field. Names, layouts, types, and nonempty value counts are validated before
    /// traversal, including for empty clouds. Traversal reuses typed metadata
    /// without further name or datatype checks. Retained points are copied and
    /// their transformed coordinates are written in the same pass.
    ///
    /// Input data must use native byte order, even for empty clouds; unsupported
    /// endianness is propagated as a point-cloud error before field validation.
    ///
    /// # Differences from original Autoware function
    ///
    /// - Uses Rust error handling instead of C++ exceptions.
    /// - Point Cloud format error checking is more restrictive. Check [PointCloudReader::try_new_typed] for details.
    /// - The first appearance of the "x", "y", and "z" fields is used for reading coordinates.
    ///   This first appearance must present the expected type (`f32`).
    ///     - In the original Autoware C++ function, it used the first appearance that matched the expected type for each coordinate field.
    ///       This allowed duplicate field names as long as one of them matched the expected type.
    /// - It checks that fields have nonzero length before processing points.
    pub fn filter(&self, cloud: &PointCloud) -> Result<CropBoxFilterResult> {
        let message = cloud;
        let cloud = PointCloudReader::try_new_typed(
            message,
            (
                Field::<f32>::new("x"),
                Field::<f32>::new("y"),
                Field::<f32>::new("z"),
            ),
        )?;
        // Make sure all fields have nonzero length.
        for field in cloud.fields() {
            if field.count() == 0 {
                return Err(PointFieldError::InvalidLength.into());
            }
        }

        let data_len = cloud.data().len();
        let point_count = cloud.point_count();

        let mut output_data = Vec::with_capacity(data_len);
        let mut width = 0;
        let mut skipped_nan_count = 0_usize;

        // Iterate over each point in the cloud and apply the crop box filter.
        for point_index in 0..point_count {
            let point_reader = cloud.point(point_index)?;
            let (x, y, z) = point_reader.fields();
            let point = Vector4::new(x.value(0)?, y.value(0)?, z.value(0)?, 1.0);
            // Skip points with NaN coordinates.
            if !point.x.is_finite() || !point.y.is_finite() || !point.z.is_finite() {
                skipped_nan_count += 1;
                continue;
            }

            let point_preprocessed = self.eigen_transform_preprocess * point;

            let param = &self.config.param;
            let point_is_inside = point_preprocessed.z > param.min_z
                && point_preprocessed.z < param.max_z
                && point_preprocessed.y > param.min_y
                && point_preprocessed.y < param.max_y
                && point_preprocessed.x > param.min_x
                && point_preprocessed.x < param.max_x;

            // If point is eligible to be included in the output cloud, process it.
            if point_is_inside != self.config.keep_outside_box {
                let point_postprocessed = self.eigen_transform_postprocess * point_preprocessed;

                // Copy the original point bytes to the output...
                let output_start = output_data.len();
                output_data.extend_from_slice(point_reader.bytes());
                let output_slice = &mut output_data[output_start..];
                // ... and overwrite the x, y, z values with the postprocessed coordinates.
                cloud.point_writer_from_bytes(output_slice)?.write_values(
                    0,
                    (
                        point_postprocessed.x,
                        point_postprocessed.y,
                        point_postprocessed.z,
                    ),
                )?;
                width += 1;
            }
        }

        Ok(CropBoxFilterResult {
            point_cloud: PointCloud {
                header: Header {
                    frame_id: self.output_frame_id.unwrap_or(message.header.frame_id),
                    timestamp: message.header.timestamp,
                },
                height: 1,
                width,
                fields: message.fields.clone(),
                is_bigendian: message.is_bigendian,
                point_step: message.point_step,
                row_step: width * message.point_step,
                data: output_data,
                is_dense: message.is_dense,
            },
            skipped_nan_count,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{string::ToString, vec};
    use common_types::{
        point_cloud::{FieldDatatype, PointField},
        transform::Transform,
        UnitQuaternion,
    };

    const POINT_STEP: u32 = 16;

    #[expect(
        clippy::too_many_arguments,
        reason = "test code: constructs all nine public message fields"
    )]
    fn message(
        header: Header,
        height: u32,
        width: u32,
        fields: Vec<PointField>,
        is_bigendian: bool,
        point_step: u32,
        row_step: u32,
        data: Vec<u8>,
        is_dense: bool,
    ) -> PointCloud {
        PointCloud {
            header,
            height,
            width,
            fields,
            is_bigendian,
            point_step,
            row_step,
            data,
            is_dense,
        }
    }

    fn fields() -> Vec<PointField> {
        ["x", "y", "z", "intensity"]
            .into_iter()
            .zip([0, 4, 8, 12])
            .map(|(name, offset)| PointField {
                name,
                offset,
                datatype: FieldDatatype::Float32,
                count: 1,
            })
            .collect()
    }

    fn cloud(points: &[[f32; 4]]) -> PointCloud {
        let data = points
            .iter()
            .flatten()
            .flat_map(|value| value.to_ne_bytes())
            .collect();
        message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            1,
            u32::try_from(points.len()).unwrap(),
            fields(),
            cfg!(target_endian = "big"),
            POINT_STEP,
            POINT_STEP * u32::try_from(points.len()).unwrap(),
            data,
            false,
        )
    }

    fn points(cloud: &PointCloud) -> Vec<[f32; 4]> {
        let (points, remainder) = cloud.data.as_chunks::<4>();
        assert!(remainder.is_empty());
        let values: Vec<f32> = points
            .iter()
            .map(|bytes| f32::from_ne_bytes(*bytes))
            .collect();
        values.as_chunks::<4>().0.to_vec()
    }

    fn filter(keep_outside_box: bool) -> CropBoxFilter {
        CropBoxFilter::new(CropBoxFilterConfig {
            param: CropBoxParam {
                min_x: -1.0,
                max_x: 1.0,
                min_y: -1.0,
                max_y: 1.0,
                min_z: -1.0,
                max_z: 1.0,
            },
            keep_outside_box,
            preprocess_transform: None,
            postprocess_transform: None,
        })
    }

    fn translation(frame_id: &'static str, x: f64) -> TransformStamped {
        TransformStamped::new(
            Header {
                frame_id,
                timestamp: 0,
            },
            "lidar",
            Transform::new(Vector3::new(x, 0.0, 0.0), UnitQuaternion::identity()),
        )
    }

    const INPUT: [[f32; 4]; 5] = [
        [0.0, 0.0, 0.0, 10.0],
        [2.0, 0.0, 0.0, 20.0],
        [f32::NAN, 0.0, 0.0, 30.0],
        [0.5, -0.5, 0.5, 40.0],
        [1.0, 0.0, 0.0, 50.0],
    ];

    #[test]
    fn keeps_points_strictly_inside_and_skips_non_finite() {
        let result = filter(false).filter(&cloud(&INPUT)).unwrap();
        let output = result.point_cloud;

        assert_eq!(result.skipped_nan_count, 1);
        assert_eq!(
            points(&output),
            vec![[0.0, 0.0, 0.0, 10.0], [0.5, -0.5, 0.5, 40.0]]
        );
        assert_eq!(output.header.frame_id, "lidar");
        assert_eq!(output.header.timestamp, 42);
        assert_eq!((output.height, output.width), (1, 2));
        assert_eq!((output.point_step, output.row_step), (16, 32));
        assert_eq!(output.fields, fields());
        assert_eq!(output.is_bigendian, cfg!(target_endian = "big"));
        assert!(!output.is_dense);
    }

    #[test]
    fn keep_outside_box_inverts_selection() {
        let result = filter(true).filter(&cloud(&INPUT)).unwrap();

        assert_eq!(result.skipped_nan_count, 1);
        assert_eq!(
            points(&result.point_cloud),
            vec![[2.0, 0.0, 0.0, 20.0], [1.0, 0.0, 0.0, 50.0]]
        );
    }

    #[test]
    fn applies_preprocess_for_cropping_and_postprocess_for_output() {
        let mut config = filter(false).config;
        config.preprocess_transform = Some(translation("base_link", -2.0));
        config.postprocess_transform = Some(translation("map", 10.0));

        let result = CropBoxFilter::new(config).filter(&cloud(&INPUT)).unwrap();
        let output = result.point_cloud;

        // Only x = 2 lands inside after the -2 preprocess shift; output is shifted by +10.
        assert_eq!(points(&output), vec![[10.0, 0.0, 0.0, 20.0]]);
        assert_eq!(output.header.frame_id, "map");
    }

    #[test]
    fn writes_overlapping_coordinates_in_xyz_order() {
        let mut input = cloud(&[[0.25, 100.0, 200.0, 42.0]]);
        for field in input.fields.iter_mut().take(3) {
            field.offset = 0;
        }
        input.fields.push(PointField {
            name: "x",
            offset: 4,
            datatype: FieldDatatype::Float32,
            count: 1,
        });
        let original = input.data.clone();
        let mut config = filter(false).config;
        config.postprocess_transform = Some(TransformStamped::new(
            Header {
                frame_id: "map",
                timestamp: 0,
            },
            "lidar",
            Transform::new(Vector3::new(1.0, 2.0, 3.0), UnitQuaternion::identity()),
        ));

        let result = CropBoxFilter::new(config).filter(&input).unwrap();
        let mut expected = original.clone();
        expected[..4].copy_from_slice(&3.25_f32.to_ne_bytes());
        assert_eq!(result.point_cloud.data, expected);
        assert_eq!(result.point_cloud.fields, input.fields);
        assert_eq!(
            (result.point_cloud.width, result.point_cloud.row_step),
            (1, 16)
        );
        assert_eq!(input.data, original);
    }

    #[test]
    fn empty_cloud_produces_empty_output() {
        let result = filter(false).filter(&cloud(&[])).unwrap();

        assert_eq!(result.skipped_nan_count, 0);
        assert!(result.point_cloud.data.is_empty());
        assert_eq!(
            (result.point_cloud.width, result.point_cloud.row_step),
            (0, 0)
        );
    }

    #[test]
    fn unsupported_endianness_propagates_without_mutating_input() {
        for mut input in [cloud(&INPUT), cloud(&[])] {
            input.is_bigendian = !cfg!(target_endian = "big");
            let original_data = input.data.clone();
            let original_fields = input.fields.clone();
            for keep_outside in [false, true] {
                let error = filter(keep_outside).filter(&input).err().unwrap();
                assert_eq!(
                    error,
                    CropBoxFilterError::PointCloud(PointCloudError::UnsupportedEndianness)
                );
                let source = core::error::Error::source(&error).unwrap();
                assert_eq!(
                    source.downcast_ref::<PointCloudError>(),
                    Some(&PointCloudError::UnsupportedEndianness)
                );
                assert_eq!(error.to_string(), "Point cloud endianness is not native");
                assert!(source.source().is_none());
                assert_eq!(input.data, original_data);
                assert_eq!(input.fields, original_fields);
                assert_eq!(input.is_bigendian, !cfg!(target_endian = "big"));
            }
        }
    }

    #[test]
    fn filtering_handles_padded_input_rows() {
        let packed = cloud(&[
            [0.0, 0.0, 0.0, 10.0],
            [2.0, 0.0, 0.0, 20.0],
            [0.5, 0.5, 0.5, 30.0],
            [3.0, 0.0, 0.0, 40.0],
        ]);
        let mut data = Vec::new();
        for row in packed.data.as_chunks::<32>().0 {
            data.extend_from_slice(row);
            data.extend_from_slice(&[0xAA; 4]);
        }
        let padded = message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            2,
            2,
            fields(),
            cfg!(target_endian = "big"),
            POINT_STEP,
            36,
            data,
            false,
        );

        let result = filter(false).filter(&padded).unwrap();
        assert_eq!(
            points(&result.point_cloud),
            vec![[0.0, 0.0, 0.0, 10.0], [0.5, 0.5, 0.5, 30.0]]
        );
        assert_eq!(result.point_cloud.row_step, 32);
    }

    #[test]
    fn rejects_malformed_layouts() {
        let missing_z_fields = fields()
            .into_iter()
            .filter(|field| field.name != "z")
            .collect::<Vec<_>>();
        let missing_z = message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            1,
            u32::try_from(INPUT.len()).unwrap(),
            missing_z_fields,
            cfg!(target_endian = "big"),
            POINT_STEP,
            POINT_STEP * u32::try_from(INPUT.len()).unwrap(),
            cloud(&INPUT).data.to_vec(),
            false,
        );
        assert_eq!(
            filter(false).filter(&missing_z).err(),
            Some(CropBoxFilterError::PointField(
                PointFieldError::FieldNotFound("z")
            ))
        );

        assert_eq!(
            PointCloudReader::try_new(
                &message(
                    Header {
                        frame_id: "lidar",
                        timestamp: 42,
                    },
                    1,
                    1,
                    fields(),
                    cfg!(target_endian = "big"),
                    0,
                    0,
                    Vec::new(),
                    false,
                ),
                None
            )
            .err(),
            Some(PointCloudError::ZeroPointStep)
        );

        assert_eq!(
            PointCloudReader::try_new(
                &message(
                    Header {
                        frame_id: "lidar",
                        timestamp: 42,
                    },
                    1,
                    1,
                    fields(),
                    cfg!(target_endian = "big"),
                    POINT_STEP,
                    POINT_STEP,
                    vec![0; 15],
                    false,
                ),
                None
            )
            .err(),
            Some(PointCloudError::InvalidDataSize {
                size: 15,
                expected: 16,
            })
        );

        let invalid_z = message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            1,
            1,
            vec![
                PointField {
                    name: "x",
                    offset: 0,
                    datatype: FieldDatatype::Float32,
                    count: 1,
                },
                PointField {
                    name: "y",
                    offset: 4,
                    datatype: FieldDatatype::Float32,
                    count: 1,
                },
                PointField {
                    name: "z",
                    offset: 13,
                    datatype: FieldDatatype::Float32,
                    count: 1,
                },
            ],
            cfg!(target_endian = "big"),
            POINT_STEP,
            POINT_STEP,
            vec![0; 16],
            false,
        );
        assert_eq!(
            filter(false).filter(&invalid_z).err(),
            Some(CropBoxFilterError::PointField(
                PointFieldError::FieldOutOfBounds {
                    name: "z",
                    offset_start: 13,
                    offset_end: 17,
                    point_step: usize::try_from(POINT_STEP).unwrap(),
                }
            ))
        );
    }

    #[test]
    fn validates_coordinates_even_when_cloud_is_empty() {
        let make_empty = |fields| {
            message(
                Header {
                    frame_id: "lidar",
                    timestamp: 42,
                },
                1,
                0,
                fields,
                cfg!(target_endian = "big"),
                POINT_STEP,
                0,
                Vec::new(),
                false,
            )
        };
        let missing = make_empty(
            fields()
                .into_iter()
                .filter(|field| field.name != "z")
                .collect(),
        );
        assert_eq!(
            filter(false).filter(&missing).err(),
            Some(CropBoxFilterError::PointField(
                PointFieldError::FieldNotFound("z")
            ))
        );
        let mut invalid_fields = fields();
        let later_valid_y = invalid_fields[1];
        invalid_fields[1].datatype = FieldDatatype::Uint32;
        invalid_fields.push(later_valid_y); // A later matching type must not mask the first name.
        assert_eq!(
            filter(false).filter(&make_empty(invalid_fields)).err(),
            Some(CropBoxFilterError::PointField(
                PointFieldError::DatatypeMismatch {
                    name: "y",
                    expected: FieldDatatype::Float32,
                    actual: FieldDatatype::Uint32,
                }
            ))
        );
        let mut empty_coordinate = fields();
        empty_coordinate[0].count = 0;
        assert_eq!(
            filter(false).filter(&make_empty(empty_coordinate)).err(),
            Some(CropBoxFilterError::PointField(
                PointFieldError::InvalidLength
            ))
        );
    }

    #[test]
    fn ignores_malformed_unused_fields_but_validates_public_message_shape() {
        let mut input = cloud(&[]);
        input.fields.push(PointField {
            name: "unused",
            offset: 15,
            datatype: FieldDatatype::Uint16,
            count: 1,
        });
        let result = filter(false).filter(&input).unwrap();
        assert_eq!(result.point_cloud.fields.last(), input.fields.last());
        assert_eq!(result.point_cloud.data, input.data);
        input.fields.pop().unwrap();
        input.point_step = 0;
        assert_eq!(
            filter(false).filter(&input).err(),
            Some(CropBoxFilterError::PointCloud(
                PointCloudError::ZeroPointStep
            ))
        );
    }

    #[test]
    fn unified_cloud_errors_preserve_filter_error_sources() {
        let field_error = PointFieldError::FieldNotFound("x");
        assert_eq!(
            CropBoxFilterError::from(PointCloudError::InvalidField(field_error)),
            CropBoxFilterError::PointField(field_error)
        );
        let field_bounds_error = PointCloudError::InvalidField(PointFieldError::ValueOutOfBounds {
            name: "x",
            index: 0,
            count: 0,
        });
        let error = CropBoxFilterError::from(field_bounds_error.clone());
        assert_eq!(
            error,
            CropBoxFilterError::PointField(PointFieldError::ValueOutOfBounds {
                name: "x",
                index: 0,
                count: 0,
            })
        );
        assert_eq!(
            core::error::Error::source(&error).unwrap().to_string(),
            "Value 0 of field x is outside its 0 values"
        );

        let cloud_error = PointCloudError::PointOutOfBounds { index: 0, count: 0 };
        let error = CropBoxFilterError::from(cloud_error.clone());
        assert_eq!(error, CropBoxFilterError::PointCloud(cloud_error));
        assert_eq!(
            core::error::Error::source(&error).unwrap().to_string(),
            "Point 0 is outside cloud of 0 points"
        );
    }

    #[test]
    fn point_access_checks_selected_fields_and_value_bounds() {
        let input = cloud(&INPUT);
        let selection =
            PointCloudReader::try_new(&input, Some(&[("x", FieldDatatype::Float32)])).unwrap();
        assert!(matches!(
            selection
                .point(3)
                .unwrap()
                .field("x")
                .unwrap()
                .into_typed::<f32>()
                .unwrap()
                .value(0),
            Ok(value) if value == INPUT[3][0]
        ));
        assert!(matches!(
            selection
                .point(0)
                .unwrap()
                .field("x")
                .and_then(|raw| raw.into_typed::<f32>())
                .and_then(|typed| typed.value(1)),
            Err(PointCloudError::InvalidField(
                PointFieldError::ValueOutOfBounds {
                    name: "x",
                    index: 1,
                    count: 1,
                }
            ))
        ));
        assert!(matches!(
            selection.point(0).unwrap().field("y"),
            Err(PointCloudError::InvalidField(
                PointFieldError::FieldNotFound("y")
            ))
        ));
        assert!(matches!(
            selection
                .point(0)
                .unwrap()
                .field("x")
                .unwrap()
                .into_typed::<u32>(),
            Err(PointCloudError::InvalidField(
                PointFieldError::DatatypeMismatch { .. }
            ))
        ));
    }

    #[test]
    fn reads_first_coordinate_value_and_preserves_remaining_values() {
        let coordinate_fields = ["x", "y", "z"]
            .into_iter()
            .zip([0, 8, 16])
            .map(|(name, offset)| PointField {
                name,
                offset,
                datatype: FieldDatatype::Float32,
                count: 2,
            })
            .collect();
        let values = [0.0_f32, f32::NAN, 0.5, f32::INFINITY, -0.5, 42.0];
        let data = values.into_iter().flat_map(f32::to_ne_bytes).collect();
        let input = message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            1,
            1,
            coordinate_fields,
            cfg!(target_endian = "big"),
            24,
            24,
            data,
            false,
        );
        let result = filter(false).filter(&input).unwrap();
        let reader = PointCloudReader::try_new(&input, None).unwrap();
        assert_eq!(
            reader
                .point(0)
                .unwrap()
                .field("z")
                .unwrap()
                .into_typed::<f32>()
                .unwrap()
                .values()
                .collect::<core::result::Result<Vec<_>, _>>()
                .unwrap(),
            vec![-0.5, 42.0]
        );
        assert_eq!(
            PointCloudReader::try_new(&result.point_cloud, None)
                .unwrap()
                .point_count(),
            1
        );
        assert_eq!(result.skipped_nan_count, 0);
        assert_eq!(result.point_cloud.data, input.data);
    }

    #[test]
    fn transforms_unaligned_coordinates_preserving_extra_values_and_point_padding() {
        let mut input_fields: Vec<_> = ["x", "y", "z"]
            .into_iter()
            .zip([1, 9, 17])
            .map(|(name, offset)| PointField {
                name,
                offset,
                datatype: FieldDatatype::Float32,
                count: 2,
            })
            .collect();
        // Unselected malformed metadata must remain ignored during output construction.
        input_fields.push(PointField {
            name: "unused",
            offset: 27,
            datatype: FieldDatatype::Float64,
            count: 1,
        });
        let packed: Vec<Vec<u8>> = [0.25_f32, 2.25, 0.75, 3.25]
            .into_iter()
            .map(|x| {
                let mut bytes = vec![0xAA];
                for value in [x, f32::NAN, 0.0, f32::INFINITY, 0.0, 42.0] {
                    bytes.extend_from_slice(&value.to_ne_bytes());
                }
                bytes.extend_from_slice(&[0xBB; 3]);
                bytes
            })
            .collect();
        let mut data = Vec::new();
        for row in packed.as_chunks::<2>().0 {
            for point in row {
                data.extend_from_slice(point);
            }
            data.extend_from_slice(&[0xCC; 3]);
        }
        let input = message(
            Header {
                frame_id: "lidar",
                timestamp: 42,
            },
            2,
            2,
            input_fields,
            cfg!(target_endian = "big"),
            28,
            59,
            data,
            false,
        );
        let mut config = filter(false).config;
        config.preprocess_transform = Some(translation("base_link", -0.25));
        config.postprocess_transform = Some(TransformStamped::new(
            Header {
                frame_id: "map",
                timestamp: 0,
            },
            "lidar",
            Transform::new(Vector3::new(10.0, 20.0, 30.0), UnitQuaternion::identity()),
        ));
        let result = CropBoxFilter::new(config).filter(&input).unwrap();
        let mut expected = Vec::new();
        for (index, x) in [(0, 10.0_f32), (2, 10.5)] {
            let mut bytes = packed[index].clone();
            bytes[1..5].copy_from_slice(&x.to_ne_bytes());
            bytes[9..13].copy_from_slice(&20.0_f32.to_ne_bytes());
            bytes[17..21].copy_from_slice(&30.0_f32.to_ne_bytes());
            expected.extend_from_slice(&bytes);
        }
        assert_eq!(result.point_cloud.data, expected);
        assert_eq!(result.point_cloud.fields, input.fields);
        assert_eq!(result.point_cloud.header.frame_id, "map");
        assert_eq!(
            (result.point_cloud.width, result.point_cloud.row_step),
            (2, 56)
        );
        assert_eq!(result.point_cloud.is_bigendian, cfg!(target_endian = "big"));
        assert_eq!(result.skipped_nan_count, 0);
    }
}
