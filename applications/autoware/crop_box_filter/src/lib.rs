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

use alloc::{vec, vec::Vec};
use common_types::{
    geometry::{Polygon, PolygonStamped},
    point_cloud::{PointCloud, PointCloudError, PointFieldError},
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
    /// The copied point lies outside the output buffer.
    PointOutOfBounds { point_index: usize },
}

impl From<PointFieldError> for CropBoxFilterError {
    fn from(error: PointFieldError) -> Self {
        Self::PointField(error)
    }
}

impl From<PointCloudError> for CropBoxFilterError {
    fn from(error: PointCloudError) -> Self {
        Self::PointCloud(error)
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

    /// Returns the minimum x-coordinate of the crop box.
    #[inline]
    pub const fn min_x(&self) -> f32 {
        self.min_x
    }

    /// Returns the maximum x-coordinate of the crop box.
    #[inline]
    pub const fn max_x(&self) -> f32 {
        self.max_x
    }

    /// Returns the minimum y-coordinate of the crop box.
    #[inline]
    pub const fn min_y(&self) -> f32 {
        self.min_y
    }

    /// Returns the maximum y-coordinate of the crop box.
    #[inline]
    pub const fn max_y(&self) -> f32 {
        self.max_y
    }

    /// Returns the minimum z-coordinate of the crop box.
    #[inline]
    pub const fn min_z(&self) -> f32 {
        self.min_z
    }

    /// Returns the maximum z-coordinate of the crop box.
    #[inline]
    pub const fn max_z(&self) -> f32 {
        self.max_z
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

        let points = vec![
            Vector3::new(x1, y1, z1),
            Vector3::new(x2, y2, z1),
            Vector3::new(x3, y3, z1),
            Vector3::new(x4, y4, z1),
            Vector3::new(x1, y1, z1),
            Vector3::new(x1, y1, z2),
            Vector3::new(x2, y2, z2),
            Vector3::new(x2, y2, z1),
            Vector3::new(x2, y2, z2),
            Vector3::new(x3, y3, z2),
            Vector3::new(x3, y3, z1),
            Vector3::new(x3, y3, z2),
            Vector3::new(x4, y4, z2),
            Vector3::new(x4, y4, z1),
            Vector3::new(x4, y4, z2),
            Vector3::new(x1, y1, z2),
        ];
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
    /// - The first field matching both name and `f32` type is selected for each axis.
    /// - Coordinates are read from each point using the first value of each x/y/z field.
    /// - Retained points are copied and their transformed coordinates are written in the same pass.
    /// - Cropping uses strict bounds after the f32 preprocess transform, followed by the f32 postprocess transform for retained points.
    /// - Nonfinite input xyz values are skipped and counted (including infinities).
    /// - Transform-generated nonfinite values retain IEEE comparison/output behavior: they are not counted as skipped input values.
    /// - All other point bytes are preserved; overlapping xyz writes are applied in x, then y, then z order.
    /// - Output is packed: nonempty clouds have height 1, width equal to retained points, and row step equal to data length.
    ///
    /// # Differences from original Autoware function
    ///
    /// - Uses Rust error handling instead of C++ exceptions.
    /// - Point cloud format checking is more restrictive; see [`PointCloud::try_new`].
    pub fn filter(&self, cloud: &PointCloud) -> Result<CropBoxFilterResult> {
        let x = cloud.get_field::<f32>("x")?;
        let y = cloud.get_field::<f32>("y")?;
        let z = cloud.get_field::<f32>("z")?;

        let data_len = cloud.data().len();
        let mut output_data = Vec::with_capacity(data_len);
        let mut width = 0_usize;
        let mut skipped_nan_count = 0_usize;

        // Iterate over each point in the cloud and apply the crop box filter.
        for point_bytes in cloud.iter_points() {
            let point = Vector4::new(
                x.try_read(point_bytes, 0)?,
                y.try_read(point_bytes, 0)?,
                z.try_read(point_bytes, 0)?,
                1.0,
            );
            // Skip points with nonfinite input coordinates.
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
                let output_end = output_start + cloud.point_step();
                output_data.extend_from_slice(point_bytes);
                let output_slice = &mut output_data[output_start..output_end];
                // ... and overwrite the x, y, z values with the postprocessed coordinates.
                x.try_write(output_slice, 0, point_postprocessed.x)?;
                y.try_write(output_slice, 0, point_postprocessed.y)?;
                z.try_write(output_slice, 0, point_postprocessed.z)?;

                width = width + 1;
            }
        }

        let point_step = cloud.point_step() as u32;
        // If no points were retained, set height to 0 and width to 1 to maintain a valid point cloud structure.
        let (height, width, row_step) = if width == 0 {
            (0, 1, point_step)
        } else {
            (1, width as u32, output_data.len() as u32)
        };
        Ok(CropBoxFilterResult {
            point_cloud: PointCloud::try_new(
                Header {
                    // No configured transform means retaining the input frame.
                    frame_id: self.output_frame_id.unwrap_or(cloud.header().frame_id),
                    timestamp: cloud.header().timestamp,
                },
                height,
                width,
                cloud.fields().to_vec(),
                cloud.is_bigendian(),
                point_step,
                row_step,
                output_data,
                cloud.is_dense(),
            )?,
            skipped_nan_count,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{string::ToString, vec};
    use common_types::{
        point_field::{FieldDatatype, PointField},
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
        PointCloud::try_new(
            header,
            height,
            width,
            fields,
            is_bigendian,
            point_step,
            row_step,
            data,
            is_dense,
        )
        .unwrap()
    }

    fn field(name: &'static str, offset: u32, datatype: FieldDatatype, count: u32) -> PointField {
        PointField::try_new(name, offset, datatype, count).unwrap()
    }

    fn fields() -> Vec<PointField> {
        ["x", "y", "z", "intensity"]
            .into_iter()
            .zip([0, 4, 8, 12])
            .map(|(name, offset)| field(name, offset, FieldDatatype::Float32, 1))
            .collect()
    }

    fn with_fields(input: &PointCloud, fields: Vec<PointField>) -> PointCloud {
        message(
            input.header().clone(),
            u32::try_from(input.height()).unwrap(),
            u32::try_from(input.width()).unwrap(),
            fields,
            input.is_bigendian(),
            u32::try_from(input.point_step()).unwrap(),
            u32::try_from(input.row_step()).unwrap(),
            input.data().to_vec(),
            input.is_dense(),
        )
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
            u32::from(!points.is_empty()),
            u32::try_from(points.len().max(1)).unwrap(),
            fields(),
            cfg!(target_endian = "big"),
            POINT_STEP,
            POINT_STEP * u32::try_from(points.len().max(1)).unwrap(),
            data,
            false,
        )
    }

    fn points(cloud: &PointCloud) -> Vec<[f32; 4]> {
        let (points, remainder) = cloud.data().as_chunks::<4>();
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
        assert_eq!(output.header().frame_id, "lidar");
        assert_eq!(output.header().timestamp, 42);
        assert_eq!((output.height(), output.width()), (1, 2));
        assert_eq!((output.point_step(), output.row_step()), (16, 32));
        assert_eq!(output.fields(), fields());
        assert_eq!(output.is_bigendian(), cfg!(target_endian = "big"));
        assert!(!output.is_dense());
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
        assert_eq!(output.header().frame_id, "map");
    }

    #[test]
    fn writes_overlapping_coordinates_in_xyz_order() {
        let packed = cloud(&[[0.25, 100.0, 200.0, 42.0]]);
        let input = with_fields(
            &packed,
            vec![
                field("x", 0, FieldDatatype::Float32, 1),
                field("y", 0, FieldDatatype::Float32, 1),
                field("z", 0, FieldDatatype::Float32, 1),
                field("x", 4, FieldDatatype::Float32, 1),
                field("intensity", 12, FieldDatatype::Float32, 1),
            ],
        );
        let original = input.data().to_vec();
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
        assert_eq!(result.point_cloud.data(), expected);
        assert_eq!(result.point_cloud.fields(), input.fields());
        assert_eq!(
            (result.point_cloud.width(), result.point_cloud.row_step()),
            (1, 16)
        );
        assert_eq!(input.data(), original);
    }

    #[test]
    fn empty_cloud_produces_empty_output() {
        let result = filter(false).filter(&cloud(&[])).unwrap();

        assert_eq!(result.skipped_nan_count, 0);
        assert!(result.point_cloud.data().is_empty());
        assert_eq!(
            (
                result.point_cloud.width(),
                result.point_cloud.height(),
                result.point_cloud.row_step()
            ),
            (1, 0, 16)
        );
    }

    #[test]
    fn empty_results_are_valid_clouds_with_preserved_metadata() {
        for keep_outside in [false, true] {
            let rejected = if keep_outside {
                [0.0, 0.0, 0.0, 7.0]
            } else {
                [2.0, 0.0, 0.0, 7.0]
            };
            for (input, expected_skips) in [
                (cloud(&[]), 0),
                (cloud(&[rejected]), 0),
                (cloud(&[[f32::INFINITY, 0.0, 0.0, 9.0]]), 1),
            ] {
                let mut config = filter(keep_outside).config;
                config.preprocess_transform = Some(translation("base_link", 0.0));
                let crop = CropBoxFilter::new(config);
                let result = crop.filter(&input).unwrap();
                let output = result.point_cloud;
                assert_eq!(
                    (output.width(), output.height(), output.point_count()),
                    (1, 0, 0)
                );
                assert_eq!(output.row_step(), output.point_step());
                assert_eq!(output.point_step(), input.point_step());
                assert!(output.data().is_empty());
                assert!(output.iter_points().next().is_none());
                assert_eq!(output.fields(), input.fields());
                assert_eq!(output.header().frame_id, "base_link");
                assert_eq!(output.header().timestamp, 42);
                assert_eq!(output.is_dense(), input.is_dense());
                assert_eq!(output.is_bigendian(), input.is_bigendian());
                assert_eq!(result.skipped_nan_count, expected_skips);
                // In particular, the canonical empty result is accepted as input again.
                let repeated = crop.filter(&output).unwrap();
                assert_eq!(
                    (repeated.point_cloud.width(), repeated.point_cloud.height()),
                    (1, 0)
                );
                assert!(repeated.point_cloud.data().is_empty());
            }
        }
    }

    #[test]
    fn all_six_faces_are_excluded_by_strict_bounds() {
        let input = cloud(&[
            [-1.0, 0.0, 0.0, 1.0],
            [1.0, 0.0, 0.0, 2.0],
            [0.0, -1.0, 0.0, 3.0],
            [0.0, 1.0, 0.0, 4.0],
            [0.0, 0.0, -1.0, 5.0],
            [0.0, 0.0, 1.0, 6.0],
        ]);
        assert!(filter(false)
            .filter(&input)
            .unwrap()
            .point_cloud
            .data()
            .is_empty());
        let outside = filter(true).filter(&input).unwrap();
        assert_eq!(outside.point_cloud.data(), input.data());
        assert_eq!(outside.skipped_nan_count, 0);
    }

    #[test]
    fn skips_nan_and_both_infinities_on_each_input_axis() {
        let mut input_points = Vec::new();
        for axis in 0..3 {
            for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
                let mut point = [0.0, 0.0, 0.0, 42.0];
                point[axis] = value;
                input_points.push(point);
            }
        }
        input_points.push([0.25, 0.5, 0.75, 99.0]);
        let input = cloud(&input_points);
        for keep_outside in [false, true] {
            let result = filter(keep_outside).filter(&input).unwrap();
            assert_eq!(result.skipped_nan_count, 9);
            if keep_outside {
                assert!(result.point_cloud.data().is_empty());
            } else {
                assert_eq!(points(&result.point_cloud), vec![[0.25, 0.5, 0.75, 99.0]]);
            }
        }
    }

    #[test]
    fn rounds_transform_coefficients_and_operations_to_f32() {
        let mut config = filter(false).config;
        // 2^24 + 1 rounds to 2^24 in f32. An f64 preprocess would yield
        // x = 1 (excluded), whereas the required f32 preprocess yields x = 0.
        config.preprocess_transform = Some(translation("base_link", 16_777_217.0));
        config.postprocess_transform = Some(translation("map", 16_777_217.0));
        let input = cloud(&[[-16_777_216.0, 0.0, 0.0, 42.0]]);
        let output = CropBoxFilter::new(config)
            .filter(&input)
            .unwrap()
            .point_cloud;
        assert_eq!(points(&output), vec![[16_777_216.0, 0.0, 0.0, 42.0]]);
        assert_eq!(output.header().frame_id, "map");
    }

    #[test]
    fn transform_generated_nonfinite_values_are_not_counted_as_input_skips() {
        let input = cloud(&[[0.0, 0.0, 0.0, 42.0]]);
        for value in [f64::INFINITY, f64::NAN] {
            for keep_outside in [false, true] {
                let mut config = filter(keep_outside).config;
                config.preprocess_transform = Some(translation("base_link", value));
                let result = CropBoxFilter::new(config).filter(&input).unwrap();
                assert_eq!(result.skipped_nan_count, 0);
                assert_eq!(result.point_cloud.point_count(), usize::from(keep_outside));
                if keep_outside {
                    let output = points(&result.point_cloud);
                    assert!(!output[0][0].is_finite());
                    assert_eq!(output[0][3], 42.0);
                }
            }
            let mut config = filter(false).config;
            config.postprocess_transform = Some(translation("map", value));
            let result = CropBoxFilter::new(config).filter(&input).unwrap();
            assert_eq!(result.skipped_nan_count, 0);
            assert_eq!(result.point_cloud.point_count(), 1);
            let output = points(&result.point_cloud);
            assert!(!output[0][0].is_finite());
            assert_eq!(output[0][3], 42.0);
        }
    }

    #[test]
    fn constructor_rejects_unsupported_endianness_even_when_empty() {
        for input in [cloud(&INPUT), cloud(&[])] {
            let error = PointCloud::try_new(
                input.header().clone(),
                u32::try_from(input.height()).unwrap(),
                u32::try_from(input.width()).unwrap(),
                input.fields().to_vec(),
                !cfg!(target_endian = "big"),
                POINT_STEP,
                u32::try_from(input.row_step()).unwrap(),
                input.data().to_vec(),
                input.is_dense(),
            )
            .unwrap_err();
            assert_eq!(error, PointCloudError::UnsupportedEndianness);
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
        for row in packed.data().as_chunks::<32>().0 {
            data.extend_from_slice(row);
            data.extend_from_slice(&[0xAA; 4]);
        }
        // Trailing bytes are valid metadata-wise, but are not points either.
        data.extend_from_slice(&[0xDD; 7]);
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
        assert_eq!(result.point_cloud.row_step(), 32);
    }

    #[test]
    fn constructor_rejects_malformed_layouts_including_unused_fields() {
        let header = cloud(&[]).header().clone();
        let construct = |height, width, point_step, row_step, fields, data| {
            PointCloud::try_new(
                header.clone(),
                height,
                width,
                fields,
                cfg!(target_endian = "big"),
                point_step,
                row_step,
                data,
                false,
            )
        };
        assert_eq!(
            construct(1, 0, 16, 16, fields(), vec![0; 16]).unwrap_err(),
            PointCloudError::ZeroWidth
        );
        assert_eq!(
            construct(1, 1, 16, 15, fields(), vec![0; 16]).unwrap_err(),
            PointCloudError::InvalidRowStep { step: 15, min: 16 }
        );
        assert_eq!(
            construct(1, 1, 16, 16, fields(), vec![0; 15]).unwrap_err(),
            PointCloudError::InvalidDataSize { size: 15, min: 16 }
        );
        // Even unselected metadata must fit, including for empty clouds.
        for height in [0, 1] {
            let mut invalid_fields = fields();
            invalid_fields.push(field("unused", 15, FieldDatatype::Uint16, 1));
            assert_eq!(
                construct(height, 1, 16, 16, invalid_fields, vec![0; 16]).unwrap_err(),
                PointCloudError::FieldOutOfBounds {
                    name: "unused",
                    offset_start: 15,
                    offset_end: 17,
                    point_step: 16,
                }
            );
        }
        assert!(matches!(
            construct(0, 1, 0, 0, fields(), Vec::new()),
            Err(PointCloudError::FieldOutOfBounds { .. })
        ));
    }

    #[test]
    fn validates_coordinate_name_and_type_upfront_and_count_when_reading() {
        for input in [cloud(&[]), cloud(&INPUT)] {
            for name in ["x", "y", "z"] {
                let missing = with_fields(
                    &input,
                    fields().into_iter().filter(|f| f.name() != name).collect(),
                );
                let wrong_type = with_fields(
                    &input,
                    fields()
                        .into_iter()
                        .map(|f| {
                            if f.name() == name {
                                field(
                                    name,
                                    u32::try_from(f.offset()).unwrap(),
                                    FieldDatatype::Uint32,
                                    1,
                                )
                            } else {
                                f
                            }
                        })
                        .collect(),
                );
                for invalid in [missing, wrong_type] {
                    assert_eq!(
                        filter(false).filter(&invalid).err(),
                        Some(CropBoxFilterError::PointField(
                            PointFieldError::FieldNotFound(name)
                        ))
                    );
                }
                let mut descriptors = fields();
                let position = descriptors.iter().position(|f| f.name() == name).unwrap();
                let offset = u32::try_from(descriptors[position].offset()).unwrap();
                descriptors[position] = field(name, offset, FieldDatatype::Float32, 0);
                // Lookup chooses the first *typed* match, even if a later one is nonempty.
                descriptors.push(field(name, offset, FieldDatatype::Float32, 1));
                let zero_count = with_fields(&input, descriptors);
                for keep_outside in [false, true] {
                    let result = filter(keep_outside).filter(&zero_count);
                    if input.point_count() == 0 {
                        let output = result.unwrap();
                        assert_eq!(output.point_cloud.point_count(), 0);
                        assert!(output.point_cloud.data().is_empty());
                        assert_eq!(output.skipped_nan_count, 0);
                    } else {
                        assert_eq!(
                            result.err(),
                            Some(CropBoxFilterError::PointField(
                                PointFieldError::ValueOutOfBounds {
                                    name,
                                    index: 0,
                                    count: 0,
                                }
                            ))
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn skips_wrong_type_duplicates_and_preserves_unused_zero_count_fields() {
        for input in [cloud(&[]), cloud(&INPUT)] {
            let mut descriptors = Vec::new();
            // These deliberately alias intensity, which would change selection if read.
            for name in ["x", "y", "z"] {
                descriptors.push(field(name, 12, FieldDatatype::Uint32, 0));
                descriptors.push(field(name, 12, FieldDatatype::Uint32, 1));
            }
            descriptors.extend(fields());
            descriptors.push(field("unused", 16, FieldDatatype::Float64, 0));
            let duplicate_input = with_fields(&input, descriptors);
            for keep_outside in [false, true] {
                let expected = filter(keep_outside).filter(&input).unwrap();
                let actual = filter(keep_outside).filter(&duplicate_input).unwrap();
                assert_eq!(actual.point_cloud.data(), expected.point_cloud.data());
                assert_eq!(actual.point_cloud.fields(), duplicate_input.fields());
                assert_eq!(actual.skipped_nan_count, expected.skipped_nan_count);
            }
        }
    }

    #[test]
    fn filter_errors_preserve_field_and_cloud_error_sources() {
        let field_error = PointFieldError::FieldNotFound("x");
        assert_eq!(
            CropBoxFilterError::from(field_error),
            CropBoxFilterError::PointField(field_error)
        );
        let field_bounds_error = PointFieldError::ValueOutOfBounds {
            name: "x",
            index: 0,
            count: 0,
        };
        let error = CropBoxFilterError::from(field_bounds_error);
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

        let cloud_error = PointCloudError::UnsupportedEndianness;
        let error = CropBoxFilterError::from(cloud_error.clone());
        assert_eq!(error, CropBoxFilterError::PointCloud(cloud_error));
        assert_eq!(
            core::error::Error::source(&error).unwrap().to_string(),
            "Point cloud endianness is not native"
        );
    }

    #[test]
    fn typed_coordinate_access_checks_value_bounds() {
        let input = cloud(&INPUT);
        let x = input.get_field::<f32>("x").unwrap();
        assert_eq!(x.try_read(input.point(3).unwrap(), 0).unwrap(), INPUT[3][0]);
        assert_eq!(
            x.try_read(input.point(0).unwrap(), 1),
            Err(PointFieldError::ValueOutOfBounds {
                name: "x",
                index: 1,
                count: 1,
            })
        );
        assert_eq!(
            input.get_field::<u32>("x").unwrap_err(),
            PointFieldError::FieldNotFound("x")
        );
    }

    #[test]
    fn reads_first_coordinate_value_and_preserves_remaining_values() {
        let coordinate_fields = ["x", "y", "z"]
            .into_iter()
            .zip([0, 8, 16])
            .map(|(name, offset)| field(name, offset, FieldDatatype::Float32, 2))
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
        let z = input.get_field::<f32>("z").unwrap();
        assert_eq!(
            z.iter(input.point(0).unwrap()).unwrap().collect::<Vec<_>>(),
            vec![-0.5, 42.0]
        );
        assert_eq!(result.point_cloud.point_count(), 1);
        assert_eq!(result.skipped_nan_count, 0);
        assert_eq!(result.point_cloud.data(), input.data());
    }

    #[test]
    fn transforms_unaligned_coordinates_preserving_extra_values_and_point_padding() {
        let mut input_fields: Vec<_> = ["x", "y", "z"]
            .into_iter()
            .zip([1, 9, 17])
            .map(|(name, offset)| field(name, offset, FieldDatatype::Float32, 2))
            .collect();
        // All metadata must fit the constructor-validated layout.
        input_fields.push(field("unused", 25, FieldDatatype::Uint8, 3));
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
        assert_eq!(result.point_cloud.data(), expected);
        assert_eq!(result.point_cloud.fields(), input.fields());
        assert_eq!(result.point_cloud.header().frame_id, "map");
        assert_eq!(
            (result.point_cloud.width(), result.point_cloud.row_step()),
            (2, 56)
        );
        assert_eq!(
            result.point_cloud.is_bigendian(),
            cfg!(target_endian = "big")
        );
        assert_eq!(result.skipped_nan_count, 0);
    }
}
