//! Rust adaptation of the supplied Autoware crop box filter tests.
//!
//! The original tests can be found [here](https://github.com/autowarefoundation/autoware_core/blob/1.8.0/sensing/autoware_crop_box_filter/test/test_crop_box_filter.cpp).

use common_types::{
    point_cloud::{
        Field, FieldDatatype, PointCloud, PointCloudReader, PointField, PointFieldError,
    },
    transform::{Transform, TransformStamped},
    Header, UnitQuaternion, Vector3,
};
use crop_box_filter::{
    generate_crop_box_polygon, CropBoxFilter, CropBoxFilterConfig, CropBoxFilterError, CropBoxParam,
};

/// Helper function to create XYZ point fields for a point cloud.
fn xyz_fields() -> Vec<PointField> {
    vec![
        PointField::new("x", 0, FieldDatatype::Float32, 1),
        PointField::new("y", 4, FieldDatatype::Float32, 1),
        PointField::new("z", 8, FieldDatatype::Float32, 1),
    ]
}

/// Helper function to create a point cloud with the specified fields and point step.
fn make_cloud(fields: Vec<PointField>, point_step: u32) -> PointCloud {
    PointCloud {
        header: Header {
            frame_id: "base_link",
            timestamp: 0,
        },
        width: 1,
        height: 1,
        fields,
        is_bigendian: cfg!(target_endian = "big"),
        point_step,
        row_step: point_step,
        data: vec![0; usize::try_from(point_step).unwrap()],
        is_dense: false,
    }
}

/// Helper function to create a point cloud from an array of XYZ points.
fn cloud_from_points(points: &[[f32; 3]]) -> PointCloud {
    let mut cloud = make_cloud(xyz_fields(), 16);
    cloud.width = u32::try_from(points.len()).unwrap();
    cloud.row_step = cloud.width * cloud.point_step;
    cloud.data.clear();
    for point in points {
        for value in point {
            cloud.data.extend_from_slice(&value.to_ne_bytes());
        }
        cloud.data.extend_from_slice(&[0; 4]); // add padding for 16-byte point step
    }
    cloud
}

/// Helper function to extract XYZ points from a point cloud.
fn extract_points(cloud: &PointCloud) -> Vec<[f32; 3]> {
    let reader = PointCloudReader::try_new_typed(
        cloud,
        (
            Field::<f32>::new("x"),
            Field::<f32>::new("y"),
            Field::<f32>::new("z"),
        ),
    )
    .unwrap();
    (0..reader.point_count())
        .map(|index| {
            let point = reader.point(index).unwrap();
            let (x, y, z) = point.fields();
            [
                x.value(0).unwrap(),
                y.value(0).unwrap(),
                z.value(0).unwrap(),
            ]
        })
        .collect()
}

/// Helper function to assert that two sets of XYZ points are the same, ignoring order.
fn assert_same_points(actual: &[[f32; 3]], expected: &[[f32; 3]]) {
    let mut actual = actual.to_vec();
    let mut expected = expected.to_vec();
    let compare = |a: &[f32; 3], b: &[f32; 3]| {
        a.iter()
            .zip(b)
            .map(|(a, b)| a.total_cmp(b))
            .find(|ordering| !ordering.is_eq())
            .unwrap_or(core::cmp::Ordering::Equal)
    };
    actual.sort_by(compare);
    expected.sort_by(compare);
    assert_eq!(actual, expected);
}

/// Helper function to create a crop box filter configuration.
fn config(bound: f32, keep_outside_box: bool) -> CropBoxFilterConfig {
    CropBoxFilterConfig {
        param: CropBoxParam::try_new(-bound, bound, -bound, bound, -bound, bound).unwrap(),
        keep_outside_box,
        preprocess_transform: None,
        postprocess_transform: None,
    }
}

/// Helper function to create a translation transform.
fn translation(frame: &'static str, x: f64, y: f64, z: f64) -> TransformStamped {
    TransformStamped::new(
        Header {
            frame_id: frame,
            timestamp: 0,
        },
        "base_link",
        Transform::new(Vector3::new(x, y, z), UnitQuaternion::identity()),
    )
}

const INPUT: [[f32; 3]; 15] = [
    // Points inside the crop box (within the bound of 5.0)
    [0.5, 0.5, 0.1],
    [1.5, 1.5, 1.1],
    [2.5, 2.5, 2.1],
    [3.5, 3.5, 3.1],
    [4.5, 4.5, 4.1],
    // Points outside the crop box (beyond the bound of 5.0)
    [5.5, 5.5, 5.1],
    [6.5, 6.5, 6.1],
    [7.5, 7.5, 7.1],
    [8.5, 8.5, 8.1],
    [9.5, 9.5, 9.1],
    [-5.5, -5.5, -5.1],
    [-6.5, -6.5, -6.1],
    [-7.5, -7.5, -7.1],
    [-8.5, -8.5, -8.1],
    [-9.5, -9.5, -9.1],
];

#[test]
fn validate_accepts_xyz_only() {
    let cloud = make_cloud(xyz_fields(), 12);
    assert!(CropBoxFilter::new(config(5.0, false))
        .filter(&cloud)
        .is_ok());
}

#[test]
fn validate_accepts_xyzirc() {
    let mut fields = xyz_fields();
    fields.extend([
        PointField::new("intensity", 12, FieldDatatype::Uint8, 1),
        PointField::new("return_type", 13, FieldDatatype::Uint8, 1),
        PointField::new("channel", 14, FieldDatatype::Uint16, 1),
    ]);
    let cloud = make_cloud(fields, 16);
    assert!(CropBoxFilter::new(config(5.0, false))
        .filter(&cloud)
        .is_ok());
}

#[test]
fn validate_rejects_missing_z() {
    let mut fields = xyz_fields();
    fields.pop();
    let cloud = make_cloud(fields, 8);
    assert_eq!(
        CropBoxFilter::new(config(5.0, false)).filter(&cloud).err(),
        Some(CropBoxFilterError::PointField(
            PointFieldError::FieldNotFound("z")
        ))
    );
}

#[test]
fn filter_zero_points_returns_zero_points() {
    let result = CropBoxFilter::new(config(5.0, true))
        .filter(&cloud_from_points(&[]))
        .unwrap();
    assert!(extract_points(&result.point_cloud).is_empty());
}

#[test]
fn filter_excludes_inside_points_when_keeping_outside() {
    let result = CropBoxFilter::new(config(5.0, true))
        .filter(&cloud_from_points(&INPUT))
        .unwrap();
    assert_same_points(&extract_points(&result.point_cloud), &INPUT[5..]);
}

#[test]
fn filter_excludes_outside_points_when_keeping_inside() {
    let result = CropBoxFilter::new(config(5.0, false))
        .filter(&cloud_from_points(&INPUT))
        .unwrap();
    assert_same_points(&extract_points(&result.point_cloud), &INPUT[..5]);
}

#[test]
fn preprocess_transform_shifts_before_cropping() {
    let mut config = config(1.0, false);
    config.preprocess_transform = Some(translation("map", 5.0, 0.0, 0.0));
    let cloud = cloud_from_points(&[[-4.5, 0.5, 0.5], [0.5, 0.0, 0.0]]);
    let result = CropBoxFilter::new(config).filter(&cloud).unwrap();
    assert_same_points(&extract_points(&result.point_cloud), &[[0.5, 0.5, 0.5]]);
    assert_eq!(result.point_cloud.header.frame_id, "map");
}

#[test]
fn postprocess_transform_shifts_after_cropping() {
    let mut config = config(1.0, false);
    config.postprocess_transform = Some(translation("output_frame", 10.0, 10.0, 10.0));
    let cloud = cloud_from_points(&[[0.5, 0.5, 0.5], [5.0, 5.0, 5.0]]);
    let result = CropBoxFilter::new(config).filter(&cloud).unwrap();
    assert_same_points(&extract_points(&result.point_cloud), &[[10.5, 10.5, 10.5]]);
    assert_eq!(result.point_cloud.header.frame_id, "output_frame");
}

#[test]
fn preprocess_and_postprocess_transforms_combine() {
    let mut config = config(1.0, false);
    config.preprocess_transform = Some(translation("intermediate", 5.0, 0.0, 0.0));
    config.postprocess_transform = Some(translation("output_frame", 0.0, 10.0, 0.0));
    let cloud = cloud_from_points(&[[-4.5, 0.5, 0.5], [0.5, 0.5, 0.5]]);
    let result = CropBoxFilter::new(config).filter(&cloud).unwrap();
    assert_same_points(&extract_points(&result.point_cloud), &[[0.5, 10.5, 0.5]]);
    assert_eq!(result.point_cloud.header.frame_id, "output_frame");
}

#[test]
fn polygon_sets_frame_stamp_and_point_count() {
    let param = CropBoxParam::try_new(-5.0, 5.0, -5.0, 5.0, -5.0, 5.0).unwrap();
    let timestamp = 123_000_000_456;
    let polygon = generate_crop_box_polygon(&param, "base_link", timestamp);
    assert_eq!(polygon.header.frame_id, "base_link");
    assert_eq!(polygon.header.timestamp, timestamp);
    assert_eq!(polygon.polygon.points.len(), 16);
}
