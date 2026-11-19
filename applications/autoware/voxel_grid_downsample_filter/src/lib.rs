#![no_std]

extern crate alloc;

use alloc::{collections::BTreeMap, vec};
use common_types::{
    centroid::{CentroidError, CentroidF32},
    point_cloud::{PointCloud, PointCloudError},
    point_field::{PointFieldError, TypedPointField},
    Matrix4, Vector3, Vector4,
};

#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum VoxelGridDownsampleFilterError {
    InvalidVoxelSize(f32, f32, f32),
    MissingOffsets,
    VoxelSizeTooSmall,
    PointField(PointFieldError),
    Centroid(CentroidError),
    PointCloud(PointCloudError),
}

impl core::fmt::Display for VoxelGridDownsampleFilterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidVoxelSize(size_x, size_y, size_z) => {
                write!(f, "Invalid voxel size: ({size_x}, {size_y}, {size_z})")
            }
            Self::MissingOffsets => write!(f, "Missing offsets"),
            Self::VoxelSizeTooSmall => write!(f, "Voxel size too small"),
            Self::PointField(e) => write!(f, "Point field error: {e}"),
            Self::Centroid(e) => write!(f, "Centroid error: {e}"),
            Self::PointCloud(e) => write!(f, "Point cloud error: {e}"),
        }
    }
}

impl core::error::Error for VoxelGridDownsampleFilterError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::PointField(e) => Some(e),
            Self::Centroid(e) => Some(e),
            Self::PointCloud(e) => Some(e),
            _ => None,
        }
    }
}

impl From<PointFieldError> for VoxelGridDownsampleFilterError {
    fn from(e: PointFieldError) -> Self {
        Self::PointField(e)
    }
}

impl From<PointCloudError> for VoxelGridDownsampleFilterError {
    fn from(e: PointCloudError) -> Self {
        Self::PointCloud(e)
    }
}

impl From<CentroidError> for VoxelGridDownsampleFilterError {
    fn from(e: CentroidError) -> Self {
        Self::Centroid(e)
    }
}

pub type Result<T> = core::result::Result<T, VoxelGridDownsampleFilterError>;

/// Offsets for the point fields in the point cloud.
#[derive(Debug, Clone)]
struct Offsets {
    /// Offset for the x field.
    x: TypedPointField<f32>,
    /// Offset for the y field.
    y: TypedPointField<f32>,
    /// Offset for the z field.
    z: TypedPointField<f32>,
    /// Offset for the intensity field, if present.
    intensity: Option<TypedPointField<u8>>,
}

#[derive(Debug, Clone)]
pub struct VoxelGridDownsampleFilter {
    inverse_voxel_size: Vector3<f32>,
    offsets: Option<Offsets>,
}

#[inline]
const fn valid_size(value: f32) -> bool {
    value > 0.0 && value.is_finite()
}

impl VoxelGridDownsampleFilter {
    pub const fn new() -> Self {
        Self {
            inverse_voxel_size: Vector3::new(0.0, 0.0, 0.0),
            offsets: None,
        }
    }

    pub fn set_voxel_size(&mut self, size_x: f32, size_y: f32, size_z: f32) -> Result<()> {
        if !valid_size(size_x) || !valid_size(size_y) || !valid_size(size_z) {
            return Err(VoxelGridDownsampleFilterError::InvalidVoxelSize(
                size_x, size_y, size_z,
            ));
        }
        let div = Vector3::new(1.0, 1.0, 1.0);
        let denom = Vector3::new(size_x, size_y, size_z);
        self.inverse_voxel_size = div.component_div(&denom);
        Ok(())
    }

    pub fn set_field_offsets(&mut self, input: &PointCloud) -> Result<()> {
        self.offsets = Some(Offsets {
            x: input.get_field::<f32>("x")?,
            y: input.get_field::<f32>("y")?,
            z: input.get_field::<f32>("z")?,
            intensity: input.get_field::<u8>("intensity").ok(),
        });
        Ok(())
    }

    pub fn filter(
        &mut self,
        input: &PointCloud,
        transform: Option<&Matrix4<f32>>,
    ) -> Result<PointCloud> {
        // Check if the field offset has been set
        if self.offsets.is_none() {
            self.set_field_offsets(input)?;
        }

        // Compute the voxel coordinates for the input point cloud
        let (min_voxel, max_voxel) = self.get_min_max_voxel(input)?;
        let voxel_centroid_map = self.calc_centroids_each_voxel(input, &max_voxel, &min_voxel)?;

        // Initialize the output point cloud
        let n_points = voxel_centroid_map.len();
        let row_step = n_points * input.point_step();

        let mut output = PointCloud::try_new(
            input.header().clone(),
            1, // height is 1 for unorganized point clouds
            n_points as u32,
            input.fields().to_vec(),
            input.is_bigendian(),
            input.point_step() as u32,
            row_step as u32,
            vec![0; row_step],
            true, // we skip invalid points
        )?;

        // Copy the centroids to the output
        self.copy_centroids_to_output(&voxel_centroid_map, &mut output, transform)?;
        Ok(output)
    }

    fn get_point_values(&self, point: &[u8]) -> Result<Vector4<f32>> {
        match self.offsets {
            None => return Err(VoxelGridDownsampleFilterError::MissingOffsets),
            Some(ref offsets) => {
                let x = offsets.x.try_read(point, 0)?;
                let y = offsets.y.try_read(point, 0)?;
                let z = offsets.z.try_read(point, 0)?;
                let intensity = match offsets.intensity {
                    Some(ref field) => field.try_read(point, 0).map(|v| v as f32).ok(),
                    None => None,
                };
                Ok(Vector4::new(x, y, z, intensity.unwrap_or(0.)))
            }
        }
    }

    fn get_min_max_voxel(&self, input: &PointCloud) -> Result<(Vector3<i32>, Vector3<i32>)> {
        // Compute the minimum and maximum point coordinates
        let mut min_point = Vector3::new(f32::MAX, f32::MAX, f32::MAX);
        let mut max_point = Vector3::new(f32::MIN, f32::MIN, f32::MIN);
        for point in input.iter_points() {
            let coords = self.get_point_values(point)?.xyz();
            if coords.x.is_finite() && coords.y.is_finite() && coords.z.is_finite() {
                min_point = min_point.inf(&coords);
                max_point = max_point.sup(&coords);
            }
        }

        // Check that the voxel size is not too small, given the size of the data
        let voxel_dims = (max_point - min_point)
            .component_mul(&self.inverse_voxel_size)
            .map(|v| libm::roundf(v) as i64 + 1);
        if voxel_dims.product() > i32::MAX as i64 {
            return Err(VoxelGridDownsampleFilterError::VoxelSizeTooSmall);
        }

        // Compute the minimum and maximum voxel coordinates
        let min_voxel = min_point
            .component_mul(&self.inverse_voxel_size)
            .map(|v| libm::floorf(v) as i32);

        let max_voxel = max_point
            .component_mul(&self.inverse_voxel_size)
            .map(|v| libm::floorf(v) as i32);

        Ok((min_voxel, max_voxel))
    }

    fn calc_centroids_each_voxel(
        &self,
        input: &PointCloud,
        max_voxel: &Vector3<i32>,
        min_voxel: &Vector3<i32>,
    ) -> Result<BTreeMap<u32, CentroidF32<4>>> {
        let mut voxel_centroid_map: BTreeMap<u32, CentroidF32<4>> = BTreeMap::new();

        // Compute the number of divisions needed along all axes
        let div_b = max_voxel - min_voxel + Vector3::repeat(1);
        // Set up the division multiplier
        let div_b_mul = Vector3::new(1, div_b.x, div_b.x * div_b.y);

        for point in input.iter_points() {
            let coords = self.get_point_values(point)?;
            let xyz = coords.xyz();

            if xyz.iter().all(|c| c.is_finite()) {
                // Calculate the voxel index to which the point belongs
                let ijk = xyz
                    .component_mul(&self.inverse_voxel_size)
                    .map(|v| libm::floorf(v) as i32)
                    - min_voxel;

                let voxel_id = ijk.dot(&div_b_mul) as u32;

                // Add the point to the corresponding centroid
                if let Some(centroid) = voxel_centroid_map.get_mut(&voxel_id) {
                    centroid.try_add_point(coords)?;
                } else {
                    voxel_centroid_map.insert(voxel_id, CentroidF32::try_new(coords)?);
                }
            }
        }

        Ok(voxel_centroid_map)
    }

    fn copy_centroids_to_output(
        &self,
        voxel_centroid_map: &BTreeMap<u32, CentroidF32<4>>,
        output: &mut PointCloud,
        transform: Option<&Matrix4<f32>>,
    ) -> Result<()> {
        let Offsets { x, y, z, intensity } = self
            .offsets
            .as_ref()
            .ok_or(VoxelGridDownsampleFilterError::MissingOffsets)?;

        for (i, centroid_data) in voxel_centroid_map.values().enumerate() {
            let mut centroid = centroid_data.try_calc_centroid()?;
            if let Some(tf) = transform {
                centroid = tf * centroid;
            }

            let point = output.point_mut(i)?;

            x.try_write(point, 0, centroid.x)?;
            y.try_write(point, 0, centroid.y)?;
            z.try_write(point, 0, centroid.z)?;

            if let Some(intensity) = intensity {
                intensity.try_write(point, 0, centroid.w as u8)?;
            }
        }
        Ok(())
    }
}

impl Default for VoxelGridDownsampleFilter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use common_types::{
        point_field::{FieldDatatype, PointField},
        Header,
    };

    fn make_cloud(points: &[(f32, f32, f32, u8, u16)]) -> PointCloud {
        let fields = vec![
            PointField::try_new("x", 0, FieldDatatype::Float32, 1).unwrap(),
            PointField::try_new("y", 4, FieldDatatype::Float32, 1).unwrap(),
            PointField::try_new("z", 8, FieldDatatype::Float32, 1).unwrap(),
            PointField::try_new("intensity", 12, FieldDatatype::Uint8, 1).unwrap(),
            // Padding byte!
            PointField::try_new("ring", 14, FieldDatatype::Uint16, 1).unwrap(),
        ];
        let point_step = 16;
        let mut data = Vec::with_capacity(points.len() * point_step);

        for &(x, y, z, intensity, ring) in points {
            data.extend_from_slice(&x.to_ne_bytes());
            data.extend_from_slice(&y.to_ne_bytes());
            data.extend_from_slice(&z.to_ne_bytes());
            data.push(intensity);
            data.push(0);
            data.extend_from_slice(&ring.to_ne_bytes());
        }

        PointCloud::try_new(
            Header {
                frame_id: "map",
                timestamp: 0,
            },
            1,
            points.len() as u32,
            fields,
            cfg!(target_endian = "big"),
            point_step as u32,
            (points.len() * point_step) as u32,
            data,
            true,
        )
        .unwrap()
    }

    #[test]
    fn filter_averages_points_per_voxel_and_leaves_other_fields_zeroed() {
        let input = make_cloud(&[
            (0.1, 0.1, 0.1, 10, 9),
            (0.4, 0.2, 0.3, 20, 11),
            (1.2, 0.1, 0.1, 40, 13),
        ]);
        let mut filter = VoxelGridDownsampleFilter::new();
        filter.set_voxel_size(1.0, 1.0, 1.0).unwrap();

        let output = filter.filter(&input, None).unwrap();

        assert_eq!(output.width(), 2);
        assert_eq!(output.height(), 1);
        let x = output.get_field::<f32>("x").unwrap();
        let y = output.get_field::<f32>("y").unwrap();
        let z = output.get_field::<f32>("z").unwrap();
        let intensity = output.get_field::<u8>("intensity").unwrap();
        let ring = output.get_field::<u16>("ring").unwrap();

        let first = output.point(0).unwrap();
        assert!((x.try_read(first, 0).unwrap() - 0.25).abs() <= f32::EPSILON);
        assert!((y.try_read(first, 0).unwrap() - 0.15).abs() <= f32::EPSILON);
        assert!((z.try_read(first, 0).unwrap() - 0.2).abs() <= f32::EPSILON);
        assert_eq!(intensity.try_read(first, 0).unwrap(), 15);
        assert_eq!(ring.try_read(first, 0).unwrap(), 0);

        let second = output.point(1).unwrap();
        assert!((x.try_read(second, 0).unwrap() - 1.2).abs() <= f32::EPSILON);
        assert_eq!(intensity.try_read(second, 0).unwrap(), 40);
        assert_eq!(ring.try_read(second, 0).unwrap(), 0);
    }

    #[test]
    fn filter_skips_points_with_non_finite_coordinates() {
        let input = make_cloud(&[
            (0.2, 0.3, 0.4, 17, 1),
            (f32::NAN, 0.3, 0.4, 99, 2),
            (0.2, f32::INFINITY, 0.4, 88, 3),
        ]);
        let mut filter = VoxelGridDownsampleFilter::new();
        filter.set_voxel_size(1.0, 1.0, 1.0).unwrap();

        let output = filter.filter(&input, None).unwrap();

        assert_eq!(output.width(), 1);
        let x = output.get_field::<f32>("x").unwrap();
        let intensity = output.get_field::<u8>("intensity").unwrap();
        let point = output.point(0).unwrap();
        assert!((x.try_read(point, 0).unwrap() - 0.2).abs() <= f32::EPSILON);
        assert_eq!(intensity.try_read(point, 0).unwrap(), 17);
    }

    #[test]
    fn set_voxel_size_rejects_non_positive_and_non_finite_dimensions() {
        for (size_x, size_y, size_z) in [
            (0.0, 1.0, 1.0),
            (1.0, -1.0, 1.0),
            (1.0, 1.0, f32::NAN),
            (f32::INFINITY, 1.0, 1.0),
        ] {
            let mut filter = VoxelGridDownsampleFilter::new();
            assert!(matches!(
                filter.set_voxel_size(size_x, size_y, size_z),
                Err(VoxelGridDownsampleFilterError::InvalidVoxelSize(..))
            ));
        }
    }
}
