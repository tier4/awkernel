use crate::{Header, Quaternion, UnitQuaternion, Vector3};
use alloc::{format, string::String};
use nalgebra::Vector4;

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Error {
    DenormalizedQuaternion,
    NonFinite,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::DenormalizedQuaternion => write!(f, "Denormalized quaternion"),
            Error::NonFinite => write!(f, "Non-finite translation or quaternion"),
        }
    }
}

impl core::error::Error for Error {}

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Clone, Debug)]
pub struct Transform {
    translation: Vector3<f64>,
    rotation: UnitQuaternion<f64>,
}

impl Transform {
    /// Creates a new `Transform` with the given translation and rotation.
    #[inline]
    pub const fn new(translation: Vector3<f64>, rotation: UnitQuaternion<f64>) -> Self {
        Self {
            translation,
            rotation,
        }
    }

    /// Tries to create a new `Transform` with the given translation and rotation.
    ///
    /// Rejects non-finite translation or rotation components and quaternions whose squared norm differs
    /// from one by at least 0.01. Accepted near-unit quaternions are normalized to preserve invariants.
    ///
    /// # Note
    ///
    /// Nalgebra's `Quaternion::new` takes `(w, i, j, k)`, not ROS's `(x, y, z, w)`.
    /// For ROS-order components, construct `Quaternion::new(w, x, y, z)` explicitly.
    #[inline]
    pub fn try_new(translation: Vector3<f64>, rotation: Quaternion<f64>) -> Result<Self> {
        if translation
            .iter()
            .chain(rotation.coords.iter())
            .any(|value| !value.is_finite())
        {
            return Err(Error::NonFinite);
        }
        let norm_squared = rotation.norm_squared();
        if !norm_squared.is_finite() || (norm_squared - 1.0).abs() >= 0.01 {
            return Err(Error::DenormalizedQuaternion);
        }
        Ok(Self::new(
            translation,
            UnitQuaternion::from_quaternion(rotation),
        ))
    }

    /// Legacy ROS2-porting helper for quaternion `[x, y, z, w]` components.
    ///
    /// This compatibility helper may be removed in the future. Prefer [`Self::try_new`]
    /// with an explicitly constructed `Quaternion::new(w, x, y, z)`.
    /// Uses the same finite-input and near-unit rotation checks as [`Self::try_new`].
    #[deprecated(
        note = "Legacy helper for porting from ROS2; may be removed in the future. Prefer Transform::try_new with Quaternion::new(w, x, y, z)."
    )]
    #[inline]
    pub fn try_from_ros_xyzw(translation: Vector3<f64>, rotation: [f64; 4]) -> Result<Self> {
        let [x, y, z, w] = rotation;
        Self::try_new(
            translation,
            Quaternion::from_vector(Vector4::new(x, y, z, w)),
        )
    }

    /// Returns the identity transform (no translation, no rotation).
    #[inline]
    pub fn identity() -> Self {
        Self::new(Vector3::new(0.0, 0.0, 0.0), UnitQuaternion::identity())
    }

    /// Applies the transform to the given vector.
    #[inline]
    pub fn apply(&self, vec: &Vector3<f64>) -> Vector3<f64> {
        self.rotation * vec + self.translation
    }

    #[inline]
    pub fn rotate(&self, vec: &Vector3<f64>) -> Vector3<f64> {
        self.rotation * vec
    }

    #[inline]
    pub fn translate(&self, vec: &Vector3<f64>) -> Vector3<f64> {
        vec + self.translation
    }
}

impl Default for Transform {
    fn default() -> Self {
        Self::identity()
    }
}

#[derive(Clone, Debug)]
pub struct TransformStamped {
    pub header: Header,
    pub child_frame_id: &'static str,
    pub transform: Transform,
}

impl TransformStamped {
    #[inline]
    pub const fn new(header: Header, child_frame_id: &'static str, transform: Transform) -> Self {
        Self {
            header,
            child_frame_id,
            transform,
        }
    }
}

impl core::ops::Deref for TransformStamped {
    type Target = Transform;

    fn deref(&self) -> &Self::Target {
        &self.transform
    }
}

pub trait TransformListener {
    fn get_latest_transform(&self, from_frame: &str, to_frame: &str) -> Option<Transform>;
    fn get_transform_at_time(
        &self,
        from_frame: &str,
        to_frame: &str,
        timestamp: u64,
    ) -> Option<Transform>;
}

pub struct MockTransformListener {
    transforms: alloc::collections::BTreeMap<String, Transform>,
}

impl MockTransformListener {
    pub fn new() -> Self {
        Self {
            transforms: alloc::collections::BTreeMap::new(),
        }
    }

    pub fn add_transform(&mut self, from_frame: &str, to_frame: &str, transform: Transform) {
        let key = format!("{}_to_{}", from_frame, to_frame);
        self.transforms.insert(key, transform);
    }
}

impl Default for MockTransformListener {
    fn default() -> Self {
        Self::new()
    }
}

impl TransformListener for MockTransformListener {
    fn get_latest_transform(&self, from_frame: &str, to_frame: &str) -> Option<Transform> {
        let key = format!("{}_to_{}", from_frame, to_frame);
        self.transforms.get(&key).cloned()
    }

    fn get_transform_at_time(
        &self,
        from_frame: &str,
        to_frame: &str,
        _timestamp: u64,
    ) -> Option<Transform> {
        self.get_latest_transform(from_frame, to_frame)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_almost_eq(actual: f64, expected: f64) {
        assert!((actual - expected).abs() < 1e-10);
    }

    #[test]
    fn try_new_rejects_zero_length_quaternion() {
        let result = Transform::try_new(Vector3::zeros(), Quaternion::new(0.0, 0.0, 0.0, 0.0));
        assert!(matches!(result, Err(Error::DenormalizedQuaternion)));
    }

    #[test]
    fn try_new_rejects_non_finite_quaternion_components() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            for rotation in [
                Quaternion::new(value, 0.0, 0.0, 0.0),
                Quaternion::new(1.0, value, 0.0, 0.0),
                Quaternion::new(1.0, 0.0, value, 0.0),
                Quaternion::new(1.0, 0.0, 0.0, value),
            ] {
                let result = Transform::try_new(Vector3::zeros(), rotation);

                assert!(
                    matches!(result, Err(Error::NonFinite)),
                    "expected NonFinite for {rotation:?}"
                );
            }
        }
    }

    #[test]
    fn try_new_rejects_quaternion_with_underflowing_squared_norm() {
        let rotation = Quaternion::new(f64::MIN_POSITIVE, 0.0, 0.0, 0.0);
        let result = Transform::try_new(Vector3::zeros(), rotation);

        assert!(matches!(result, Err(Error::DenormalizedQuaternion)));
    }

    #[test]
    fn try_new_rejects_non_finite_translation_components() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            for translation in [
                Vector3::new(value, 0.0, 0.0),
                Vector3::new(0.0, value, 0.0),
                Vector3::new(0.0, 0.0, value),
            ] {
                // Non-finite inputs take precedence over a denormalized rotation.
                for rotation in [Quaternion::identity(), Quaternion::new(0.0, 0.0, 0.0, 0.0)] {
                    assert!(matches!(
                        Transform::try_new(translation, rotation),
                        Err(Error::NonFinite)
                    ));
                }
            }
        }
    }

    #[test]
    fn try_new_rejects_overflowing_subnormal_and_arbitrary_length_quaternions() {
        for rotation in [
            Quaternion::new(1e155, 0.0, 0.0, 1e155),
            Quaternion::new(1e-160, 0.0, 0.0, 1e-160),
            Quaternion::new(2.0, 0.0, 0.0, 2.0),
        ] {
            assert!(matches!(
                Transform::try_new(Vector3::zeros(), rotation),
                Err(Error::DenormalizedQuaternion)
            ));
        }
    }

    #[test]
    fn try_new_enforces_squared_norm_tolerance_on_both_sides() {
        for norm_squared in [0.990001_f64, 1.009999] {
            let rotation = Quaternion::new(norm_squared.sqrt(), 0.0, 0.0, 0.0);
            assert!((rotation.norm_squared() - 1.0).abs() < 0.01);
            let transform = Transform::try_new(Vector3::zeros(), rotation).unwrap();
            assert_almost_eq(transform.rotation.norm(), 1.0);
        }
        for norm_squared in [0.989999_f64, 1.010001] {
            let rotation = Quaternion::new(norm_squared.sqrt(), 0.0, 0.0, 0.0);
            assert!((rotation.norm_squared() - 1.0).abs() >= 0.01);
            assert!(matches!(
                Transform::try_new(Vector3::zeros(), rotation),
                Err(Error::DenormalizedQuaternion)
            ));
        }
    }

    #[test]
    fn try_new_normalizes_valid_quaternion_and_preserves_translation() {
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let component = core::f64::consts::FRAC_1_SQRT_2 * 1.002;
        let rotation = Quaternion::new(component, 0.0, 0.0, component);
        let transform = Transform::try_new(translation, rotation).unwrap();

        assert_eq!(&transform.translation, &translation);
        assert_almost_eq(transform.rotation.norm(), 1.0);

        let rotated = transform.rotate(&Vector3::new(1.0, 0.0, 0.0));
        assert_almost_eq(rotated.x, 0.0);
        assert_almost_eq(rotated.y, 1.0);
        assert_almost_eq(rotated.norm(), 1.0);

        let transformed = transform.apply(&Vector3::new(1.0, 0.0, 0.0));
        assert_almost_eq(transformed.x, 1.0);
        assert_almost_eq(transformed.y, 3.0);
        assert_almost_eq(transformed.z, 3.0);
    }

    #[test]
    fn quaternion_component_order_matches_nalgebra_convention() {
        let half_sqrt_two = core::f64::consts::FRAC_1_SQRT_2;
        let yaw = Transform::try_new(
            Vector3::zeros(),
            Quaternion::new(half_sqrt_two, 0.0, 0.0, half_sqrt_two),
        )
        .unwrap();
        let rotated = yaw.rotate(&Vector3::new(1.0, 0.0, 0.0));

        assert_almost_eq(rotated.x, 0.0);
        assert_almost_eq(rotated.y, 1.0);
        assert_almost_eq(rotated.z, 0.0);

        let roll =
            Transform::try_new(Vector3::zeros(), Quaternion::new(0.0, 1.0, 0.0, 0.0)).unwrap();
        let angular_velocity = Vector3::new(1.0, 2.0, 3.0);
        let rotated = roll.rotate(&angular_velocity);

        assert_almost_eq(rotated.x, angular_velocity.x);
        assert_almost_eq(rotated.y, -angular_velocity.y);
        assert_almost_eq(rotated.z, -angular_velocity.z);
    }

    #[test]
    #[expect(
        deprecated,
        reason = "regression test for the legacy ROS2-porting helper"
    )]
    fn from_ros_xyzw_preserves_identity_and_translation() {
        let transform =
            Transform::try_from_ros_xyzw(Vector3::new(1.0, 2.0, 3.0), [0.0, 0.0, 0.0, 1.0])
                .unwrap();
        let point = Vector3::new(4.0, 5.0, 6.0);
        let rotated = transform.rotate(&point);
        let transformed = transform.apply(&point);

        for (actual, expected) in rotated.iter().zip(point.iter()) {
            assert_almost_eq(*actual, *expected);
        }
        for (actual, expected) in transformed.iter().zip([5.0, 7.0, 9.0]) {
            assert_almost_eq(*actual, expected);
        }
    }

    #[test]
    #[expect(
        deprecated,
        reason = "regression test for the legacy ROS2-porting helper"
    )]
    fn from_ros_xyzw_maps_each_rotation_axis_correctly() {
        let c = core::f64::consts::FRAC_1_SQRT_2;
        for (quaternion, input, expected) in [
            ([c, 0.0, 0.0, c], Vector3::y(), Vector3::z()),
            ([0.0, c, 0.0, c], Vector3::z(), Vector3::x()),
            ([0.0, 0.0, c, c], Vector3::x(), Vector3::y()),
        ] {
            let transform = Transform::try_from_ros_xyzw(Vector3::zeros(), quaternion).unwrap();
            let rotated = transform.rotate(&input);
            for (actual, expected) in rotated.iter().zip(expected.iter()) {
                assert_almost_eq(*actual, *expected);
            }
            assert_almost_eq(rotated.norm(), 1.0);
        }
    }

    #[test]
    #[expect(
        deprecated,
        reason = "regression test for the legacy ROS2-porting helper"
    )]
    fn from_ros_xyzw_reuses_input_validation() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            for index in 0..3 {
                let mut translation = [0.0; 3];
                translation[index] = value;
                assert!(matches!(
                    Transform::try_from_ros_xyzw(translation.into(), [0.0, 0.0, 0.0, 1.0]),
                    Err(Error::NonFinite)
                ));
            }
            for index in 0..4 {
                let mut rotation = [0.0, 0.0, 0.0, 1.0];
                rotation[index] = value;
                assert!(matches!(
                    Transform::try_from_ros_xyzw(Vector3::zeros(), rotation),
                    Err(Error::NonFinite)
                ));
            }
        }
        for rotation in [[0.0; 4], [0.0, 0.0, 0.0, 2.0]] {
            assert!(matches!(
                Transform::try_from_ros_xyzw(Vector3::zeros(), rotation),
                Err(Error::DenormalizedQuaternion)
            ));
        }
    }

    #[test]
    fn identity_transform_preserves_vector() {
        let vector = Vector3::new(1.0, -2.0, 3.0);
        let transformed = Transform::identity().apply(&vector);

        assert_almost_eq(transformed.x, vector.x);
        assert_almost_eq(transformed.y, vector.y);
        assert_almost_eq(transformed.z, vector.z);
    }

    #[test]
    fn transform_rotates_then_translates_vector() {
        let half_sqrt_two = core::f64::consts::FRAC_1_SQRT_2;
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let rotation = Quaternion::new(half_sqrt_two, 0.0, 0.0, half_sqrt_two);

        let transform = Transform::try_new(translation, rotation);
        assert!(transform.is_ok());
        let transform = transform.unwrap();

        let transformed = transform.apply(&Vector3::new(1.0, 0.0, 0.0));

        assert_almost_eq(transformed.x, 1.0);
        assert_almost_eq(transformed.y, 3.0);
        assert_almost_eq(transformed.z, 3.0);
    }
}
