use crate::{Quaternion, UnitQuaternion, Vector3};
use alloc::{format, string::String};

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Error {
    ZeroLengthQuaternion,
    NonFiniteQuaternion,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::ZeroLengthQuaternion => write!(f, "Zero length quaternion"),
            Error::NonFiniteQuaternion => write!(f, "Non-finite quaternion"),
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
    /// Returns an error if the rotation quaternion is zero-length or contains non-finite values.
    #[inline]
    pub fn try_new(translation: Vector3<f64>, rotation: Quaternion<f64>) -> Result<Self> {
        if rotation.coords.iter().any(|value| !value.is_finite()) {
            Err(Error::NonFiniteQuaternion)
        } else if rotation.norm_squared() == 0.0 {
            Err(Error::ZeroLengthQuaternion)
        } else {
            Ok(Self::new(
                translation,
                UnitQuaternion::from_quaternion(rotation),
            ))
        }
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

        assert!(matches!(result, Err(Error::ZeroLengthQuaternion)));
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
                    matches!(result, Err(Error::NonFiniteQuaternion)),
                    "expected NonFiniteQuaternion for {rotation:?}"
                );
            }
        }
    }

    #[test]
    fn try_new_rejects_quaternion_with_underflowing_squared_norm() {
        let rotation = Quaternion::new(f64::MIN_POSITIVE, 0.0, 0.0, 0.0);
        let result = Transform::try_new(Vector3::zeros(), rotation);

        assert!(matches!(result, Err(Error::ZeroLengthQuaternion)));
    }

    #[test]
    fn try_new_normalizes_valid_quaternion_and_preserves_translation() {
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let rotation = Quaternion::new(2.0, 0.0, 0.0, 2.0);
        let transform = Transform::try_new(translation, rotation).unwrap();

        assert_eq!(&transform.translation, &translation);
        assert_almost_eq(transform.rotation.norm(), 1.0);

        let transformed = transform.apply(&Vector3::new(1.0, 0.0, 0.0));
        assert_almost_eq(transformed.x, 1.0);
        assert_almost_eq(transformed.y, 3.0);
        assert_almost_eq(transformed.z, 3.0);
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
