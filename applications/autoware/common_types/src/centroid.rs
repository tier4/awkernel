use nalgebra::{RealField, SVector};

/// Errors that can occur when working with centroids.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CentroidError {
    NonFinite,
    CountOverflow,
    CountConv,
}

impl core::fmt::Display for CentroidError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NonFinite => write!(f, "Centroid contains a non-finite component"),
            Self::CountOverflow => write!(f, "Centroid point count overflows u32"),
            Self::CountConv => write!(f, "Centroid point count conversion failed"),
        }
    }
}

impl core::error::Error for CentroidError {}

pub type Result<T> = core::result::Result<T, CentroidError>;

/// An allocation-free accumulator for N-dimensional points.
///
/// [`Self::try_new`] starts with one point; [`Self::default`] starts empty.
/// Add at least one point before calculating the mean of a default accumulator.
/// Components are accumulated sequentially in the selected scalar type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Centroid<T: RealField + Copy, const N: usize> {
    sum: SVector<T, N>,
    count: u32,
}

/// A centroid accumulated in single precision.
pub type CentroidF32<const N: usize> = Centroid<f32, N>;

/// A centroid accumulated in double precision.
pub type CentroidF64<const N: usize> = Centroid<f64, N>;

impl<T: RealField + Copy, const N: usize> Centroid<T, N> {
    /// Starts an accumulator with one point, rejecting non-finite components.
    #[inline]
    pub fn try_new(point: SVector<T, N>) -> Result<Self> {
        if point.iter().any(|value| !value.is_finite()) {
            return Err(CentroidError::NonFinite);
        }
        Ok(Self {
            sum: point,
            count: 1,
        })
    }

    /// Adds a point. Any error leaves the accumulator unchanged.
    ///
    /// # Errors
    ///
    /// - `CentroidError::NonFinite` if any component of the accumulated point would not be finite.
    /// - `CentroidError::CountOverflow` if the point count would overflow.
    pub fn try_add_point(&mut self, point: SVector<T, N>) -> Result<()> {
        let new_count = self
            .count
            .checked_add(1)
            .ok_or(CentroidError::CountOverflow)?;
        let new_sum = self.sum + point;
        if new_sum.iter().any(|value| !value.is_finite()) {
            return Err(CentroidError::NonFinite);
        }

        self.sum = new_sum;
        self.count = new_count;
        Ok(())
    }

    /// Returns the component-wise arithmetic mean.
    ///
    /// # Errors
    ///
    /// - `CentroidError::CountConv` if the point count cannot be converted to the scalar type.
    #[inline]
    pub fn try_calc_centroid(&self) -> Result<SVector<T, N>> {
        let count = T::from_u32(self.count).ok_or(CentroidError::CountConv)?;
        Ok(self.sum / count)
    }
}

impl<T: RealField + Copy, const N: usize> Default for Centroid<T, N> {
    #[inline]
    fn default() -> Self {
        Self {
            sum: SVector::<T, N>::zeros(),
            count: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_close<const N: usize>(actual: SVector<f32, N>, expected: SVector<f32, N>) {
        for (actual, expected) in actual.iter().zip(expected.iter()) {
            assert!((actual - expected).abs() <= f32::EPSILON);
        }
    }

    #[test]
    fn default_accumulator_does_not_count_an_implicit_zero_point() {
        let mut centroid = CentroidF32::<3>::default();
        assert_eq!(centroid.count, 0);
        assert_eq!(centroid.sum, SVector::<f32, 3>::zeros());

        let first = SVector::<f32, 3>::new(-4.0, 2.0, 8.0);
        centroid.try_add_point(first).unwrap();
        assert_close(centroid.try_calc_centroid().unwrap(), first);

        centroid
            .try_add_point(SVector::<f32, 3>::new(2.0, 4.0, -2.0))
            .unwrap();
        assert_close(
            centroid.try_calc_centroid().unwrap(),
            SVector::<f32, 3>::new(-1.0, 3.0, 3.0),
        );
    }

    #[test]
    fn single_point_is_its_own_centroid() {
        let point = SVector::<f32, 3>::new(-3.0, 0.0, 7.5);
        let centroid = CentroidF32::<3>::try_new(point).unwrap();
        assert_close(centroid.try_calc_centroid().unwrap(), point);
    }

    #[test]
    fn averages_two_dimensional_points() {
        let mut centroid = Centroid::try_new(SVector::<f32, 2>::new(-4.0, 2.0)).unwrap();
        centroid
            .try_add_point(SVector::<f32, 2>::new(2.0, 4.0))
            .unwrap();
        centroid
            .try_add_point(SVector::<f32, 2>::new(-1.0, 9.0))
            .unwrap();
        assert_close(
            centroid.try_calc_centroid().unwrap(),
            SVector::<f32, 2>::new(-1.0, 5.0),
        );
    }

    #[test]
    fn averages_four_components_including_fractional_intensity() {
        let mut centroid = Centroid::try_new(SVector::<f32, 4>::new(-2.0, 4.0, 8.0, 10.0)).unwrap();
        centroid
            .try_add_point(SVector::<f32, 4>::new(4.0, -2.0, 2.0, 11.0))
            .unwrap();
        assert_close(
            centroid.try_calc_centroid().unwrap(),
            SVector::<f32, 4>::new(1.0, 1.0, 5.0, 10.5),
        );
    }

    #[test]
    fn rejects_non_finite_first_point() {
        for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
            assert!(matches!(
                Centroid::try_new(SVector::<f32, 2>::new(1.0, value)),
                Err(CentroidError::NonFinite)
            ));
        }
    }

    #[test]
    fn invalid_addition_leaves_state_unchanged() {
        let mut centroid = Centroid::try_new(SVector::<f32, 2>::new(1.0, 2.0)).unwrap();
        let before = centroid;
        for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
            assert_eq!(
                centroid.try_add_point(SVector::<f32, 2>::new(3.0, value)),
                Err(CentroidError::NonFinite)
            );
            assert_eq!(centroid.sum, before.sum);
            assert_eq!(centroid.count, before.count);
        }
        centroid
            .try_add_point(SVector::<f32, 2>::new(3.0, 4.0))
            .unwrap();
        assert_close(
            centroid.try_calc_centroid().unwrap(),
            SVector::<f32, 2>::new(2.0, 3.0),
        );
    }

    #[test]
    fn sum_overflow_leaves_state_unchanged() {
        let mut centroid = Centroid::try_new(SVector::<f32, 2>::new(1.0, f32::MAX)).unwrap();
        let before = centroid;
        assert_eq!(
            centroid.try_add_point(SVector::<f32, 2>::new(2.0, f32::MAX)),
            Err(CentroidError::NonFinite)
        );
        assert_eq!(centroid.sum, before.sum);
        assert_eq!(centroid.count, before.count);
    }

    #[test]
    fn count_overflow_leaves_state_unchanged() {
        let mut centroid = Centroid {
            sum: SVector::<f32, 2>::new(1.0, 2.0),
            count: u32::MAX,
        };
        let before = centroid;
        assert_eq!(
            centroid.try_add_point(SVector::<f32, 2>::new(3.0, 4.0)),
            Err(CentroidError::CountOverflow)
        );
        assert_eq!(centroid.sum, before.sum);
        assert_eq!(centroid.count, before.count);
    }

    #[test]
    fn double_precision_mean_preserves_values_not_representable_in_single_precision() {
        let mut centroid =
            CentroidF64::<2>::try_new(SVector::<f64, 2>::new(16_777_217.0, -4.0)).unwrap();
        centroid
            .try_add_point(SVector::<f64, 2>::new(16_777_219.0, 1.0))
            .unwrap();
        let expected = SVector::<f64, 2>::new(16_777_218.0, -1.5);
        for (actual, expected) in centroid
            .try_calc_centroid()
            .unwrap()
            .iter()
            .zip(expected.iter())
        {
            assert!((actual - expected).abs() <= f64::EPSILON);
        }
    }

    #[test]
    fn double_precision_rejects_non_finite_input_without_mutation() {
        let mut centroid = CentroidF64::<2>::try_new(SVector::<f64, 2>::new(1.0, 2.0)).unwrap();
        let before = centroid;
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(matches!(
                CentroidF64::<2>::try_new(SVector::<f64, 2>::new(1.0, value)),
                Err(CentroidError::NonFinite)
            ));
            assert_eq!(
                centroid.try_add_point(SVector::<f64, 2>::new(3.0, value)),
                Err(CentroidError::NonFinite)
            );
            assert_eq!(centroid.sum, before.sum);
            assert_eq!(centroid.count, before.count);
        }
    }

    #[test]
    fn double_precision_sum_overflow_leaves_state_unchanged() {
        let mut centroid =
            CentroidF64::<2>::try_new(SVector::<f64, 2>::new(1.0, f64::MAX)).unwrap();
        let before = centroid;
        assert_eq!(
            centroid.try_add_point(SVector::<f64, 2>::new(2.0, f64::MAX)),
            Err(CentroidError::NonFinite)
        );
        assert_eq!(centroid.sum, before.sum);
        assert_eq!(centroid.count, before.count);
    }

    #[test]
    fn double_precision_count_conversion_preserves_all_u32_bits() {
        let centroid = Centroid::<f64, 1> {
            sum: SVector::<f64, 1>::new(f64::from(u32::MAX)),
            count: u32::MAX,
        };
        let mean = centroid.try_calc_centroid().unwrap();
        assert!((mean.x - 1.0).abs() <= f64::EPSILON);
    }
}
