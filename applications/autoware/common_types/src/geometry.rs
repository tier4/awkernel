pub use crate::{Header, Vector3};
use alloc::vec::Vec;

/// Represents a 3D point with 32-bit floating point coordinates.
pub type Point32 = Vector3<f32>;

/// Represents a polygon defined by a sequence of 3D points.
///
/// The first and last points are assumed to be connected.
#[repr(transparent)]
#[derive(Debug, Clone)]
pub struct Polygon {
    /// Sequence of 3D points defining the polygon.
    pub points: Vec<Point32>,
}

impl Polygon {
    #[inline]
    pub const fn into_stamped(self, header: Header) -> PolygonStamped {
        PolygonStamped {
            header,
            polygon: self,
        }
    }
}

/// A polygon with a reference coordinate frame and timestamp.
#[derive(Debug, Clone)]
pub struct PolygonStamped {
    pub header: Header,
    pub polygon: Polygon,
}

impl From<PolygonStamped> for Polygon {
    fn from(stamped: PolygonStamped) -> Self {
        stamped.polygon
    }
}

impl core::ops::Deref for PolygonStamped {
    type Target = Polygon;

    fn deref(&self) -> &Self::Target {
        &self.polygon
    }
}

impl core::ops::DerefMut for PolygonStamped {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.polygon
    }
}
