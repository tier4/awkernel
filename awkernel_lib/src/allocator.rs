#[cfg(feature = "std")]
pub use std::alloc::System;

#[cfg(not(feature = "std"))]
pub use super::heap::TALLOC as System;
