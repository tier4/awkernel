pub mod phy_addr;
pub mod virt_addr;

pub trait Addr:
    Sized
    + core::ops::Add<usize>
    + core::ops::Add
    + core::ops::AddAssign<usize>
    + core::ops::AddAssign
    + core::ops::Sub<usize>
    + core::ops::Sub
    + core::ops::SubAssign<usize>
    + core::ops::SubAssign
    + core::ops::Mul<usize>
    + core::ops::Mul
    + core::ops::MulAssign<usize>
    + core::ops::MulAssign
    + core::ops::Div<usize>
    + core::ops::Div
    + core::ops::DivAssign<usize>
    + core::ops::DivAssign
    + core::ops::Not
    + core::ops::BitAnd
    + core::ops::BitAndAssign
    + core::ops::BitOr
    + core::ops::BitOrAssign
    + core::ops::BitXor
    + core::ops::BitXorAssign
    + core::ops::Shl<usize>
    + core::ops::ShlAssign<usize>
    + core::ops::Shr<usize>
    + core::ops::ShrAssign<usize>
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Clone
    + Copy
{
    fn as_usize(&self) -> usize;
    fn from_usize(addr: usize) -> Self;
    fn as_ptr<T>(&self) -> *const T;
    fn as_mut_ptr<T>(&self) -> *mut T;
}
