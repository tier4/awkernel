pub mod phy_addr;
pub mod virt_addr;

pub trait Addr:
    Sized
    + core::ops::Add
    + core::ops::AddAssign
    + core::ops::Sub
    + core::ops::SubAssign
    + core::ops::Mul
    + core::ops::MulAssign
    + core::ops::Div
    + core::ops::DivAssign
    + core::ops::Not
    + core::ops::BitAnd
    + core::ops::BitAndAssign
    + core::ops::BitOr
    + core::ops::BitOrAssign
    + core::ops::BitXor
    + core::ops::BitXorAssign
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Clone
    + Copy
{
    fn to_usize(&self) -> usize;
    fn from_usize(addr: usize) -> Self;
}
