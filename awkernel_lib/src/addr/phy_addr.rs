#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhyAddr(usize);

impl core::ops::Add<usize> for PhyAddr {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 + rhs)
    }
}

impl core::ops::Add for PhyAddr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 + rhs.0)
    }
}

impl core::ops::AddAssign<usize> for PhyAddr {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl core::ops::AddAssign for PhyAddr {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl core::ops::Mul<usize> for PhyAddr {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 * rhs)
    }
}

impl core::ops::Mul for PhyAddr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 * rhs.0)
    }
}

impl core::ops::MulAssign<usize> for PhyAddr {
    fn mul_assign(&mut self, rhs: usize) {
        self.0 *= rhs;
    }
}

impl core::ops::MulAssign for PhyAddr {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl core::ops::Sub<usize> for PhyAddr {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 - rhs)
    }
}

impl core::ops::Sub for PhyAddr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 - rhs.0)
    }
}

impl core::ops::SubAssign<usize> for PhyAddr {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 -= rhs
    }
}

impl core::ops::SubAssign for PhyAddr {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0
    }
}

impl core::ops::Div<usize> for PhyAddr {
    type Output = Self;

    fn div(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 / rhs)
    }
}

impl core::ops::Div for PhyAddr {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 / rhs.0)
    }
}

impl core::ops::DivAssign<usize> for PhyAddr {
    fn div_assign(&mut self, rhs: usize) {
        self.0 /= rhs
    }
}

impl core::ops::DivAssign for PhyAddr {
    fn div_assign(&mut self, rhs: Self) {
        self.0 /= rhs.0
    }
}

impl core::ops::Not for PhyAddr {
    type Output = Self;

    fn not(self) -> Self::Output {
        PhyAddr(!self.0)
    }
}

impl core::ops::BitAnd for PhyAddr {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 & rhs.0)
    }
}

impl core::ops::BitAndAssign for PhyAddr {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 = self.0 & rhs.0;
    }
}

impl core::ops::BitOr for PhyAddr {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 | rhs.0)
    }
}

impl core::ops::BitOrAssign for PhyAddr {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 = self.0 | rhs.0;
    }
}

impl core::ops::BitXor for PhyAddr {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 ^ rhs.0)
    }
}

impl core::ops::BitXorAssign for PhyAddr {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 = self.0 ^ rhs.0;
    }
}

impl core::ops::Shl<usize> for PhyAddr {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 << rhs)
    }
}

impl core::ops::ShlAssign<usize> for PhyAddr {
    fn shl_assign(&mut self, rhs: usize) {
        self.0 = self.0 << rhs;
    }
}

impl core::ops::Shr<usize> for PhyAddr {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        PhyAddr(self.0 >> rhs)
    }
}

impl core::ops::ShrAssign<usize> for PhyAddr {
    fn shr_assign(&mut self, rhs: usize) {
        self.0 = self.0 >> rhs;
    }
}

impl super::Addr for PhyAddr {
    fn as_usize(&self) -> usize {
        self.0
    }

    fn from_usize(addr: usize) -> Self {
        PhyAddr(addr)
    }

    fn as_ptr<T>(&self) -> *const T {
        self.0 as *const T
    }

    fn as_mut_ptr<T>(&self) -> *mut T {
        self.0 as *mut T
    }
}

impl PhyAddr {
    pub const fn new(addr: usize) -> Self {
        PhyAddr(addr)
    }
}
