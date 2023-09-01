use core::ops::AddAssign;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhyAddr(usize);

impl core::ops::Add for PhyAddr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 + rhs.0)
    }
}

impl AddAssign for PhyAddr {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl core::ops::Mul for PhyAddr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 * rhs.0)
    }
}

impl core::ops::MulAssign for PhyAddr {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl core::ops::Sub for PhyAddr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 - rhs.0)
    }
}

impl core::ops::SubAssign for PhyAddr {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0
    }
}

impl core::ops::Div for PhyAddr {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        PhyAddr(self.0 / rhs.0)
    }
}

impl core::ops::DivAssign for PhyAddr {
    fn div_assign(&mut self, rhs: Self) {
        self.0 /= rhs.0
    }
}

impl super::Addr for PhyAddr {
    fn to_usize(&self) -> usize {
        self.0
    }

    fn from_usize(addr: usize) -> Self {
        PhyAddr(addr)
    }
}

impl PhyAddr {
    pub fn new(addr: usize) -> Self {
        PhyAddr(addr)
    }
}
