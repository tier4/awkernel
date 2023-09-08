use core::ops::AddAssign;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtAddr(usize);

impl core::ops::Add for VirtAddr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 + rhs.0)
    }
}

impl AddAssign for VirtAddr {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl core::ops::Mul for VirtAddr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 * rhs.0)
    }
}

impl core::ops::MulAssign for VirtAddr {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl core::ops::Sub for VirtAddr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 - rhs.0)
    }
}

impl core::ops::SubAssign for VirtAddr {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0
    }
}

impl core::ops::Div for VirtAddr {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 / rhs.0)
    }
}

impl core::ops::DivAssign for VirtAddr {
    fn div_assign(&mut self, rhs: Self) {
        self.0 /= rhs.0
    }
}

impl core::ops::Not for VirtAddr {
    type Output = Self;

    fn not(self) -> Self::Output {
        VirtAddr::new(!self.0)
    }
}

impl core::ops::BitAnd for VirtAddr {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 & rhs.0)
    }
}

impl core::ops::BitAndAssign for VirtAddr {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 = self.0 & rhs.0;
    }
}

impl core::ops::BitOr for VirtAddr {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 | rhs.0)
    }
}

impl core::ops::BitOrAssign for VirtAddr {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 = self.0 | rhs.0;
    }
}

impl core::ops::BitXor for VirtAddr {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        VirtAddr(self.0 ^ rhs.0)
    }
}

impl core::ops::BitXorAssign for VirtAddr {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 = self.0 ^ rhs.0;
    }
}

impl super::Addr for VirtAddr {
    fn to_usize(&self) -> usize {
        self.0
    }

    fn from_usize(addr: usize) -> Self {
        VirtAddr(addr)
    }
}

impl VirtAddr {
    pub const fn new(addr: usize) -> Self {
        VirtAddr(addr)
    }
}
