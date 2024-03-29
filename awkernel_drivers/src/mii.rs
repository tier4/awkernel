//! Media-independent interface (MII) driver.

pub fn attach() {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiError {
    Read,
    Write,
}

pub trait Mii {
    /// Read a register from the PHY.
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError>;

    /// Write a register to the PHY.
    fn write_reg(&mut self, phy: u32, reg: u32, data: u32) -> Result<(), MiiError>;
}
