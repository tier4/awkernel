#[cfg(feature = "igb")]
pub mod igb; // Intel GbE

#[cfg(feature = "ixgbe")]
pub mod ixgbe; // Intel 10GbE

pub mod e1000e_example;
