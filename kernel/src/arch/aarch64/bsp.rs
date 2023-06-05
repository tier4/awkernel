pub mod config;
pub mod memory;

#[cfg(feature = "raspi")]
pub mod raspi;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}
