pub mod config;
pub mod memory;

#[cfg(feature = "raspi")]
pub mod raspi;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}

pub unsafe fn init_device() {
    #[cfg(feature = "raspi")]
    raspi::init_device();
}
