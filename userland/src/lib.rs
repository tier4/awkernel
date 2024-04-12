#![no_std]

extern crate alloc;

use alloc::borrow::Cow;

pub async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_services::run().await;

    #[cfg(feature = "test_network")]
    test_network::run().await; // test for network

    #[cfg(feature = "test_pubsub")]
    test_pubsub::run().await; // test for pubsub

    #[cfg(feature = "test_rpi_hal")]
    test_rpi_hal::run().await; // test for RPi HAL

    Ok(())
}
