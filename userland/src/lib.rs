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

    #[cfg(feature = "test_graphics")]
    test_graphics::run().await; // test for graphics

    #[cfg(feature = "test_prioritized_fifo")]
    test_prioritized_fifo::run().await; // test for prioritized_fifo

    #[cfg(feature = "test_rr")]
    test_rr::run().await; // test for rr Round Robin scheduler

    Ok(())
}
