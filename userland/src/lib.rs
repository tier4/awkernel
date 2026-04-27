#![no_std]

extern crate alloc;

use alloc::borrow::Cow;

pub async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_services::run().await;

    #[cfg(feature = "rd_gen_to_dags")]
    rd_gen_to_dags::run().await; // run the rd_gen_to_dags application

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

    #[cfg(feature = "test_multi_prioritized_scheduler")]
    test_multi_prioritized_scheduler::run().await; // test for multi prioritized scheduler

    #[cfg(feature = "test_prioritized_rr")]
    test_prioritized_rr::run().await; // test for prioritized_rr

    #[cfg(feature = "test_async_mutex")]
    test_async_mutex::run().await; // test for async_mutex

    #[cfg(feature = "test_gedf")]
    test_gedf::run().await; // test for Global Earliest Deadline First scheduler

    #[cfg(feature = "test_measure_channel")]
    test_measure_channel::run().await; // measure channel

    #[cfg(feature = "test_measure_channel_heavy")]
    test_measure_channel_heavy::run().await; // measure channel heavy

    #[cfg(feature = "test_dag")]
    test_dag::run().await; // test for DAG

    #[cfg(feature = "test_autoware")]
    test_autoware::run().await; // test for Autoware

    #[cfg(feature = "test_dvfs")]
    test_dvfs::run().await; // test for DVFS

    #[cfg(feature = "test_voluntary_preemption")]
    test_voluntary_preemption::run().await; // test for voluntary preemption

    Ok(())
}
