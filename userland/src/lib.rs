#![no_std]

extern crate alloc;

use alloc::borrow::Cow;

pub async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_services::run().await;

    velodyne_icp::run().await;

    Ok(())
}
