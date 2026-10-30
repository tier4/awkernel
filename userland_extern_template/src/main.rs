#![no_std]
#![no_main]

extern crate alloc;
// Links the kernel's entry points and panic handler.
extern crate awkernel;

use alloc::borrow::Cow;
use awkernel_async_lib::sleep;
use core::time::Duration;

#[awkernel::main]
async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_userland::run().await?;
    loop {
        log::info!("Hello from an out-of-tree userland!");
        sleep(Duration::from_secs(1)).await;
    }
}
