#![cfg_attr(not(feature = "std"), no_std)]
#![no_main]

extern crate alloc;

use alloc::borrow::Cow;

#[awkernel::main]
async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_userland::run().await
}
