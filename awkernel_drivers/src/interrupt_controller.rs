#[cfg(feature = "aarch64")]
pub mod bcm2835;

#[cfg(feature = "aarch64")]
pub mod gicv2;

#[cfg(feature = "aarch64")]
pub mod gicv3;

#[cfg(feature = "x86")]
#[allow(static_mut_refs)]
pub mod apic;
