//! Frequency information utilities for x86_64 architecture
//! .
//! This module provides functions to retrieve information from leaf 0x16 of the CPUID instruction.

use super::try_read_leaf;
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x16;

pub struct FrequencyInfo(CpuidResult);

impl FrequencyInfo {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    pub const fn base_freq_mhz(&self) -> Option<u16> {
        match self.0.eax as u16 {
            0 => None,
            freq_mhz => Some(freq_mhz),
        }
    }

    pub const fn max_freq_mhz(&self) -> Option<u16> {
        match self.0.ebx as u16 {
            0 => None,
            freq_mhz => Some(freq_mhz),
        }
    }

    pub const fn bus_freq_mhz(&self) -> Option<u16> {
        match self.0.ecx as u16 {
            0 => None,
            freq_mhz => Some(freq_mhz),
        }
    }
}

#[inline]
pub fn try_read() -> Option<FrequencyInfo> {
    try_read_leaf(LEAF_NUMBER).map(FrequencyInfo::new)
}

#[inline]
pub fn base_freq_mhz() -> Option<u16> {
    try_read().and_then(|info| info.base_freq_mhz())
}

#[inline]
pub fn max_freq_mhz() -> Option<u16> {
    try_read().and_then(|info| info.max_freq_mhz())
}

#[inline]
pub fn bus_freq_mhz() -> u16 {
    try_read()
        .and_then(|info| info.bus_freq_mhz())
        .unwrap_or(100)
}

#[inline]
pub fn base_freq_hz() -> Option<u64> {
    base_freq_mhz().map(|freq_mhz| freq_mhz as u64 * 1_000_000)
}

#[inline]
pub fn max_freq_hz() -> Option<u64> {
    max_freq_mhz().map(|freq_mhz| freq_mhz as u64 * 1_000_000)
}

#[inline]
pub fn bus_freq_hz() -> u64 {
    bus_freq_mhz() as u64 * 1_000_000
}
