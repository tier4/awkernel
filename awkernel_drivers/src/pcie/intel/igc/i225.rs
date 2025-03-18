use super::igc_hw::{IgcHw, IgcMacOperations, IgcNvmOperations, IgcOperations, IgcPhyOperations};
use crate::pcie::PCIeInfo;

pub(super) struct I225Flash {
    info: PCIeInfo,
    hw: IgcHw,
}

impl IgcOperations for I225Flash {}
impl IgcMacOperations for I225Flash {}
impl IgcPhyOperations for I225Flash {}
impl IgcNvmOperations for I225Flash {}

pub(super) struct I225NoFlash {
    info: PCIeInfo,
    hw: IgcHw,
}

impl IgcOperations for I225NoFlash {}
impl IgcMacOperations for I225NoFlash {}
impl IgcPhyOperations for I225NoFlash {}
impl IgcNvmOperations for I225NoFlash {}
