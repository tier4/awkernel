use super::igc_hw::{IgcMacOperations, IgcNvmOperations, IgcOperations, IgcPhyOperations};

pub(super) struct I225Flash;

impl IgcOperations for I225Flash {}
impl IgcMacOperations for I225Flash {}
impl IgcPhyOperations for I225Flash {}
impl IgcNvmOperations for I225Flash {}

pub(super) struct I225NoFlash;

impl IgcOperations for I225NoFlash {}
impl IgcMacOperations for I225NoFlash {}
impl IgcPhyOperations for I225NoFlash {}
impl IgcNvmOperations for I225NoFlash {}
