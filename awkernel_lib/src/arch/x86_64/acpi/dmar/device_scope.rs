use core::{marker::PhantomData, mem};

#[derive(Debug)]
pub struct DeviceScopeIter<'a> {
    pub(super) pointer: *const u8,
    pub(super) remaining_length: u8,
    pub(super) _phantom: PhantomData<&'a ()>,
}

impl<'a> Iterator for DeviceScopeIter<'a> {
    type Item = (&'a DeviceScope, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_length >= mem::size_of::<DeviceScope>() as u8 {
            let device_scope = unsafe { &*(self.pointer as *const DeviceScope) };

            let size_of_device_scope = mem::size_of::<DeviceScope>();
            let ptr_path = self.pointer.wrapping_add(size_of_device_scope) as *const u8;

            let path = unsafe {
                core::slice::from_raw_parts(
                    ptr_path,
                    device_scope.length as usize - size_of_device_scope,
                )
            };

            self.pointer = unsafe { self.pointer.offset(device_scope.length as isize) };
            self.remaining_length = self
                .remaining_length
                .saturating_sub(device_scope.length as u8);

            Some((&device_scope, path))
        } else {
            None
        }
    }
}

#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DeviceScope {
    pub entry_type: u8, // 1: PCI Endpoint Device, 2: PCI Sub-hierarchy, 3: IOAPIC, 4: MSI_CAPABLE_HPET1, 5: ACPI Namespace Device
    pub length: u8,
    pub flags: u8,
    pub reserved: u8,
    pub enumeration_id: u8,
    pub start_bus_number: u8,
}
