# PCIe

In this section, we explain functions in [awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs).



## PCIeTree

The `PCIeTree` structure is defined as follows.

```rust
struct PCIeTree {
    // - Key: Bus number
    // - Value: PCIeBus
    tree: BTreeMap<u8, Box<PCIeBus>>,
}
```

There are 3 functions which `PCIeTree` structure provides.

| function | description |
|----------|-------------|
| `fn update_bridge_info(...)` | For each bus that the tree has, update the bridge information. |
| `fn attach(&mut self)` | Attach all the buses that the tree has to actually communicate with the PCIe device. |
| `fn init_base_address(&mut self, ranges: &mut [PCIeRange])` | Initialize the base address of every bus the tree has based on the PCIe memory range. |

<!-- ### Impl fmt::Display -->

The `PCIeTree` structure implements the `fmt:Display` trait as follows.

```rust
impl fmt::Display for PCIeTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (_, bus) in self.tree.iter() {
            if !bus.devices.is_empty() {
                write!(f, "{}", bus)?;
            }
        }

        Ok(())
    }
}
```

## PCIeBus

The `PCIeBus` structure is defined as follows.

```rust
pub struct PCIeBus {
    segment_group: u16,
    bus_number: u8,
    base_address: Option<VirtAddr>,
    info: Option<PCIeInfo>,
    devices: Vec<ChildDevice>,
}
```

There are 4 functions which `PCIeBus` structure provides.

| function | description |
|----------|-------------|
| `fn new(...)` | Construct `PCIeBus` structure. |
| ` fn update_bridge_info(...)` | Reflects bridge information to a bus and updates bus information. |
| `fn attach(&mut self)` | Attach all devices that the bus has. |
| `fn init_base_address(&mut self, ranges: &mut [PCIeRange])` | Initialize the base address of all devices that the bus has based on the PCIe memory range. |

<!-- ### Impl fmt::Display -->

The `PCIeBus` structure implements the [`PCIeDevice`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) trait as follows.

```rust
impl PCIeDevice for PCIeBus {
    fn device_name(&self) -> Cow<'static, str> {
        if let Some(info) = self.info.as_ref() {
            let bfd = info.get_bfd();
            let name = format!("{bfd}: Bridge, Bus #{:02x}", self.bus_number);
            name.into()
        } else {
            let name = format!("Bus #{:02x}", self.bus_number);
            name.into()
        }
    }

    fn children(&self) -> Option<&Vec<ChildDevice>> {
        Some(&self.devices)
    }
}
```

<!-- ### Impl PCIeDevice -->

The `PCIeBus` structure implements the `fmt::Display` trait as follows.

```rust
impl fmt::Display for PCIeBus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        print_pcie_devices(self, f, 0)
    }
}
```


## PCIeInfo

The `PCIeInfo` structure is defined as follows.

```rust
/// Information necessary for initializing the device
#[derive(Debug)]
pub struct PCIeInfo {
    pub(crate) config_space: ConfigSpace,
    segment_group: u16,
    bus_number: u8,
    device_number: u8,
    function_number: u8,
    id: u16,
    vendor: u16,
    revision_id: u8,
    interrupt_pin: u8,
    pcie_class: pcie_class::PCIeClass,
    device_name: Option<pcie_id::PCIeID>,
    pub(crate) header_type: u8,
    base_addresses: [BaseAddress; 6],
    msi: Option<capability::msi::Msi>,
    msix: Option<capability::msix::Msix>,
    pcie_cap: Option<capability::pcie_cap::PCIeCap>,

    // The bridge having this device.
    bridge_bus_number: Option<u8>,
    bridge_device_number: Option<u8>,
    bridge_function_number: Option<u8>,
}
```

There are 27 functions which `PCIeInfo` structure provides.

| function | description |
|----------|-------------|
| `fn from_io(...)` | Construct `PCIeInfo` structure with I/O ports (x86 only). |
| `fn from_addr(...)` | Construct `PCIeInfo` structure with virtual address. |
| `fn new(...)` | Construct `PCIeInfo` structure. |
| `fn init_base_address(&mut self, ranges: &mut [PCIeRange])` | Initialize the base address of `PCIeInfo` based on the PCIe memory range. |
| `pub fn get_bfd(&self)` | Get PCIe information in BDF format. |
| `pub fn get_secondary_bus(&self)` | Get the number of the PCIe secondary bus. |
| ` pub fn get_device_name(&self)` | Get the name of a PCIe device. |
| `pub fn get_class(&self)` | Get PCIe device classification. |
| `pub fn get_id(&self)` | Get PCIe device ID. |
| `pub fn get_revision_id(&self)` | Get PCIe revision ID. |
| `pub fn set_revision_id(&mut self, revision_id: u8)` | Set PCIe revision ID. |
| `pub fn get_msi_mut(&mut self)` | Get a mutable reference to the MSI (Message Signaled Interrupts) of a PCIe device. |
| `pub fn get_msix_mut(&mut self)` | Get a mutable reference to the MSI-X (Message Signaled Interrupts eXtended) of a PCIe device. |
| `pub fn get_pcie_cap_mut(&mut self)` | Get a mutable reference to the Capabilities Pointer (extended functionality) of a PCIe device. |
| `pub fn read_status_command(&self)` | Get the value of the STATUS_COMMAND register of a PCIe device. |
| `pub fn write_status_command(&mut self, csr: registers::StatusCommand)` | Set the value of the STATUS_COMMAND register of a PCIe device. |
| `pub fn get_segment_group(&self)` | Get the segment to which the PCIe device belongs. |
| `pub fn get_interrupt_line(&self)` | Get the interrupt line number to which the PCIe device belongs. |
| `pub fn set_interrupt_line(&mut self, irq: u8)` | Set the interrupt line number to which the PCIe device belongs. |
| `pub fn get_interrupt_pin(&self)` | Get the interrupt pin number corresponding to PCIe devices. |
| `pub(crate) fn read_capability(&mut self)` | Check PCIe device extension functionality settings and construct structures for PCIe extensions such as MSI, MSI-X, etc.. |
| `fn read_bar(&mut self)` | Read the base address of the PCIe device and reflect it in the `PCIeInfo` structure. |
| `pub(crate) fn map_bar(&mut self)` | Mapping the base address that a PCIe device has to a page. |
| `pub fn get_bar(&self, i: usize)` | Get the base address of the specified index. |
| `fn attach(self)` | Initialize the PCIe device based on the information. |
| `pub fn disable_legacy_interrupt(&mut self)` | Disable legacy interrupts (non-MSI interrupts) on PCIe devices. |
| `pub fn enable_legacy_interrupt(&mut self)` | Enable legacy interrupts (non-MSI interrupts) on PCIe devices. |

<!-- ### Impl fmt::Display -->

The `PCIeInfo` structure implements the `fmt::Display` trait as follows.

```rust
impl fmt::Display for PCIeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:04x}:{:02x}:{:02x}.{:01x}, Device ID = {:04x}, PCIe Class = {:?}",
            self.segment_group,
            self.bus_number,
            self.device_number,
            self.function_number,
            self.id,
            self.pcie_class,
        )
    }
}
```


## ChildDevice

The `ChildDevice` enum is defined as follows.

```rust
pub enum ChildDevice {
    Bus(Box<PCIeBus>),
    Attached(Arc<dyn PCIeDevice + Sync + Send>),
    Attaching,
    Unattached(Box<PCIeInfo>),
}
```

There are 2 functions which `ChildDevice` enum provides.

| function | description |
|----------|-------------|
| `fn attach(&mut self)` | Attach a child PCIe device. |
| `fn init_base_address(&mut self, ranges: &mut [PCIeRange])` | Initialize the base address of a child PCIe device based on the PCIe memory range. |


## UnknownDevice

The `UnknownDevice` structure is defined as follows.

```rust
struct UnknownDevice {
    segment_group: u16,
    bus_number: u8,
    device_number: u8,
    function_number: u8,
    vendor: u16,
    id: u16,
    pcie_class: pcie_class::PCIeClass,
}
```

<!-- ### Impl PCIeDevice -->

The `UnknownDevice` structure implements the [`PCIeDevice`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) trait as follows.

```rust
impl PCIeDevice for PCIeBus {
    fn device_name(&self) -> Cow<'static, str> {
        let bfd = format!(
            "{:04x}:{:02x}:{:02x}.{:01x}",
            self.segment_group, self.bus_number, self.device_number, self.function_number
        );

        let name = format!(
            "{bfd}: Vendor ID = {:04x}, Device ID = {:04x}, PCIe Class = {:?}",
            self.vendor, self.id, self.pcie_class,
        );
        name.into()
    }

    fn children(&self) -> Option<&Vec<ChildDevice>> {
        None
    }
}
```

## PCIeDeviceErr

The `PCIeDeviceErr` enum is defined as follows.

```rust
#[derive(Debug, Clone)]
pub enum PCIeDeviceErr {
    InitFailure,
    ReadFailure,
    PageTableFailure,
    CommandFailure,
    UnRecognizedDevice { bus: u8, device: u16, vendor: u16 },
    InvalidClass,
    Interrupt,
    NotImplemented,
    BARFailure,
}
```

<!-- ### Impl fmt::Display -->

The `PCIeDeviceErr` structure implements the `fmt::Display` trait as follows.

```rust
impl fmt::Display for PCIeDeviceErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InitFailure => {
                write!(f, "Failed to initialize the device driver.")
            }
            // omitted
        }
    }
}
```


## Initialization

### x86

For x86, the PCIe is initialized with ACPI in [`init_with_acpi`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) and with I/O port in [`init_with_io`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
/// Initialize the PCIe with ACPI.
#[cfg(feature = "x86")]
pub fn init_with_acpi(acpi: &AcpiTables<AcpiMapper>) -> Result<(), PCIeDeviceErr> {
    use awkernel_lib::{addr::phy_addr::PhyAddr, paging::Flags};

    const CONFIG_SPACE_SIZE: usize = 256 * 1024 * 1024; // 256 MiB

    let pcie_info = PciConfigRegions::new(acpi).or(Err(PCIeDeviceErr::InitFailure))?;
    for segment in pcie_info.iter() {
        let flags = Flags {
            write: true,
            execute: false,
            cache: false,
            write_through: false,
            device: true,
        };

        let mut config_start = segment.physical_address;
        let config_end = config_start + CONFIG_SPACE_SIZE;

        while config_start < config_end {
            let phy_addr = PhyAddr::new(config_start);
            let virt_addr = VirtAddr::new(config_start);

            unsafe {
                paging::map(virt_addr, phy_addr, flags).or(Err(PCIeDeviceErr::PageTableFailure))?
            };

            config_start += PAGESIZE;
        }

        let base_address = segment.physical_address;
        init_with_addr(segment.segment_group, VirtAddr::new(base_address), None);
    }

    Ok(())
}
```

```rust
/// Initialize the PCIe with IO port.
#[cfg(feature = "x86")]
pub fn init_with_io() {
    init(0, None, PCIeInfo::from_io, None);
}
```

### Others

The PCIe is initialized with the base address in [`init_with_addr`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) and in [`init`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
/// If `ranges` is not None, the base address registers of the device will be initialized by using `ranges`.
pub fn init_with_addr(
    segment_group: u16,
    base_address: VirtAddr,
    ranges: Option<&mut [PCIeRange]>,
) {
    init(
        segment_group,
        Some(base_address),
        PCIeInfo::from_addr,
        ranges,
    );
}
```

```rust
fn init<F>(
    segment_group: u16,
    base_address: Option<VirtAddr>,
    f: F,
    ranges: Option<&mut [PCIeRange]>,
) where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    let mut visited = BTreeSet::new();

    let mut bus_tree = PCIeTree {
        tree: BTreeMap::new(),
    };

    let mut host_bridge_bus = 0;

    //omitted: Construct `PCIeTree` and create a tree structure.

    bus_tree.update_bridge_info(host_bridge_bus, 0, 0);

    if let Some(ranges) = ranges {
        bus_tree.init_base_address(ranges);
    }

    bus_tree.attach();

    log::info!("PCIe: segment_group = {segment_group:04x}\r\n{}", bus_tree);

    let mut node = MCSNode::new();
    let mut pcie_trees = PCIE_TREES.lock(&mut node);
    pcie_trees.insert(segment_group, Arc::new(bus_tree));
}
```

## Enumerating PCI Buses

These functions which follows are to check every device on PCIe bus.

### check_bus

32 devices on a PCIe bus are checked in [`check_bus`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
#[inline]
fn check_bus<F>(bus: &mut PCIeBus, bus_tree: &mut PCIeTree, visited: &mut BTreeSet<u8>, f: &F)
where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    for device in 0..32 {
        check_device(bus, device, bus_tree, visited, f);
    }
}
```

### check_device

8 functions on a device are checked in [`check_device`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
#[inline]
fn check_device<F>(
    bus: &mut PCIeBus,
    device: u8,
    bus_tree: &mut PCIeTree,
    visited: &mut BTreeSet<u8>,
    f: &F,
) where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    for function in 0..8 {
        check_function(bus, device, function, bus_tree, visited, f);
    }
}
```

### check_function

The PCIe bus is actually scanned and its configuration information is stored in the `PCIeTree` in [`check_function`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
fn check_function<F>(
    bus: &mut PCIeBus,
    device: u8,
    function: u8,
    bus_tree: &mut PCIeTree,
    visited: &mut BTreeSet<u8>,
    f: &F,
) -> bool
where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    let offset =
        (bus.bus_number as usize) << 20 | (device as usize) << 15 | (function as usize) << 12;

    let addr = if let Some(base_address) = bus.base_address {
        base_address + offset
    } else {
        VirtAddr::new(0)
    };

    if let Ok(info) = f(bus.segment_group, bus.bus_number, device, function, addr) {

        // omitted: Push PCIe device to `PCIeTree`, considering if it is a bridge device
        
        true
    } else {
        false
    }
}

```

## Read base address

Reads the base address specified by offset from the PCIe device config space.

### read_bar

Reads the base address in [`read_bar`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
/// Read the base address of `addr`.
fn read_bar(config_space: &ConfigSpace, offset: usize) -> BaseAddress {
    let bar = config_space.read_u32(offset);

    if (bar & BAR_IO) == 1 {

        // omitted: Read the base address for x86

} else {
        // Memory space

        let bar_type = bar & BAR_TYPE_MASK;
        if bar_type == BAR_TYPE_32 {

            // ommitted: Read the base address for 32bit target

        } else if bar_type == BAR_TYPE_64 {

            // ommitted: Read the base address for 64bit target

        } else {
            BaseAddress::None
        }
    }
}

```

## Print PCIe devices

Print the configuration of devices on the PCIe bus.

### print_pcie_devices

Print devices in [`print_pcie_devices`:awkernel/awkernel_drivers/src/pcie.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/pcie.rs) as follows.

```rust
fn print_pcie_devices(device: &dyn PCIeDevice, f: &mut fmt::Formatter, indent: u8) -> fmt::Result {
    let indent_str = " ".repeat(indent as usize * 4);
    write!(f, "{}{}\r\n", indent_str, device.device_name())?;

    if let Some(children) = device.children() {
        for child in children.iter() {
            match child {
                ChildDevice::Attached(child) => {
                    print_pcie_devices(child.as_ref(), f, indent + 1)?;
                }
                ChildDevice::Unattached(info) => {
                    let name = format!(
                        "{}: Vendor ID = {:04x}, Device ID = {:04x}, PCIe Class = {:?}, bridge = {:?}-{:?}-{:?}",
                        info.get_bfd(),
                        info.vendor,
                        info.id,
                        info.pcie_class,
                        info.bridge_bus_number,
                        info.bridge_device_number,
                        info.bridge_function_number,
                    );

                    let indent_str = " ".repeat((indent as usize + 1) * 4);
                    write!(f, "{}{}\r\n", indent_str, name)?;
                }
                ChildDevice::Bus(bus) => {
                    print_pcie_devices(bus.as_ref(), f, indent + 1)?;
                }
                _ => (),
            }
        }
    }

    Ok(())
}
```