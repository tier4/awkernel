use super::acpi::AcpiMapper;
use crate::{
    delay,
    mmio::{ReadOnlyOffset, WriteOnlyOffset},
    sync::mutex::{MCSNode, Mutex},
};
use acpi::{
    address::{AccessSize, AddressSpace, GenericAddress},
    fadt::Fadt,
    AcpiHandler, AcpiTables,
};
use alloc::boxed::Box;
use aml::{
    value::{AmlValue, Args},
    AmlContext, AmlName, DebugVerbosity, Handler,
};
use core::{ptr, slice};
use x86_64::{
    instructions::{
        hlt,
        port::{PortReadOnly, PortWriteOnly},
    },
    VirtAddr,
};

const SCI_EN: u64 = 1 << 0;
const SLP_TYP_SHIFT: u16 = 10;
const SLP_EN: u16 = 1 << 13;
const SLP_TYP_MASK: u64 = 0x7 << SLP_TYP_SHIFT;

static POWER_CONTROL: Mutex<PowerControlState> = Mutex::new(PowerControlState::Uninitialized);

#[derive(Clone, Copy)]
enum PowerControlState {
    Uninitialized,
    Ready(PowerControl),
    Failed(&'static str),
}

#[derive(Clone, Copy)]
struct PowerControl {
    reset_reg: Option<AcpiRegister>,
    reset_value: u8,
    smi_cmd_port: Option<u16>,
    acpi_enable: u8,
    pm1a_control: AcpiRegister,
    pm1b_control: Option<AcpiRegister>,
    slp_typa: u16,
    slp_typb: u16,
}

#[derive(Clone, Copy)]
struct AcpiRegister {
    address_space: AddressSpace,
    width_bytes: u8,
    address: u64,
}

pub fn init(acpi: &AcpiTables<AcpiMapper>) -> Result<(), &'static str> {
    let mut node = MCSNode::new();
    let mut state = POWER_CONTROL.lock(&mut node);
    if !matches!(*state, PowerControlState::Uninitialized) {
        return Ok(());
    }

    match init_power_control(acpi) {
        Ok(control) => {
            *state = PowerControlState::Ready(control);
            Ok(())
        }
        Err(err) => {
            *state = PowerControlState::Failed(err);
            Err(err)
        }
    }
}

pub fn shutdown() -> ! {
    let control = match current_power_control() {
        Ok(control) => control,
        Err(err) => {
            log::error!("Shutdown is unavailable. {err}");
            qemu_shutdown_fallback();
        }
    };

    if let Err(err) = enable_acpi(&control) {
        log::warn!("Failed to enable ACPI mode before shutdown. {err}");
    }

    if let Err(err) = write_sleep_control(control.pm1a_control, control.slp_typa) {
        log::error!("Failed to write PM1a control block. {err}");
        qemu_shutdown_fallback();
    }

    if let Some(pm1b) = control.pm1b_control {
        if let Err(err) = write_sleep_control(pm1b, control.slp_typb) {
            log::error!("Failed to write PM1b control block. {err}");
            qemu_shutdown_fallback();
        }
    }

    wait_for_power_transition();
}

pub fn reboot() -> ! {
    if let Ok(control) = current_power_control() {
        if let Some(reset_reg) = control.reset_reg {
            if let Err(err) = write_register(reset_reg, control.reset_value as u64) {
                log::warn!("ACPI reset register reboot failed. {err}");
            }
        }
    } else {
        log::warn!("ACPI reboot is unavailable, using legacy reset paths.");
    }

    legacy_reboot();
}

fn init_power_control(acpi: &AcpiTables<AcpiMapper>) -> Result<PowerControl, &'static str> {
    let fadt = acpi
        .find_table::<Fadt>()
        .map_err(|_| "Failed to locate FADT.")?;
    let physical_memory_offset = fadt.virtual_start().as_ptr() as usize - fadt.physical_start();
    let flags = unsafe { ptr::addr_of!(fadt.flags).read_unaligned() };
    let supports_fadt_reset = flags.supports_system_reset_via_fadt();

    let reset_reg = match fadt.reset_register() {
        Ok(register) if supports_fadt_reset => {
            Some(convert_register(register, physical_memory_offset)?)
        }
        _ => None,
    };

    let pm1a_control = convert_register(
        fadt.pm1a_control_block()
            .map_err(|_| "Failed to locate PM1a control block.")?,
        physical_memory_offset,
    )?;
    let pm1b_control = fadt
        .pm1b_control_block()
        .map_err(|_| "Failed to locate PM1b control block.")?
        .map(|register| convert_register(register, physical_memory_offset))
        .transpose()?;

    let (slp_typa, slp_typb) = parse_s5_sleep_types(acpi, fadt.handler().clone())?;

    Ok(PowerControl {
        reset_reg,
        reset_value: fadt.reset_value,
        smi_cmd_port: (fadt.smi_cmd_port != 0).then_some(fadt.smi_cmd_port as u16),
        acpi_enable: fadt.acpi_enable,
        pm1a_control,
        pm1b_control,
        slp_typa,
        slp_typb,
    })
}

fn current_power_control() -> Result<PowerControl, &'static str> {
    let mut node = MCSNode::new();
    let state = POWER_CONTROL.lock(&mut node);
    match *state {
        PowerControlState::Ready(control) => Ok(control),
        PowerControlState::Failed(err) => Err(err),
        PowerControlState::Uninitialized => Err("x86 power control is not initialized."),
    }
}

fn convert_register(
    register: GenericAddress,
    physical_memory_offset: usize,
) -> Result<AcpiRegister, &'static str> {
    let width_bytes = register_width_bytes(&register)?;
    if register.bit_offset != 0 {
        return Err("ACPI register bit offsets are not supported.");
    }

    let address = match register.address_space {
        AddressSpace::SystemIo => {
            if register.address > u16::MAX as u64 {
                return Err("System I/O register address exceeds 16-bit port range.");
            }
            if !matches!(width_bytes, 1 | 2 | 4) {
                return Err("Unsupported I/O register width.");
            }
            register.address
        }
        AddressSpace::SystemMemory => {
            if !matches!(width_bytes, 1 | 2 | 4 | 8) {
                return Err("Unsupported memory register width.");
            }
            let virt = VirtAddr::new(physical_memory_offset as u64) + register.address;
            virt.as_u64()
        }
        _ => return Err("Unsupported ACPI register address space."),
    };

    Ok(AcpiRegister {
        address_space: register.address_space,
        width_bytes,
        address,
    })
}

fn register_width_bytes(register: &GenericAddress) -> Result<u8, &'static str> {
    match register.access_size {
        AccessSize::ByteAccess => Ok(1),
        AccessSize::WordAccess => Ok(2),
        AccessSize::DWordAccess => Ok(4),
        AccessSize::QWordAccess => Ok(8),
        AccessSize::Undefined => match register.bit_width {
            0..=8 => Ok(1),
            9..=16 => Ok(2),
            17..=32 => Ok(4),
            33..=64 => Ok(8),
            _ => Err("Unsupported ACPI register width."),
        },
    }
}

fn read_register(register: AcpiRegister) -> Result<u64, &'static str> {
    match register.address_space {
        AddressSpace::SystemIo => unsafe {
            Ok(match register.width_bytes {
                1 => PortReadOnly::<u8>::new(register.address as u16).read() as u64,
                2 => PortReadOnly::<u16>::new(register.address as u16).read() as u64,
                4 => PortReadOnly::<u32>::new(register.address as u16).read() as u64,
                _ => return Err("Unsupported I/O register width."),
            })
        },
        AddressSpace::SystemMemory => Ok(match register.width_bytes {
            1 => ReadOnlyOffset::<0, u8>::new().read(register.address as usize) as u64,
            2 => ReadOnlyOffset::<0, u16>::new().read(register.address as usize) as u64,
            4 => ReadOnlyOffset::<0, u32>::new().read(register.address as usize) as u64,
            8 => ReadOnlyOffset::<0, u64>::new().read(register.address as usize),
            _ => return Err("Unsupported memory register width."),
        }),
        _ => Err("Unsupported ACPI register address space."),
    }
}

fn write_register(register: AcpiRegister, value: u64) -> Result<(), &'static str> {
    match register.address_space {
        AddressSpace::SystemIo => unsafe {
            match register.width_bytes {
                1 => PortWriteOnly::<u8>::new(register.address as u16).write(value as u8),
                2 => PortWriteOnly::<u16>::new(register.address as u16).write(value as u16),
                4 => PortWriteOnly::<u32>::new(register.address as u16).write(value as u32),
                _ => return Err("Unsupported I/O register width."),
            }
        },
        AddressSpace::SystemMemory => match register.width_bytes {
            1 => WriteOnlyOffset::<0, u8>::new().write(value as u8, register.address as usize),
            2 => WriteOnlyOffset::<0, u16>::new().write(value as u16, register.address as usize),
            4 => WriteOnlyOffset::<0, u32>::new().write(value as u32, register.address as usize),
            8 => WriteOnlyOffset::<0, u64>::new().write(value, register.address as usize),
            _ => return Err("Unsupported memory register width."),
        },
        _ => return Err("Unsupported ACPI register address space."),
    }

    Ok(())
}

fn write_sleep_control(register: AcpiRegister, slp_typ: u16) -> Result<(), &'static str> {
    let current = read_register(register)?;
    let sleep_type = ((slp_typ as u64) << SLP_TYP_SHIFT) & SLP_TYP_MASK;
    let prepared = (current & !(SLP_TYP_MASK | SLP_EN as u64)) | sleep_type;

    write_register(register, prepared)?;
    write_register(register, prepared | SLP_EN as u64)
}

fn enable_acpi(control: &PowerControl) -> Result<(), &'static str> {
    let Some(smi_cmd_port) = control.smi_cmd_port else {
        return Ok(());
    };

    if control.acpi_enable == 0 {
        return Ok(());
    }

    if read_register(control.pm1a_control)? & SCI_EN != 0 {
        return Ok(());
    }

    unsafe {
        PortWriteOnly::<u8>::new(smi_cmd_port).write(control.acpi_enable);
    }

    for _ in 0..300 {
        if read_register(control.pm1a_control)? & SCI_EN != 0 {
            return Ok(());
        }

        delay::wait_millisec(10);
    }

    Err("Timed out while waiting for SCI_EN.")
}

fn parse_s5_sleep_types(
    acpi: &AcpiTables<AcpiMapper>,
    handler: AcpiMapper,
) -> Result<(u16, u16), &'static str> {
    let mut context = AmlContext::new(
        Box::new(AmlHandler::new(handler.clone())),
        DebugVerbosity::None,
    );

    parse_aml_table(
        &mut context,
        handler.clone(),
        acpi.dsdt().map_err(|_| "Failed to locate DSDT.")?,
    )?;
    for ssdt in acpi.ssdts() {
        parse_aml_table(&mut context, handler.clone(), ssdt)?;
    }

    let path = AmlName::from_str("\\_S5").map_err(|_| "Invalid AML name for _S5.")?;
    let value = match context
        .namespace
        .get_by_path(&path)
        .map_err(|_| "Failed to locate \\_S5 in AML.")?
        .clone()
    {
        AmlValue::Method { .. } => context
            .invoke_method(&path, Args::default())
            .map_err(|_| "Failed to evaluate \\_S5 AML method.")?,
        value => value,
    };

    parse_sleep_types(&value, &context)
}

fn parse_aml_table(
    context: &mut AmlContext,
    handler: AcpiMapper,
    table: acpi::AmlTable,
) -> Result<(), &'static str> {
    let mapping =
        unsafe { handler.map_physical_region::<u8>(table.address, table.length as usize) };
    let data =
        unsafe { slice::from_raw_parts(mapping.virtual_start().as_ptr(), mapping.region_length()) };
    context
        .parse_table(data)
        .map_err(|_| "Failed to parse AML table.")
}

fn parse_sleep_types(value: &AmlValue, context: &AmlContext) -> Result<(u16, u16), &'static str> {
    let AmlValue::Package(values) = value else {
        return Err("\\_S5 is not an AML package.");
    };

    if values.is_empty() {
        return Err("\\_S5 package is empty.");
    }

    let typa = values[0]
        .as_integer(context)
        .map_err(|_| "Failed to decode \\_S5 sleep type A.")? as u16;
    let typb = if values.len() >= 2 {
        values[1]
            .as_integer(context)
            .map_err(|_| "Failed to decode \\_S5 sleep type B.")? as u16
    } else {
        typa
    };

    Ok((typa, typb))
}

fn qemu_shutdown_fallback() -> ! {
    unsafe {
        PortWriteOnly::<u16>::new(0x604).write(0x2000);
        PortWriteOnly::<u16>::new(0xB004).write(0x2000);
    }

    wait_for_power_transition();
}

fn legacy_reboot() -> ! {
    unsafe {
        PortWriteOnly::<u8>::new(0xCF9).write(0x02);
        PortWriteOnly::<u8>::new(0xCF9).write(0x06);
        PortWriteOnly::<u8>::new(0x64).write(0xFE);
    }

    wait_for_power_transition();
}

fn wait_for_power_transition() -> ! {
    loop {
        hlt();
    }
}

struct AmlHandler {
    mapper: AcpiMapper,
}

impl AmlHandler {
    fn new(mapper: AcpiMapper) -> Self {
        Self { mapper }
    }

    fn read_system_memory<T: Copy>(&self, address: usize) -> T {
        let mapping = unsafe {
            self.mapper
                .map_physical_region::<T>(address, core::mem::size_of::<T>())
        };
        let value = ReadOnlyOffset::<0, T>::new().read(mapping.virtual_start().as_ptr() as usize);
        AcpiMapper::unmap_physical_region(&mapping);
        value
    }

    fn write_system_memory<T: Copy>(&mut self, address: usize, value: T) {
        let mapping = unsafe {
            self.mapper
                .map_physical_region::<T>(address, core::mem::size_of::<T>())
        };
        WriteOnlyOffset::<0, T>::new().write(value, mapping.virtual_start().as_ptr() as usize);
        AcpiMapper::unmap_physical_region(&mapping);
    }
}

impl Handler for AmlHandler {
    fn read_u8(&self, address: usize) -> u8 {
        self.read_system_memory(address)
    }

    fn read_u16(&self, address: usize) -> u16 {
        self.read_system_memory(address)
    }

    fn read_u32(&self, address: usize) -> u32 {
        self.read_system_memory(address)
    }

    fn read_u64(&self, address: usize) -> u64 {
        self.read_system_memory(address)
    }

    fn write_u8(&mut self, address: usize, value: u8) {
        self.write_system_memory(address, value)
    }

    fn write_u16(&mut self, address: usize, value: u16) {
        self.write_system_memory(address, value)
    }

    fn write_u32(&mut self, address: usize, value: u32) {
        self.write_system_memory(address, value)
    }

    fn write_u64(&mut self, address: usize, value: u64) {
        self.write_system_memory(address, value)
    }

    fn read_io_u8(&self, port: u16) -> u8 {
        unsafe { PortReadOnly::<u8>::new(port).read() }
    }

    fn read_io_u16(&self, port: u16) -> u16 {
        unsafe { PortReadOnly::<u16>::new(port).read() }
    }

    fn read_io_u32(&self, port: u16) -> u32 {
        unsafe { PortReadOnly::<u32>::new(port).read() }
    }

    fn write_io_u8(&self, port: u16, value: u8) {
        unsafe { PortWriteOnly::<u8>::new(port).write(value) }
    }

    fn write_io_u16(&self, port: u16, value: u16) {
        unsafe { PortWriteOnly::<u16>::new(port).write(value) }
    }

    fn write_io_u32(&self, port: u16, value: u32) {
        unsafe { PortWriteOnly::<u32>::new(port).write(value) }
    }

    fn read_pci_u8(&self, segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u8 {
        (read_pci_config(segment, bus, device, function, offset & !3)
            >> (((offset & 3) * 8) as u32)) as u8
    }

    fn read_pci_u16(&self, segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u16 {
        (read_pci_config(segment, bus, device, function, offset & !3)
            >> (((offset & 2) * 8) as u32)) as u16
    }

    fn read_pci_u32(&self, segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
        read_pci_config(segment, bus, device, function, offset & !3)
    }

    fn write_pci_u8(
        &self,
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        offset: u16,
        value: u8,
    ) {
        write_pci_partial(segment, bus, device, function, offset, value as u32, 0xFF);
    }

    fn write_pci_u16(
        &self,
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        offset: u16,
        value: u16,
    ) {
        write_pci_partial(segment, bus, device, function, offset, value as u32, 0xFFFF);
    }

    fn write_pci_u32(
        &self,
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        offset: u16,
        value: u32,
    ) {
        write_pci_config(segment, bus, device, function, offset, value);
    }

    fn stall(&self, microseconds: u64) {
        delay::wait_microsec(microseconds);
    }

    fn sleep(&self, milliseconds: u64) {
        delay::wait_millisec(milliseconds);
    }
}

fn read_pci_config(segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
    if segment != 0 {
        return 0;
    }

    let address = 0x8000_0000u32
        | ((bus as u32) << 16)
        | ((device as u32) << 11)
        | ((function as u32) << 8)
        | ((offset as u32) & 0xFC);

    unsafe {
        PortWriteOnly::<u32>::new(0xCF8).write(address);
        PortReadOnly::<u32>::new(0xCFC).read()
    }
}

fn write_pci_config(segment: u16, bus: u8, device: u8, function: u8, offset: u16, value: u32) {
    if segment != 0 {
        return;
    }

    let address = 0x8000_0000u32
        | ((bus as u32) << 16)
        | ((device as u32) << 11)
        | ((function as u32) << 8)
        | ((offset as u32) & 0xFC);

    unsafe {
        PortWriteOnly::<u32>::new(0xCF8).write(address);
        PortWriteOnly::<u32>::new(0xCFC).write(value);
    }
}

fn write_pci_partial(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    offset: u16,
    value: u32,
    mask: u32,
) {
    let aligned = offset & !3;
    let shift = ((offset & 3) * 8) as u32;
    let current = read_pci_config(segment, bus, device, function, aligned);
    let value = (current & !(mask << shift)) | ((value & mask) << shift);
    write_pci_config(segment, bus, device, function, aligned, value);
}
