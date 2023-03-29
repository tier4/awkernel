use self::acpi::AcpiMapper;
use ::acpi::AcpiTables;

pub mod acpi;
pub(super) mod cpu;
pub(crate) mod delay;

pub fn init(acpi: &AcpiTables<AcpiMapper>, offset: u64) {
    // Initialize timer.
    acpi::init(acpi);
    delay::init(acpi, offset);
}
