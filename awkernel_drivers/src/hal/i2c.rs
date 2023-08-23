use embedded_hal::blocking::i2c::{self, AddressMode};

pub fn write_quick<A: AddressMode, E>(
    i2c: &mut dyn i2c::Write<A, Error = E>,
    address: A,
) -> Result<(), E> {
    i2c.write(address, &[])
}
