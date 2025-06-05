use embedded_hal::i2c;

pub fn write_quick<A: i2c::AddressMode, E: i2c::Error>(
    i2c: &mut dyn i2c::I2c<A, Error = E>,
    address: A,
) -> Result<(), E> {
    i2c.write(address, &[])
}
