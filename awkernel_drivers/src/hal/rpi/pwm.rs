use super::gpio::{GpioFunction, GpioPin, GpioPinAlt, PullMode};
use crate::clock::{self, CLOCK_FREQUENCY};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};
use embedded_hal::pwm::{Error, ErrorKind, ErrorType, SetDutyCycle};

/// Base address for the PWM module
pub static mut PWM_BASE: usize = 0;

/// Set the base address for the PWM module
///
/// # Safety
///
/// This function is unsafe because it modifies a static mutable variable
pub unsafe fn set_pwm_base(base: usize) {
    write_volatile(&mut PWM_BASE, base);
}

/// Registers associated with the PWM module
pub mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    mmio_rw!(offset 0x00 => pub CTL<Control>); // Control
    mmio_rw!(offset 0x04 => pub STA<Status>); // Status
    mmio_rw!(offset 0x10 => pub RNG1<u32>); // Channel 1 Range
    mmio_rw!(offset 0x14 => pub DAT1<u32>); // Channel 1 Data
    mmio_rw!(offset 0x18 => pub FIF1<u32>); // FIFO Input
    mmio_rw!(offset 0x20 => pub RNG2<u32>); // Channel 2 Range
    mmio_rw!(offset 0x24 => pub DAT2<u32>); // Channel 2 Data

    bitflags! {
        #[derive(Debug)]
        pub struct Control: u32 {
            const PWEN1 = 1 << 0; // Channel 1 Enable
            const MODE1 = 1 << 1; // Channel 1 Mode
            const RPTL1 = 1 << 2; // Channel 1 Repeat Last Data
            const SBIT1 = 1 << 3; // Channel 1 State in Standby Mode
            const POLA1 = 1 << 4; // Channel 1 Output Polarity
            const USEF1 = 1 << 5; // Channel 1 Use FIFO
            const CLRF = 1 << 6; // Clear FIFO
            const MSEN1 = 1 << 7; // Channel 1 M/S Enable
            const PWEN2 = 1 << 8; // Channel 2 Enable
            const MODE2 = 1 << 9; // Channel 2 Mode
            const MSEN2 = 1 << 15; // Channel 2 M/S Enable
        }

        #[derive(Debug)]
        pub struct Status: u32 {
            const FULL1 = 1 << 0; // FIFO Full Flag
            const EMPT1 = 1 << 1; // FIFO Empty Flag
            const WERR1 = 1 << 2; // FIFO Write Error Flag
            const RERR1 = 1 << 3; // FIFO Read Error Flag
            const GAPO1 = 1 << 4; // Channel 2 Gap Occurred Flag
            const GAPO2 = 1 << 5; // Channel 1 Gap Occurred Flag
            const BERR = 1 << 8; // Bus Error Flag
            const STA1 = 1 << 9; // Channel 2 State
            const STA2 = 1 << 10; // Channel 1 State
        }
    }
}

pub const FREQUENCY: u32 = 9_000_000; // 9 [MHz]

/// Error types for the PWM module
#[derive(Debug)]
pub enum PwmError {
    InvalidDutyCycle,
    InvalidPeriod,
    HardwareFailure,
    InvalidFrequency,
}

impl Error for PwmError {
    fn kind(&self) -> ErrorKind {
        ErrorKind::Other
    }
}

impl ErrorType for Pwm {
    type Error = PwmError;
}

impl From<&str> for PwmError {
    fn from(_: &str) -> Self {
        PwmError::InvalidDutyCycle
    }
}

/// Indicator if the clock has been initialized
static INIT_CLOCK: AtomicBool = AtomicBool::new(false);

pub struct Pwm {
    base: usize,
    rng1: u32,
    dat1: u32,
    _pin12: GpioPinAlt,
}

impl Pwm {
    /// Creates a new instance of the PWM module
    pub fn new() -> Result<Pwm, &'static str> {
        let pin12 = GpioPin::new(12)?;
        let pin12 = pin12.into_alt(GpioFunction::ALTF0, PullMode::None)?;

        let base = unsafe { read_volatile(&PWM_BASE) };

        let mut pwm = Pwm {
            base,
            rng1: FREQUENCY / 100,
            dat1: (FREQUENCY / 100) / 2,
            _pin12: pin12,
        };

        let _ = pwm.disable();

        pwm.clear_sta();

        Ok(pwm)
    }
    /// Enables the PWM module
    pub fn enable(&mut self) -> Result<(), PwmError> {
        use registers::Control;

        let old_pwm_ctl = registers::CTL.read(self.base)
            & (Control::PWEN1 | Control::MSEN1 | Control::PWEN2 | Control::MSEN2);

        if !INIT_CLOCK.load(Ordering::Relaxed) {
            registers::CTL.write(Control::empty(), self.base);
            awkernel_lib::delay::wait_microsec(10);
            let osc_freq: usize = unsafe { read_volatile(&CLOCK_FREQUENCY) };

            let desired_pwm_freq = FREQUENCY;

            let div_total = osc_freq as f64 / desired_pwm_freq as f64;
            let divi = div_total as u32;
            let divf = ((div_total - divi as f64) * 4096.0) as u32;
            let clk = clock::Clock::new();

            match clk.enable_pwm_clock(
                clock::ClockSource::Oscillator,
                divi,
                divf,
                clock::MashType::Stage1,
            ) {
                Ok(()) => log::info!("PWM clock enabled"),
                Err(err) => log::info!("Error enabling PWM clock: {}", err),
            }

            INIT_CLOCK.store(true, Ordering::Relaxed);
        }

        self.set_rng1();
        self.set_dat1();

        registers::CTL.write(
            old_pwm_ctl | registers::Control::PWEN1 | registers::Control::MSEN1,
            self.base,
        );

        Ok(())
    }

    /// Disables the PWM module
    pub fn disable(&mut self) -> Result<(), PwmError> {
        let mut ctl = registers::CTL.read(self.base);
        ctl.remove(registers::Control::PWEN1);
        registers::CTL.write(ctl, self.base);
        Ok(())
    }

    /// Sets the frequency for the PWM module
    pub fn set_frequency(&mut self, frequency: u32) -> Result<(), PwmError> {
        if frequency == 0 || frequency > FREQUENCY {
            return Err(PwmError::InvalidFrequency);
        }
        let clock_frequency = FREQUENCY;
        let range = clock_frequency / frequency;
        if range == 0 {
            return Err(PwmError::InvalidFrequency);
        }
        let remainder = clock_frequency % frequency;
        if remainder != 0 {
            log::warn!("PWM frequency {} Hz is not an exact divisor of clock frequency {} Hz. Actual frequency will be {} Hz.",
                frequency, clock_frequency, clock_frequency / range);
        }

        registers::RNG1.write(range, self.base);
        Ok(())
    }

    fn set_rng1(&mut self) {
        registers::RNG1.write(self.rng1, self.base);
    }

    fn set_dat1(&mut self) {
        registers::DAT1.write(self.dat1, self.base);
    }

    fn clear_sta(&self) {
        use registers::Status;
        registers::STA.write(
            Status::BERR | Status::GAPO1 | Status::GAPO2 | Status::RERR1 | Status::WERR1,
            self.base,
        );
    }
}

impl SetDutyCycle for Pwm {
    /// Returns the maximum duty cycle
    fn get_max_duty_cycle(&self) -> u16 {
        registers::RNG1.read(self.base) as u16
    }

    /// Sets the duty cycle
    fn set_duty_cycle(&mut self, duty: u16) -> Result<(), Self::Error> {
        registers::DAT1.write(duty as u32, self.base);
        Ok(())
    }

    /// Sets the duty cycle based on a fraction
    fn set_duty_cycle_fraction(&mut self, num: u16, denom: u16) -> Result<(), Self::Error> {
        let duty = num as u32 * self.get_max_duty_cycle() as u32 / denom as u32;
        self.set_duty_cycle(duty as u16)
    }

    /// Sets the duty cycle based on a percentage
    fn set_duty_cycle_percent(&mut self, percent: u8) -> Result<(), Self::Error> {
        self.set_duty_cycle_fraction(percent as u16, 100)
    }
}
