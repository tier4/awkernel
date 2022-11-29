#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub mod pl011;

use alloc::vec::Vec;

pub trait UART {
    fn new(base: usize) -> Self;
    fn send(&self, c: u32);
    fn recv(&self) -> u32;
    fn enable_recv_interrupt(&self);
    fn disable_recv_interrupt(&self);
    fn on(&self);
    fn off(&self);
    fn init(&self, clock: usize, baudrate: usize);

    fn write_str(&self, data: &str) {
        for c in data.bytes() {
            self.send(c as u32);
            if c == b'\n' {
                self.send(b'\r' as u32);
            }
        }
    }

    fn read_line(&self) -> Vec<u8> {
        let mut res = Vec::new();

        loop {
            let c = self.recv() as u8;
            if c == b'\r' || c == b'\n' {
                break;
            } else if c == 0x08 || c == 0x7F {
                if !res.is_empty() {
                    self.send(0x08);
                    self.send(b' ' as u32);
                    self.send(0x08);
                    res.pop();
                }
            } else if c == b'\t' {
                let c = b' ';
                for _ in 0..8 {
                    self.send(c as u32);
                    res.push(c);
                }
            } else if c == 0x15 {
                while !res.is_empty() {
                    self.send(0x08);
                    self.send(b' ' as u32);
                    self.send(0x08);
                    res.pop();
                }
            } else {
                self.send(c as u32);
                res.push(c);
            }
        }

        self.write_str("\n");

        res
    }
}

#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub type DevUART = pl011::RaspiUART;

impl DevUART
where
    DevUART: UART,
{
    // pub fn new() -> Self {
    //     pl011::RaspiUART::new()
    // }
}
