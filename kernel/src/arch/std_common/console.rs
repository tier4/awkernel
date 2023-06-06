use awkernel_lib::console::register_console;
use core::fmt::{Error, Write};
use std::io::{BufReader, Read, Stdin};

pub struct Console {
    reader: BufReader<Stdin>,
}

impl Write for Console {
    fn write_str(&mut self, msg: &str) -> core::fmt::Result {
        let buf = msg.as_bytes();
        if unsafe { libc::write(0, buf.as_ptr() as _, buf.len()) } == 0 {
            Ok(())
        } else {
            Err(Error)
        }
    }
}

impl Console {
    fn new() -> Self {
        Self {
            reader: BufReader::new(std::io::stdin()),
        }
    }
}

pub fn init() {
    register_console(Box::new(Console::new()));
}

impl awkernel_lib::console::Console for Console {
    fn acknowledge_recv_interrupt(&mut self) {
        // TODO
    }

    fn enable(&mut self) {
        // TODO
    }

    fn disable(&mut self) {
        // TODO
    }

    fn get(&mut self) -> Option<u8> {
        let mut buf = [0; 1];

        let n = self.reader.read(&mut buf).ok()?;
        if n == 1 {
            Some(buf[0])
        } else {
            None
        }
    }

    fn put(&mut self, data: u8) {
        unsafe { libc::write(0, &data as *const u8 as _, 1) };
    }

    fn enable_recv_interrupt(&mut self) {
        // TODO
    }

    fn disable_recv_interrupt(&mut self) {
        // TODO
    }

    fn irq_id(&self) -> usize {
        // TODO
        0
    }
}
