use awkernel_lib::{
    console::register_console,
    sync::mutex::{MCSNode, Mutex},
};
use core::fmt::{Error, Write};
use log::Log;
use std::io::{BufReader, Read, Stdin};

pub static CONSOLE: Console = Console::new();

pub struct Console {
    lock: Mutex<StdInOut>,
}

pub struct StdInOut {
    stdin: Option<BufReader<Stdin>>,
}

impl Write for StdInOut {
    fn write_str(&mut self, msg: &str) -> core::fmt::Result {
        let buf = msg.as_bytes();
        if unsafe { libc::write(0, buf.as_ptr() as _, buf.len()) } == 0 {
            Ok(())
        } else {
            Err(Error)
        }
    }
}

impl StdInOut {
    fn init(&mut self) {
        if self.stdin.is_none() {
            self.stdin = Some(BufReader::new(std::io::stdin()));
        }
    }
}

impl Console {
    const fn new() -> Self {
        Self {
            lock: Mutex::new(StdInOut { stdin: None }),
        }
    }
}

impl Log for Console {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut node = MCSNode::new();
        let mut guard = self.lock.lock(&mut node);

        let stdout: &mut StdInOut = &mut guard;
        awkernel_lib::logger::write_msg(stdout, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);

    register_console(&CONSOLE);
}

impl awkernel_lib::console::Console for Console {
    fn acknowledge_recv_interrupt(&self) {
        // TODO
    }

    fn enable(&self) {
        // TODO
    }

    fn disable(&self) {
        // TODO
    }

    fn get(&self) -> Option<u8> {
        let mut node = MCSNode::new();
        let mut inout = self.lock.lock(&mut node);

        inout.init();

        let ref_stdin = inout.stdin.as_mut().unwrap();

        let mut buf = [0; 1];

        let n = ref_stdin.read(&mut buf).ok()?;
        if n == 1 {
            Some(buf[0])
        } else {
            None
        }
    }

    fn put(&self, data: u8) {
        let mut node = MCSNode::new();
        let mut inout = self.lock.lock(&mut node);

        let _ = inout.write_char(data as char);
    }

    fn enable_recv_interrupt(&self) {
        // TODO
    }

    fn disable_recv_interrupt(&self) {
        // TODO
    }

    fn irq_id(&self) -> usize {
        // TODO
        0
    }

    fn print(&self, data: &str) {
        let mut node = MCSNode::new();
        let mut inout = self.lock.lock(&mut node);

        let _ = inout.write_str(data);
    }
}
