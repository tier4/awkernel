use alloc::string::String;
use awkernel_async_lib::channel::bounded;
use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};

static BUFFERED_LOGGER: Mutex<Option<BufferedLogger>> = Mutex::new(None);
static LOGGER: Logger = Logger;

struct BufferedLogger {
    tx: bounded::Sender<String>,
    discarded: u64,
}

struct Logger;

impl log::Log for Logger {
    fn log(&self, record: &log::Record) {
        {
            let mut node = MCSNode::new();
            let mut logger = BUFFERED_LOGGER.lock(&mut node);

            if let Some(logger) = logger.as_mut() {
                if logger.tx.is_full() {
                    logger.discarded += 1;
                    return;
                }

                let msg = awkernel_lib::logger::format_msg(record);

                if logger.tx.try_send(msg).is_err() {
                    logger.discarded += 1;
                }

                return;
            }
        }

        // Nobody drains the buffer, so print directly.
        // The lock is released first, so that a panic while printing
        // does not make the panic handler spin on it.
        let msg = awkernel_lib::logger::format_msg(record);
        awkernel_lib::console::print(&msg);
    }

    fn flush(&self) {}

    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }
}

/// Stops buffering when the logger task ends, e.g., because it panicked.
///
/// If the task panicked, it would be moved to the panicked scheduler and
/// nobody would drain the buffer, so all log output, including the panic
/// report, would silently disappear.
///
/// This must be declared after the receiver so that it is dropped first.
struct FallbackOnDrop<'a>(&'a bounded::Receiver<String>);

impl Drop for FallbackOnDrop<'_> {
    fn drop(&mut self) {
        // After this, `Logger::log` prints directly and nothing is queued.
        let buffered_logger = {
            let mut node = MCSNode::new();
            let mut logger = BUFFERED_LOGGER.lock(&mut node);
            logger.take()
        };
        drop(buffered_logger);

        // Print what is still queued, which includes the panic report.
        while let Ok(msg) = self.0.try_recv() {
            awkernel_lib::console::print(&msg);
        }

        // Do not use `log` here, because it allocates during unwinding.
        awkernel_lib::console::print("buffered logger stopped; falling back to direct output\r\n");
    }
}

pub async fn run() {
    let (tx, rx) = bounded::new(bounded::Attribute {
        queue_size: 4096,
        ..Default::default()
    });
    let buffered_logger = BufferedLogger { tx, discarded: 0 };

    {
        let mut node = MCSNode::new();
        let mut logger = BUFFERED_LOGGER.lock(&mut node);

        *logger = Some(buffered_logger);
    }

    let _fallback = FallbackOnDrop(&rx);

    awkernel_lib::logger::set_buf_console(&LOGGER);
    log::set_max_level(log::LevelFilter::Debug);

    let mut n: u8 = 0;
    while let Ok(msg) = rx.recv().await {
        awkernel_lib::console::print(&msg);
        n = n.wrapping_add(1);

        if n & 0x0f == 0 {
            awkernel_async_lib::r#yield().await;
        }
    }
}
