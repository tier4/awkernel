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
        let mut node = MCSNode::new();
        let mut logger = BUFFERED_LOGGER.lock(&mut node);

        let Some(logger) = logger.as_mut() else {
            return;
        };

        if logger.tx.is_full() {
            logger.discarded += 1;
            return;
        }

        let msg = awkernel_lib::logger::format_msg(record);

        if logger.tx.try_send(msg).is_err() {
            logger.discarded += 1;
        }
    }

    fn flush(&self) {}

    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        let mut node = MCSNode::new();
        let logger = BUFFERED_LOGGER.lock(&mut node);

        logger.is_some()
    }
}

pub async fn run() {
    let (tx, rx) = bounded::new(Default::default());
    let buffered_logger = BufferedLogger { tx, discarded: 0 };

    {
        let mut node = MCSNode::new();
        let mut logger = BUFFERED_LOGGER.lock(&mut node);

        *logger = Some(buffered_logger);
    }

    let _ = log::set_logger(&LOGGER);
    log::set_max_level(log::LevelFilter::Debug);

    while let Ok(msg) = rx.recv().await {
        awkernel_lib::console::print(&msg);
        awkernel_async_lib::r#yield().await;
    }
}
