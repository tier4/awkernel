use alloc::{boxed::Box, string::String};
use awkernel_async_lib::channel::bounded;
use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};
use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

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
    FallbackOnPanic(Box::pin(run_logger())).await
}

/// Switches the logger back to the raw console when the wrapped future panics.
///
/// If the buffered logger task panicked, it would be moved to the panicked
/// scheduler and nobody would drain the buffer, so all log output, including
/// the panic message, would silently disappear.
struct FallbackOnPanic<F>(Pin<Box<F>>);

impl<F: Future> Future for FallbackOnPanic<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // `guard` is dropped only when `poll` unwinds.
        let guard = RawConsoleOnUnwind;
        let result = self.get_mut().0.as_mut().poll(cx);
        core::mem::forget(guard);
        result
    }
}

struct RawConsoleOnUnwind;

impl Drop for RawConsoleOnUnwind {
    fn drop(&mut self) {
        awkernel_lib::logger::unset_buf_console();
        log::error!("buffered logger panicked; falling back to the raw console");
    }
}

async fn run_logger() {
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
