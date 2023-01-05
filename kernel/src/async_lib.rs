use core::time::Duration;
use futures::Future;

pub mod sleep;
pub mod yield_task;

pub trait Cancel: Future {
    fn cancel(self: core::pin::Pin<&mut Self>);
}

pub fn sleep(duration: Duration) -> sleep::Sleep {
    sleep::Sleep::new(duration.as_micros() as u64)
}

pub fn r#yield() -> yield_task::Yield {
    yield_task::Yield::new()
}
