use futures::Future;

pub mod sleep;

pub trait Cancel: Future {
    fn cancel(self: core::pin::Pin<&mut Self>);
}
