//! # Oneshot channel
//!
//! ```
//! use t4os_async_lib::channel::oneshot;
//!
//! let (tx, rx) = oneshot::channel();
//!
//! tx.send(10).unwrap();
//!
//! let task = async move {
//!     let _data = rx.await.unwrap();
//! };
//! ```

pub use futures::channel::*;

pub mod bounded;
pub mod unbounded;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_oneshot() {
        let (tx, rx) = oneshot::channel();

        tx.send(10).unwrap();

        let task = async move {
            let _data = rx.await.unwrap();
        };

        let tasks = crate::mini_task::Tasks::new();
        tasks.spawn(task);

        tasks.run();
    }
}
