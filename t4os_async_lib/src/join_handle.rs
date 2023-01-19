use futures::channel::oneshot::{Canceled, Receiver};

pub struct JoinHandle<T> {
    rx: Receiver<T>,
}

impl<T> JoinHandle<T> {
    pub fn new(rx: Receiver<T>) -> Self {
        Self { rx }
    }

    pub async fn join(self) -> Result<T, Canceled> {
        self.rx.await
    }
}
