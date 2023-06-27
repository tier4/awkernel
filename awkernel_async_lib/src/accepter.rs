use crate::{
    anydict::{AnyDict, AnyDictResult},
    channel::unbounded::{self, Receiver, RecvErr, Sender},
    session_types::{self as S},
};
use alloc::{borrow::Cow, vec::Vec};
use core::{marker::PhantomData, sync::atomic::AtomicPtr};

/// Channel so that a server accepts a connection.

pub(crate) type TxRx = (Sender<AtomicPtr<u8>>, Receiver<AtomicPtr<u8>>);

/// `P` is a protocol of a server.
pub struct Accepter<P: 'static> {
    receiver: Option<Receiver<TxRx>>,
    name: Cow<'static, str>,
    drop_fn: fn(&mut Self),
    _phantom: PhantomData<fn(P)>,
}

impl<P> Accepter<P> {
    fn new(receiver: Receiver<TxRx>, name: Cow<'static, str>, drop_fn: fn(&mut Self)) -> Self {
        Self {
            receiver: Some(receiver),
            name,
            drop_fn,
            _phantom: Default::default(),
        }
    }

    /// Accept a connection.
    /// If accepted, it returns the name and a channel.
    pub async fn accept(&self) -> Result<S::Chan<(), P>, RecvErr> {
        let (tx, rx) = self.receiver.as_ref().unwrap().recv().await?;
        Ok(S::mk_chan(tx, rx))
    }

    pub fn get_name(&self) -> Cow<'static, str> {
        self.name.clone()
    }

    pub fn take(&mut self) -> Self {
        Accepter {
            receiver: self.receiver.take(),
            name: self.name.clone(),
            drop_fn: self.drop_fn,
            _phantom: PhantomData,
        }
    }
}

/// `P` is a protocol of a server and `P::Dual` is a protocol of a client.
struct Inner<P: 'static> {
    accepter: Option<Accepter<P>>,
    sender: Sender<TxRx>,
}

impl<P> Inner<P> {
    fn new_and_accepter(
        name: Cow<'static, str>,
        drop_fn: fn(&mut Accepter<P>),
    ) -> (Self, Accepter<P>) {
        let (tx, rx) = unbounded::new();
        let accepter = Accepter::new(rx, name, drop_fn);

        (
            Self {
                accepter: None,
                sender: tx,
            },
            accepter,
        )
    }

    fn new(name: Cow<'static, str>, drop_fn: fn(&mut Accepter<P>)) -> Self {
        let (tx, rx) = unbounded::new();
        Self {
            accepter: Some(Accepter::new(rx, name, drop_fn)),
            sender: tx,
        }
    }

    fn get_sender(&self) -> Result<Sender<TxRx>, &'static str> {
        if self.sender.is_terminated() {
            Err("channel has been terminated")
        } else {
            Ok(self.sender.clone())
        }
    }
}

pub struct Services {
    services: AnyDict,
}

impl Services {
    pub const fn new() -> Self {
        Self {
            services: AnyDict::new(),
        }
    }

    pub fn get_services(&self) -> Vec<Cow<'static, str>> {
        self.services.keys()
    }

    /// `P` is a protocol of a server.
    pub fn create_server<P: 'static>(
        &mut self,
        name: Cow<'static, str>,
        drop_fn: fn(&mut Accepter<P>),
    ) -> Result<Accepter<P>, &'static str> {
        match self.services.get_mut::<Inner<P>>(&name) {
            AnyDictResult::None => {
                let (inner, accepter) = Inner::new_and_accepter(name.clone(), drop_fn);
                self.services.insert(name, inner);
                Ok(accepter)
            }
            AnyDictResult::Ok(s) => s
                .accepter
                .take()
                .ok_or("create_server: a server has been already created"),
            AnyDictResult::TypeError => Err("create_server: typing error"),
        }
    }

    /// `P` is a protocol of a client.
    pub fn create_client<P: S::HasDual>(
        &mut self,
        name: Cow<'static, str>,
        drop_fn: fn(&mut Accepter<P::Dual>),
    ) -> Result<Sender<TxRx>, &'static str> {
        match self.services.get_mut::<Inner<P::Dual>>(&name) {
            AnyDictResult::None => {
                let inner = Inner::<P::Dual>::new(name.clone(), drop_fn);
                let tx = inner.get_sender();
                self.services.insert(name, inner);
                tx
            }
            AnyDictResult::Ok(s) => s.get_sender(),
            AnyDictResult::TypeError => Err("create_client: typing error"),
        }
    }

    pub fn set_accepter<P>(&mut self, accepter: Accepter<P>) {
        match self.services.get_mut::<Inner<P>>(&accepter.get_name()) {
            AnyDictResult::Ok(s) => {
                if s.accepter.is_none() {
                    s.accepter = Some(accepter);
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        }
    }
}
