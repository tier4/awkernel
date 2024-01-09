//! Session types for Rust.
//!
//! # Example
//!
//! ```
//! use awkernel_async_lib::{session_types::*, scheduler::SchedulerType};
//!
//! // Define protocol.
//! type Server = Recv<u64, Send<bool, Eps>>;
//! type Client = <Server as HasDual>::Dual;
//!
//! // Server.
//! async fn srv(c: Chan<(), Server>) {
//!     let (c, n) = c.recv().await;
//!     let c = if n % 2 == 0 {
//!         c.send(true).await
//!     } else {
//!         c.send(false).await
//!     };
//!     c.close();
//! }
//!
//! // Client.
//! async fn cli(c: Chan<(), Client>) {
//!     let c = c.send(9).await;
//!     let (c, _result) = c.recv().await;
//!     c.close();
//! }
//!
//! let _ = async {
//!     let (server, client) = session_channel::<Server>();
//!
//!     awkernel_async_lib::spawn("server".into(), async { srv(server).await; }, SchedulerType::FIFO).await;
//!     awkernel_async_lib::spawn("client".into(), async { cli(client).await; }, SchedulerType::FIFO).await;
//! };
//! ```
//!
//! # LICENSE
//!
//! ```text
//! The MIT License (MIT)
//!
//! Copyright (c) 2015 Thomas Bracht Laumann Jespersen, Philip Munksgaard
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.
//! ```

#![cfg_attr(feature = "cargo-clippy", allow(clippy::double_must_use))]
#![cfg_attr(feature = "cargo-clippy", allow(clippy::type_complexity))]
use crate::{
    channel::unbounded::{self, Receiver, Sender},
    r#yield,
};
use alloc::{boxed::Box, vec::Vec};
use core::{
    marker::{self, PhantomData},
    mem, ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

pub use Branch::*;

/// A session typed channel. `P` is the protocol and `E` is the environment,
/// containing potential recursion targets
#[must_use]
pub struct Chan<E, P>(
    Sender<AtomicPtr<u8>>,
    Receiver<AtomicPtr<u8>>,
    PhantomData<(E, P)>,
);

unsafe impl<E: marker::Send, P: marker::Send> marker::Send for Chan<E, P> {}
unsafe impl<E: marker::Sync, P: marker::Sync> Sync for Chan<E, P> {}

unsafe fn write_chan<A: marker::Send + 'static, E, P>(Chan(tx, _, _): &Chan<E, P>, x: A) {
    let ptr = AtomicPtr::new(Box::into_raw(Box::new(x)) as *mut _);
    tx.send_no_yield(ptr).unwrap();
}

async unsafe fn read_chan<A: marker::Send + 'static, E, P>(Chan(_, rx, _): &Chan<E, P>) -> A {
    let ptr = rx.recv().await.unwrap();
    *Box::from_raw(ptr.load(Ordering::Relaxed) as *mut A)
}

unsafe fn try_read_chan<A: marker::Send + 'static, E, P>(Chan(_, rx, _): &Chan<E, P>) -> Option<A> {
    match rx.try_recv() {
        Ok(a) => Some(*Box::from_raw(a.load(Ordering::Relaxed) as *mut A)),
        Err(_) => None,
    }
}

/// Peano numbers: Zero
#[allow(missing_copy_implementations)]
pub struct Z;

/// Peano numbers: Increment
pub struct S<N>(PhantomData<N>);

/// End of communication session (epsilon)
#[allow(missing_copy_implementations)]
pub struct Eps;

/// Receive `A`, then `P`
pub struct Recv<A, P>(PhantomData<(A, P)>);

/// Send `A`, then `P`
pub struct Send<A, P>(PhantomData<(A, P)>);

/// Active choice between `P` and `Q`
pub struct Choose<P, Q>(PhantomData<(P, Q)>);

/// Passive choice (offer) between `P` and `Q`
pub struct Offer<P, Q>(PhantomData<(P, Q)>);

/// Enter a recursive environment
pub struct Rec<P>(PhantomData<P>);

/// Recurse. N indicates how many layers of the recursive environment we recurse
/// out of.
pub struct Var<N>(PhantomData<N>);

/// The HasDual trait defines the dual relationship between protocols.
///
/// Any valid protocol has a corresponding dual.
///
/// This trait is sealed and cannot be implemented outside of session-types
pub trait HasDual: private::Sealed {
    type Dual;
}

impl HasDual for Eps {
    type Dual = Eps;
}

impl<A, P: HasDual> HasDual for Send<A, P> {
    type Dual = Recv<A, P::Dual>;
}

impl<A, P: HasDual> HasDual for Recv<A, P> {
    type Dual = Send<A, P::Dual>;
}

impl<P: HasDual, Q: HasDual> HasDual for Choose<P, Q> {
    type Dual = Offer<P::Dual, Q::Dual>;
}

impl<P: HasDual, Q: HasDual> HasDual for Offer<P, Q> {
    type Dual = Choose<P::Dual, Q::Dual>;
}

impl HasDual for Var<Z> {
    type Dual = Var<Z>;
}

impl<N> HasDual for Var<S<N>> {
    type Dual = Var<S<N>>;
}

impl<P: HasDual> HasDual for Rec<P> {
    type Dual = Rec<P::Dual>;
}

pub enum Branch<L, R> {
    Left(L),
    Right(R),
}

impl<E, P> Drop for Chan<E, P> {
    fn drop(&mut self) {
        panic!("Session channel prematurely dropped");
    }
}

impl<E> Chan<E, Eps> {
    /// Close a channel. Should always be used at the end of your program.
    pub fn close(self) {
        // This method cleans up the channel without running the panicky destructor
        // In essence, it calls the drop glue bypassing the `Drop::drop` method

        let this = mem::ManuallyDrop::new(self);

        let sender = unsafe { ptr::read(&(this).0 as *const _) };
        let receiver = unsafe { ptr::read(&(this).1 as *const _) };

        drop(sender);
        drop(receiver); // drop them
    }
}

impl<E, P> Chan<E, P> {
    unsafe fn cast<E2, P2>(self) -> Chan<E2, P2> {
        let this = mem::ManuallyDrop::new(self);
        Chan(
            ptr::read(&(this).0 as *const _),
            ptr::read(&(this).1 as *const _),
            PhantomData,
        )
    }
}

impl<E, P, A: marker::Send + 'static> Chan<E, Send<A, P>> {
    /// Send a value of type `A` over the channel. Returns a channel with
    /// protocol `P`
    #[must_use]
    pub async fn send(self, v: A) -> Chan<E, P> {
        unsafe {
            write_chan(&self, v);
            r#yield().await;
            self.cast()
        }
    }
}

impl<E, P, A: marker::Send + 'static> Chan<E, Recv<A, P>> {
    /// Receives a value of type `A` from the channel. Returns a tuple
    /// containing the resulting channel and the received value.
    #[must_use]
    pub async fn recv(self) -> (Chan<E, P>, A) {
        unsafe {
            let v = read_chan(&self).await;
            (self.cast(), v)
        }
    }

    /// Non-blocking receive.
    #[must_use]
    pub fn try_recv(self) -> Result<(Chan<E, P>, A), Self> {
        unsafe {
            if let Some(v) = try_read_chan(&self) {
                Ok((self.cast(), v))
            } else {
                Err(self)
            }
        }
    }
}

impl<E, P, Q> Chan<E, Choose<P, Q>> {
    /// Perform an active choice, selecting protocol `P`.
    #[must_use]
    pub async fn sel1(self) -> Chan<E, P> {
        unsafe {
            write_chan(&self, true);
            r#yield().await;
            self.cast()
        }
    }

    /// Perform an active choice, selecting protocol `Q`.
    #[must_use]
    pub async fn sel2(self) -> Chan<E, Q> {
        unsafe {
            write_chan(&self, false);
            r#yield().await;
            self.cast()
        }
    }

    /// Perform an active choice, selecting protocol `Q`.
    #[must_use]
    fn sel2_ny(self) -> Chan<E, Q> {
        unsafe {
            write_chan(&self, false);
            self.cast()
        }
    }
}

/// Convenience function. This is identical to `.sel2()`
impl<Z, A, B> Chan<Z, Choose<A, B>> {
    #[must_use]
    pub async fn skip(self) -> Chan<Z, B> {
        let result = self.sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function. This is identical to `.sel2().sel2()`
impl<Z, A, B, C> Chan<Z, Choose<A, Choose<B, C>>> {
    #[must_use]
    pub async fn skip2(self) -> Chan<Z, C> {
        let result = self.sel2_ny().sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2()`
impl<Z, A, B, C, D> Chan<Z, Choose<A, Choose<B, Choose<C, D>>>> {
    #[must_use]
    pub async fn skip3(self) -> Chan<Z, D> {
        let result = self.sel2_ny().sel2_ny().sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2().sel2()`
impl<Z, A, B, C, D, E> Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, E>>>>> {
    #[must_use]
    pub async fn skip4(self) -> Chan<Z, E> {
        let result = self.sel2_ny().sel2_ny().sel2_ny().sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2().sel2().sel2()`
impl<Z, A, B, C, D, E, F> Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, F>>>>>> {
    #[must_use]
    pub async fn skip5(self) -> Chan<Z, F> {
        let result = self.sel2_ny().sel2_ny().sel2_ny().sel2_ny().sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function.
impl<Z, A, B, C, D, E, F, G>
    Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, Choose<F, G>>>>>>>
{
    #[must_use]
    pub async fn skip6(self) -> Chan<Z, G> {
        let result = self
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny();
        r#yield().await;
        result
    }
}

/// Convenience function.
impl<Z, A, B, C, D, E, F, G, H>
    Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, Choose<F, Choose<G, H>>>>>>>>
{
    #[must_use]
    pub async fn skip7(self) -> Chan<Z, H> {
        let result = self
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny()
            .sel2_ny();
        r#yield().await;
        result
    }
}

impl<E, P, Q> Chan<E, Offer<P, Q>> {
    /// Passive choice. This allows the other end of the channel to select one
    /// of two options for continuing the protocol: either `P` or `Q`.
    #[must_use]
    pub async fn offer(self) -> Branch<Chan<E, P>, Chan<E, Q>> {
        unsafe {
            let b = read_chan(&self).await;
            if b {
                Left(self.cast())
            } else {
                Right(self.cast())
            }
        }
    }

    /// Poll for choice.
    #[must_use]
    pub fn try_offer(self) -> Result<Branch<Chan<E, P>, Chan<E, Q>>, Self> {
        unsafe {
            if let Some(b) = try_read_chan(&self) {
                if b {
                    Ok(Left(self.cast()))
                } else {
                    Ok(Right(self.cast()))
                }
            } else {
                Err(self)
            }
        }
    }
}

impl<E, P> Chan<E, Rec<P>> {
    /// Enter a recursive environment, putting the current environment on the
    /// top of the environment stack.
    #[must_use]
    pub fn enter(self) -> Chan<(P, E), P> {
        unsafe { self.cast() }
    }
}

impl<E, P> Chan<(P, E), Var<Z>> {
    /// Recurse to the environment on the top of the environment stack.
    #[must_use]
    pub fn zero(self) -> Chan<(P, E), P> {
        unsafe { self.cast() }
    }
}

impl<E, P, N> Chan<(P, E), Var<S<N>>> {
    /// Pop the top environment from the environment stack.
    #[must_use]
    pub fn succ(self) -> Chan<E, Var<N>> {
        unsafe { self.cast() }
    }
}

/// Heterogeneous selection structure for channels
///
/// This builds a structure of channels that we wish to select over. This is
/// structured in a way such that the channels selected over cannot be
/// interacted with (consumed) as long as the borrowing ChanSelect object
/// exists. This is necessary to ensure memory safety.
///
/// The type parameter T is a return type, ie we store a value of some type T
/// that is returned in case its associated channels is selected on `wait()`
pub struct ChanSelect<'c> {
    receivers: Vec<&'c Receiver<AtomicPtr<u8>>>,
}

impl<'c> ChanSelect<'c> {
    pub fn new() -> ChanSelect<'c> {
        ChanSelect {
            receivers: Vec::new(),
        }
    }

    /// Add a channel whose next step is `Recv`
    ///
    /// Once a channel has been added it cannot be interacted with as long as it
    /// is borrowed here (by virtue of borrow checking and lifetimes).
    pub fn add_recv<E, P, A: marker::Send>(&mut self, chan: &'c Chan<E, Recv<A, P>>) {
        let Chan(_, rx, _) = chan;
        self.receivers.push(rx);
    }

    pub fn add_offer<E, P, Q>(&mut self, chan: &'c Chan<E, Offer<P, Q>>) {
        let Chan(_, rx, _) = chan;
        self.receivers.push(rx);
    }

    /// How many channels are there in the structure?
    pub fn len(&self) -> usize {
        self.receivers.len()
    }

    pub fn is_empty(&self) -> bool {
        self.receivers.is_empty()
    }
}

impl<'c> Default for ChanSelect<'c> {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns two session channels
#[must_use]
pub fn session_channel<P: HasDual>() -> (Chan<(), P>, Chan<(), P::Dual>) {
    let (tx1, rx1) = unbounded::new();
    let (tx2, rx2) = unbounded::new();

    let c1 = Chan(tx1, rx2, PhantomData);
    let c2 = Chan(tx2, rx1, PhantomData);

    (c1, c2)
}

/// Create a channel.
pub(crate) fn mk_chan<P>(tx: Sender<AtomicPtr<u8>>, rx: Receiver<AtomicPtr<u8>>) -> Chan<(), P> {
    Chan(tx, rx, PhantomData)
}

mod private {
    use super::*;
    pub trait Sealed {}

    // Impl for all exported protocol types
    impl Sealed for Eps {}
    impl<A, P> Sealed for Send<A, P> {}
    impl<A, P> Sealed for Recv<A, P> {}
    impl<P, Q> Sealed for Choose<P, Q> {}
    impl<P, Q> Sealed for Offer<P, Q> {}
    impl<Z> Sealed for Var<Z> {}
    impl<P> Sealed for Rec<P> {}
}

/// This macro is convenient for server-like protocols of the form:
///
/// `Offer<A, Offer<B, Offer<C, ... >>>`
///
/// # Examples
///
/// Assume we have a protocol `Offer<Recv<u64, Eps>, Offer<Recv<String, Eps>,Eps>>>`
/// we can use the `offer!` macro as follows:
///
/// ```rust
/// use awkernel_async_lib::session_types::*;
/// use awkernel_async_lib::*;
///
/// type SrvProtocol = Offer<Recv<u64, Eps>, Offer<Recv<String, Eps>, Eps>>;
/// type CliProtocol = <SrvProtocol as HasDual>::Dual;
///
/// async fn srv(c: Chan<(), SrvProtocol>) {
///     offer! { c,
///         Number => {
///             let (c, n) = c.recv().await;
///             assert_eq!(42, n);
///             c.close();
///         },
///         String => {
///             c.recv().await.0.close();
///         },
///         Quit => {
///             c.close();
///         }
///     }
/// }
///
/// async fn cli(c: Chan<(), CliProtocol>) {
///     c.sel1().await.send(42).await.close();
/// }
/// ```
///
/// The identifiers on the left-hand side of the arrows have no semantic
/// meaning, they only provide a meaningful name for the reader.
#[macro_export]
macro_rules! offer {
    (
        $id:ident, $branch:ident => $code:expr, $($t:tt)+
    ) => (
        match $id.offer().await {
            $crate::session_types::Left($id) => $code,
            $crate::session_types::Right($id) => offer!{ $id, $($t)+ }
        }
    );
    (
        $id:ident, $branch:ident => $code:expr
    ) => (
        $code
    )
}

/// Returns the channel unchanged on `TryRecvError::Empty`.
#[macro_export]
macro_rules! try_offer {
    (
        $id:ident, $branch:ident => $code:expr, $($t:tt)+
    ) => (
        match $id.try_offer() {
            Ok($crate::session_types::Left($id)) => $code,
            Ok($crate::session_types::Right($id)) => try_offer!{ $id, $($t)+ },
            Err($id) => Err($id)
        }
    );
    (
        $id:ident, $branch:ident => $code:expr
    ) => (
        $code
    )
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;
    use crate::mini_task;

    #[test]
    fn proxy() {
        type Server = Recv<u64, Eps>;
        type SrvChan = Chan<(), Server>;
        type ProxySrv1 = Recv<SrvChan, Eps>;
        type ProxyCli1 = <ProxySrv1 as HasDual>::Dual;
        type ProxySrv2 = Send<SrvChan, Eps>;
        type ProxyCli2 = <ProxySrv2 as HasDual>::Dual;

        let (pr_srv1, pr_cli1) = session_channel::<ProxySrv1>();
        let (pr_srv2, pr_cli2) = session_channel::<ProxySrv2>();

        async fn cli(c: Chan<(), ProxyCli1>) {
            let (server, client) = session_channel::<Server>();
            let pr = c.send(server).await;
            pr.close();

            let c = client.send(123).await;
            c.close();
        }

        async fn srv(c: Chan<(), ProxyCli2>) {
            let (pr, server) = c.recv().await;
            pr.close();

            let (c, _result) = server.recv().await;
            c.close();
        }

        async fn proxy(c1: Chan<(), ProxySrv1>, c2: Chan<(), ProxySrv2>) {
            let (c1, server) = c1.recv().await;
            c1.close();

            let c2 = c2.send(server).await;
            c2.close();
        }

        let tasks = mini_task::Tasks::new();
        tasks.spawn(async move { cli(pr_cli1).await });
        tasks.spawn(async move { srv(pr_cli2).await });
        tasks.spawn(async move { proxy(pr_srv1, pr_srv2).await });

        tasks.run();
    }

    #[test]
    fn test_offer() {
        type Server = Offer<Recv<u64, Eps>, Recv<String, Eps>>;
        type Client = <Server as HasDual>::Dual;

        async fn srv(c: Chan<(), Server>) {
            offer! {c,
                Number => {
                    let (c, _result) = c.recv().await;
                    c.close();
                },
                String => {
                    let (c, _result) = c.recv().await;
                    c.close();
                }
            }
        }

        async fn cli(c: Chan<(), Client>) {
            let c = c.sel2().await;
            let c = c.send("Hello, world!".to_string()).await;
            c.close();
        }

        let (server, client) = session_channel::<Server>();

        let tasks = mini_task::Tasks::new();
        tasks.spawn(async move { srv(server).await });
        tasks.spawn(async move { cli(client).await });

        tasks.run();
    }

    #[test]
    #[allow(unused_variables)]
    #[allow(dead_code)]
    fn recursive_protocol() {
        type Server = Rec<Recv<u64, Send<bool, Var<Z>>>>;
        type Client = <Server as HasDual>::Dual;

        async fn srv(chan: Chan<(), Server>) {
            let mut chan = chan.enter();
            loop {
                let (c, n) = chan.recv().await;

                if n % 2 == 0 {
                    chan = c.send(true).await.zero();
                } else {
                    chan = c.send(false).await.zero();
                }
            }
        }

        async fn cli(chan: Chan<(), Client>) {
            let mut chan = chan.enter();
            loop {
                let c = chan.send(9).await;
                let (c, _result) = c.recv().await;
                chan = c.zero();
            }
        }
    }

    #[test]
    fn simple_protocol() {
        type Server = Recv<u64, Send<bool, Eps>>;
        type Client = <Server as HasDual>::Dual;

        async fn srv(c: Chan<(), Server>) {
            let (c, n) = c.recv().await;
            let c = if n % 2 == 0 {
                c.send(true).await
            } else {
                c.send(false).await
            };
            c.close();
        }

        async fn cli(c: Chan<(), Client>) {
            let c = c.send(9).await;
            let (c, _result) = c.recv().await;
            c.close();
        }

        let (server, client) = session_channel::<Server>();

        let tasks = mini_task::Tasks::new();
        tasks.spawn(async move { srv(server).await });
        tasks.spawn(async move { cli(client).await });

        tasks.run();
    }
}
