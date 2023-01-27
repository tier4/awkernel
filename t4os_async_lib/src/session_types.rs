//! > The MIT License (MIT)
//! >
//! > Copyright (c) 2015 Thomas Bracht Laumann Jespersen, Philip Munksgaard
//! >
//! > Permission is hereby granted, free of charge, to any person obtaining a copy
//! > of this software and associated documentation files (the "Software"), to deal
//! > in the Software without restriction, including without limitation the rights
//! > to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! > copies of the Software, and to permit persons to whom the Software is
//! > furnished to do so, subject to the following conditions:
//! >
//! > The above copyright notice and this permission notice shall be included in all
//! > copies or substantial portions of the Software.
//! >
//! > THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! > IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! > FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! > AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! > LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! > OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! > SOFTWARE.

#![cfg_attr(feature = "cargo-clippy", allow(clippy::double_must_use))]
#![cfg_attr(feature = "cargo-clippy", allow(clippy::type_complexity))]
use alloc::{boxed::Box, collections::VecDeque, sync::Arc, vec::Vec};
use core::{
    marker::{self, PhantomData},
    mem, ptr,
    task::{Poll, Waker},
};
use futures::Future;
use synctools::mcs::{MCSLock, MCSNode};

pub use Branch::*;

use crate::r#yield;

struct Channel {
    queue: VecDeque<*mut u8>,
    waker_receiver: Option<Waker>,
    finished: bool,
}

struct Sender {
    chan: Arc<MCSLock<Channel>>,
}

impl Sender {
    async fn send(&self, data: *mut u8) -> Result<(), &'static str> {
        {
            let mut node = MCSNode::new();
            let mut chan = self.chan.lock(&mut node);

            if chan.finished {
                return Err("Connection closed");
            }

            chan.queue.push_back(data);
        }

        r#yield().await;
        Ok(())
    }
}

impl Drop for Sender {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        chan.finished = true;
        if let Some(waker) = chan.waker_receiver.take() {
            waker.wake();
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum RecvErr {
    ChannelClosed,
    NoData,
}

struct Receiver {
    chan: Arc<MCSLock<Channel>>,
}

impl Receiver {
    async fn recv(&self) -> Result<*mut u8, RecvErr> {
        let receiver = AsyncReceiver { receiver: self };
        receiver.await
    }

    fn try_recv(&self) -> Result<*mut u8, RecvErr> {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        if let Some(e) = chan.queue.pop_front() {
            Ok(e)
        } else if chan.finished {
            Err(RecvErr::ChannelClosed)
        } else {
            Err(RecvErr::NoData)
        }
    }
}

impl Drop for Receiver {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        chan.finished = true;
    }
}

struct AsyncReceiver<'a> {
    receiver: &'a Receiver,
}

impl<'a> Future for AsyncReceiver<'a> {
    type Output = Result<*mut u8, RecvErr>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let mut node = MCSNode::new();
        let mut chan = self.receiver.chan.lock(&mut node);

        if let Some(data) = chan.queue.pop_front() {
            Poll::Ready(Ok(data))
        } else if chan.finished {
            Poll::Ready(Err(RecvErr::ChannelClosed))
        } else {
            chan.waker_receiver = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

/// A session typed channel. `P` is the protocol and `E` is the environment,
/// containing potential recursion targets
#[must_use]
pub struct Chan<E, P>(Sender, Receiver, PhantomData<(E, P)>);

unsafe impl<E: marker::Send, P: marker::Send> marker::Send for Chan<E, P> {}

async unsafe fn write_chan<A: marker::Send + 'static, E, P>(Chan(tx, _, _): &Chan<E, P>, x: A) {
    tx.send(Box::into_raw(Box::new(x)) as *mut _).await.unwrap()
}

async unsafe fn read_chan<A: marker::Send + 'static, E, P>(Chan(_, rx, _): &Chan<E, P>) -> A {
    *Box::from_raw(rx.recv().await.unwrap() as *mut A)
}

unsafe fn try_read_chan<A: marker::Send + 'static, E, P>(Chan(_, rx, _): &Chan<E, P>) -> Option<A> {
    match rx.try_recv() {
        Ok(a) => Some(*Box::from_raw(a as *mut A)),
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
            write_chan(&self, v).await;
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
            write_chan(&self, true).await;
            self.cast()
        }
    }

    /// Perform an active choice, selecting protocol `Q`.
    #[must_use]
    pub async fn sel2(self) -> Chan<E, Q> {
        unsafe {
            write_chan(&self, false).await;
            self.cast()
        }
    }
}

/// Convenience function. This is identical to `.sel2()`
impl<Z, A, B> Chan<Z, Choose<A, B>> {
    #[must_use]
    pub async fn skip(self) -> Chan<Z, B> {
        self.sel2().await
    }
}

/// Convenience function. This is identical to `.sel2().sel2()`
impl<Z, A, B, C> Chan<Z, Choose<A, Choose<B, C>>> {
    #[must_use]
    pub async fn skip2(self) -> Chan<Z, C> {
        self.sel2().await.sel2().await
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2()`
impl<Z, A, B, C, D> Chan<Z, Choose<A, Choose<B, Choose<C, D>>>> {
    #[must_use]
    pub async fn skip3(self) -> Chan<Z, D> {
        self.sel2().await.sel2().await.sel2().await
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2().sel2()`
impl<Z, A, B, C, D, E> Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, E>>>>> {
    #[must_use]
    pub async fn skip4(self) -> Chan<Z, E> {
        self.sel2().await.sel2().await.sel2().await.sel2().await
    }
}

/// Convenience function. This is identical to `.sel2().sel2().sel2().sel2().sel2()`
impl<Z, A, B, C, D, E, F> Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, F>>>>>> {
    #[must_use]
    pub async fn skip5(self) -> Chan<Z, F> {
        self.sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
    }
}

/// Convenience function.
impl<Z, A, B, C, D, E, F, G>
    Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, Choose<F, G>>>>>>>
{
    #[must_use]
    pub async fn skip6(self) -> Chan<Z, G> {
        self.sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
    }
}

/// Convenience function.
impl<Z, A, B, C, D, E, F, G, H>
    Chan<Z, Choose<A, Choose<B, Choose<C, Choose<D, Choose<E, Choose<F, Choose<G, H>>>>>>>>
{
    #[must_use]
    pub async fn skip7(self) -> Chan<Z, H> {
        self.sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
            .sel2()
            .await
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
    receivers: Vec<&'c Receiver>,
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

fn channel() -> (Sender, Receiver) {
    let chan = Channel {
        queue: Default::default(),
        waker_receiver: None,
        finished: false,
    };

    let chan = Arc::new(MCSLock::new(chan));

    let sender = Sender { chan: chan.clone() };
    let receiver = Receiver { chan };

    (sender, receiver)
}

/// Returns two session channels
#[must_use]
pub fn session_channel<P: HasDual>() -> (Chan<(), P>, Chan<(), P::Dual>) {
    let (tx1, rx1) = channel();
    let (tx2, rx2) = channel();

    let c1 = Chan(tx1, rx2, PhantomData);
    let c2 = Chan(tx2, rx1, PhantomData);

    (c1, c2)
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
/// extern crate session_types;
/// use session_types::*;
/// use std::thread::spawn;
///
/// fn srv(c: Chan<(), Offer<Recv<u64, Eps>, Offer<Recv<String, Eps>, Eps>>>) {
///     offer! { c,
///         Number => {
///             let (c, n) = c.recv();
///             assert_eq!(42, n);
///             c.close();
///         },
///         String => {
///             c.recv().0.close();
///         },
///         Quit => {
///             c.close();
///         }
///     }
/// }
///
/// fn cli(c: Chan<(), Choose<Send<u64, Eps>, Choose<Send<String, Eps>, Eps>>>) {
///     c.sel1().send(42).close();
/// }
///
/// fn main() {
///     let (s, c) = session_channel();
///     spawn(move|| cli(c));
///     srv(s);
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
        match $id.offer() {
            $crate::Left($id) => $code,
            $crate::Right($id) => offer!{ $id, $($t)+ }
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
            Ok($crate::Left($id)) => $code,
            Ok($crate::Right($id)) => try_offer!{ $id, $($t)+ },
            Err($id) => Err($id)
        }
    );
    (
        $id:ident, $branch:ident => $code:expr
    ) => (
        $code
    )
}
