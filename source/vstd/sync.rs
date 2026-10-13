//! Blocking synchronization primitives backed by `std::sync`, specified by a
//! user-chosen predicate on the protected or transmitted values.
//!
//! Unlike [`RwLock`](crate::rwlock::RwLock), which is verified on top of atomics
//! and spins while waiting, these wrap the standard library and block.
#![allow(unused_imports)]
use super::prelude::*;
use super::rwlock::RwLockPredicate;
use core::marker::PhantomData;

verus! {

/// A blocking mutex whose value always satisfies `pred.inv`.
/// (Wrapper around [`std::sync::Mutex`](https://doc.rust-lang.org/std/sync/struct.Mutex.html).)
///
/// The value is moved out by [`lock`](Mutex::lock) and must be moved back in by
/// [`MutexGuard::release`], which requires the predicate to hold again.
///
/// **Warning:** The lock is _NOT_ released if the guard is dropped without calling
/// [`MutexGuard::release`]; later calls to `lock` will block forever, and
/// [`into_inner`](Mutex::into_inner) will abort.
#[verifier::external_body]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(Pred)]
pub struct Mutex<V, Pred: RwLockPredicate<V>> {
    inner: std::sync::Mutex<Option<V>>,
    _pred: PhantomData<fn (Pred)>,
}

/// Handle for a locked [`Mutex`]. See [`Mutex::lock`].
#[verifier::external_body]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(Pred)]
pub struct MutexGuard<'a, V, Pred: RwLockPredicate<V>> {
    guard: Option<std::sync::MutexGuard<'a, Option<V>>>,
    _pred: PhantomData<fn (Pred)>,
}

impl<V, Pred: RwLockPredicate<V>> Mutex<V, Pred> {
    /// Predicate configured for this lock instance.
    pub uninterp spec fn pred(&self) -> Pred;

    pub open spec fn inv(&self, val: V) -> bool {
        self.pred().inv(val)
    }

    #[verifier::external_body]
    pub fn new(val: V, Ghost(pred): Ghost<Pred>) -> (s: Self)
        requires
            pred.inv(val),
        ensures
            s.pred() == pred,
    {
        Mutex { inner: std::sync::Mutex::new(Some(val)), _pred: PhantomData }
    }

    /// Blocks until the lock is acquired, then moves the value out.
    #[verifier::external_body]
    pub fn lock(&self) -> (ret: (V, MutexGuard<'_, V, Pred>))
        ensures
            self.inv(ret.0),
            ret.1.pred() == self.pred(),
    {
        let mut guard = lock_ignoring_poison(&self.inner);
        let val = take_or_abort(&mut guard);
        (val, MutexGuard { guard: Some(guard), _pred: PhantomData })
    }

    #[verifier::external_body]
    pub fn into_inner(self) -> (v: V)
        ensures
            self.inv(v),
    {
        match self.inner.into_inner() {
            Ok(Some(v)) => v,
            _ => std::process::abort(),
        }
    }
}

impl<'a, V, Pred: RwLockPredicate<V>> MutexGuard<'a, V, Pred> {
    /// Predicate of the [`Mutex`] this guard locks.
    pub uninterp spec fn pred(&self) -> Pred;

    /// Moves the value back in and releases the lock.
    #[verifier::external_body]
    pub fn release(mut self, new_val: V)
        requires
            self.pred().inv(new_val),
    {
        let mut guard = self.guard.take().unwrap();
        *guard = Some(new_val);
    }
}

/// A condition variable for use with [`Mutex`].
/// (Wrapper around [`std::sync::Condvar`](https://doc.rust-lang.org/std/sync/struct.Condvar.html).)
#[verifier::external_body]
pub struct Condvar {
    inner: std::sync::Condvar,
}

impl Condvar {
    #[verifier::external_body]
    pub fn new() -> Condvar {
        Condvar { inner: std::sync::Condvar::new() }
    }

    /// Moves `val` back into the mutex, blocks until notified (or spuriously woken),
    /// then moves the current value out again.
    #[verifier::external_body]
    pub fn wait<'a, V, Pred: RwLockPredicate<V>>(
        &self,
        mut guard: MutexGuard<'a, V, Pred>,
        val: V,
    ) -> (ret: (V, MutexGuard<'a, V, Pred>))
        requires
            guard.pred().inv(val),
        ensures
            guard.pred().inv(ret.0),
            ret.1.pred() == guard.pred(),
    {
        let mut g = guard.guard.take().unwrap();
        *g = Some(val);
        let mut g = match self.inner.wait(g) {
            Ok(g) => g,
            Err(e) => e.into_inner(),
        };
        let val = take_or_abort(&mut g);
        (val, MutexGuard { guard: Some(g), _pred: PhantomData })
    }

    #[verifier::external_body]
    pub fn notify_one(&self) {
        self.inner.notify_one()
    }

    #[verifier::external_body]
    pub fn notify_all(&self) {
        self.inner.notify_all()
    }
}

/// Sending half of a [`channel`].
/// (Wrapper around [`std::sync::mpsc::Sender`](https://doc.rust-lang.org/std/sync/mpsc/struct.Sender.html).)
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(Pred)]
pub struct Sender<T, Pred: RwLockPredicate<T>> {
    inner: std::sync::mpsc::Sender<T>,
    _pred: PhantomData<fn (Pred)>,
}

/// Receiving half of a [`channel`].
/// (Wrapper around [`std::sync::mpsc::Receiver`](https://doc.rust-lang.org/std/sync/mpsc/struct.Receiver.html).)
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(Pred)]
pub struct Receiver<T, Pred: RwLockPredicate<T>> {
    inner: std::sync::mpsc::Receiver<T>,
    _pred: PhantomData<fn (Pred)>,
}

/// Creates a channel whose messages all satisfy `pred.inv`.
/// (Wrapper around [`std::sync::mpsc::channel`](https://doc.rust-lang.org/std/sync/mpsc/fn.channel.html).)
#[verifier::external_body]
pub fn channel<T, Pred: RwLockPredicate<T>>(Ghost(pred): Ghost<Pred>) -> (ret: (
    Sender<T, Pred>,
    Receiver<T, Pred>,
))
    ensures
        ret.0.pred() == pred,
        ret.1.pred() == pred,
{
    let (tx, rx) = std::sync::mpsc::channel();
    (Sender { inner: tx, _pred: PhantomData }, Receiver { inner: rx, _pred: PhantomData })
}

impl<T, Pred: RwLockPredicate<T>> Sender<T, Pred> {
    pub uninterp spec fn pred(&self) -> Pred;

    /// Sends a value. Fails, returning the value, if the receiver has been dropped.
    #[verifier::external_body]
    pub fn send(&self, t: T) -> (ret: Result<(), T>)
        requires
            self.pred().inv(t),
        ensures
            ret matches Err(u) ==> u == t,
    {
        self.inner.send(t).map_err(|e| e.0)
    }
}

impl<T, Pred: RwLockPredicate<T>> Clone for Sender<T, Pred> {
    #[verifier::external_body]
    fn clone(&self) -> (s: Self)
        ensures
            s.pred() == self.pred(),
    {
        Sender { inner: self.inner.clone(), _pred: PhantomData }
    }
}

impl<T, Pred: RwLockPredicate<T>> Receiver<T, Pred> {
    pub uninterp spec fn pred(&self) -> Pred;

    /// Blocks until a value is received. Fails if all senders have been dropped.
    #[verifier::external_body]
    pub fn recv(&self) -> (ret: Result<T, ()>)
        ensures
            ret matches Ok(t) ==> self.pred().inv(t),
    {
        self.inner.recv().map_err(|_| ())
    }

    /// Returns a value if one is available, without blocking.
    #[verifier::external_body]
    pub fn try_recv(&self) -> (ret: Option<T>)
        ensures
            ret matches Some(t) ==> self.pred().inv(t),
    {
        self.inner.try_recv().ok()
    }
}

} // verus!
fn lock_ignoring_poison<V>(m: &std::sync::Mutex<V>) -> std::sync::MutexGuard<'_, V> {
    match m.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    }
}

// The value is only absent while a guard holds it, and guards never unlock
// without restoring it (see `Drop`), so this cannot fail.
fn take_or_abort<V>(guard: &mut std::sync::MutexGuard<'_, Option<V>>) -> V {
    match guard.take() {
        Some(v) => v,
        None => std::process::abort(),
    }
}

impl<'a, V, Pred: RwLockPredicate<V>> Drop for MutexGuard<'a, V, Pred> {
    fn drop(&mut self) {
        // Dropped without `release`: keep the lock held, as with `RwLock`
        if let Some(g) = self.guard.take() {
            core::mem::forget(g);
        }
    }
}
