#![allow(unused_imports)]
use super::super::prelude::*;
use core::time::Duration;
use std::sync::{Barrier, BarrierWaitResult};
use std::thread::{LocalKey, Thread, ThreadId};

// Specs for std::thread functions other than spawning, and std::sync::Barrier.
// For spawning threads, see `vstd::thread`.
verus! {

pub assume_specification[ std::thread::sleep ](dur: Duration)
    no_unwind
;

pub assume_specification[ std::thread::yield_now ]()
    no_unwind
;

pub assume_specification[ Duration::from_secs ](secs: u64) -> Duration
    no_unwind
;

pub assume_specification[ Duration::from_millis ](millis: u64) -> Duration
    no_unwind
;

pub assume_specification[ Duration::from_micros ](micros: u64) -> Duration
    no_unwind
;

pub assume_specification[ Duration::from_nanos ](nanos: u64) -> Duration
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExThread(Thread);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExThreadId(ThreadId);

pub assume_specification[ std::thread::current ]() -> Thread
    no_unwind
;

pub assume_specification[ Thread::id ](t: &Thread) -> ThreadId
    no_unwind
;

pub assume_specification[ std::thread::park ]()
    no_unwind
;

pub assume_specification[ Thread::unpark ](t: &Thread)
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBarrier(Barrier);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBarrierWaitResult(BarrierWaitResult);

pub assume_specification[ Barrier::new ](n: usize) -> Barrier
    no_unwind
;

pub assume_specification[ Barrier::wait ](b: &Barrier) -> BarrierWaitResult
    no_unwind
;

pub assume_specification[ BarrierWaitResult::is_leader ](r: &BarrierWaitResult) -> bool
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(std::io::Error);

#[cfg(feature = "nonzero_internals")]
pub assume_specification[ std::thread::available_parallelism ]() -> std::io::Result<
    core::num::NonZero<usize>,
>
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExLocalKey<T: 'static>(LocalKey<T>);

// Panics if the thread-local has been destroyed (i.e. during thread teardown).
// A `thread_local!` key is external to Verus, so access it through an
// `external_body` function returning `&'static LocalKey<T>`.
pub assume_specification<T: 'static, F: FnOnce(&T) -> R, R>[ LocalKey::<T>::with ](
    key: &'static LocalKey<T>,
    f: F,
) -> (ret: R)
    requires
        forall|t: &T| #[trigger] f.requires((t,)),
    ensures
        exists|t: &T| #[trigger] f.ensures((t,), ret),
;

} // verus!
