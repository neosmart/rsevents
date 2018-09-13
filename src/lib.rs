//! `rsevents` is an implementation of WIN32's auto- and manual-reset events for the rust world.
//! Events are synchronization primitives (i.e. not implemented atop of mutexes) used to either
//! create other synchronization primitives with or for implementing signalling between threads.
//!
//! Events come in two different flavors: [`AutoResetEvent`] and [`ManualResetEvent`], both
//! implementing the [`Event`] trait for abstracting over the underlying event type. Internally,
//! both are implemented with the unsafe [`RawEvent`] and use the `parking_lot_core` crate to
//! take care of efficiently suspending (parking) threads while they wait for an event to become
//! signalled.
extern crate parking_lot_core;

use parking_lot_core as plc;
use parking_lot_core::ParkResult;
use std::sync::atomic::{AtomicBool, Ordering, ATOMIC_BOOL_INIT};
use std::time::{Duration, Instant};

#[cfg(test)]
use std::sync::Arc;
#[cfg(test)]
use std::thread;

struct RawEvent(AtomicBool); // true for set, false for unset

/// A representation of the state of an `[Event]`, which can either be `Set` (i.e. signalled,
/// ready) or `Unset` (i.e. not ready).
#[derive(Clone, Debug, PartialEq)]
pub enum State {
    /// The event is available and call(s) to [`Event::wait()`] will go through without
    /// blocking, i.e. the event is signalled.
    Set,
    /// The event is unavailable and calls to [`Event::wait()`] will block until the event
    /// becomes set, i.e. the event is unsignalled.
    Unset,
}

/// An `Event` is a synchronization primitive that is functionally the equivalent of an (optionally
/// gated) waitable boolean that allows for synchronization between threads. Unlike mutexes and
/// condition variables which are most often used to restrict access to a critical section, events
/// are more appropriate for efficiently signalling remote threads or waiting on a remote thread to
/// change state.
pub trait Event {
    fn new(initial_state: State) -> Self;
    /// Signal that the event has been set. Depending on the type of event, this may allow one or
    /// more parked or future waiters through. See [`AutoResetEvent::set()`] and
    /// [`ManualResetEvent::set()`] for type-specific details.
    fn set(&self);
    /// Set the state of the internal event to [`State::Unset`], regardless of its current status.
    fn reset(&self);
    /// Check if the event has been signalled, and if not, block waiting for it to be set.
    fn wait(&self);
    /// Check if the event has been signalled, and if not, block for `limit` waiting for it to be set.
    /// Returns `true` if the event was originally set or if it was signalled within the specified
    /// duration, and `false` otherwise (if the timeout elapsed without the event becoming set).
    fn wait_for(&self, limit: Duration) -> bool;

    /// Test if an `Event` is available without blocking, return `false` immediately if it is not
    /// set. Note that this is *not* the same as calling [`Event::wait_for()`] with a `Duration` of
    /// zero, as the calling thread never yields.
    fn wait0(&self) -> bool;
}

/// An `AutoResetEvent` is a gated [`Event`] that is functionally equivalent to a "waitable
/// boolean" and can be atomically waited upon and consumed to signal one and only one waiter at a
/// time, thereby guaranteeing exclusive access to a critical section.
///
/// While an `AutoResetEvent` can be used to implement mutexes and condition variables, it is more
/// appropriate for uses involving signalling between two or more threads. Unlike a
/// `ManualResetEvent`, an `AutoResetEvent`'s `set` state is selectively made visible to only one
/// waiter at a time (including past waiters currently in a suspended/parked state). When
/// [`AutoResetEvent::set()`] is called, at most one thread blocked in a call to
/// [`AutoResetEvent::wait()`] will be let through (hence the "gated" description). If a previously
/// parked thread was awaked, then the event's state remains unset for all future callers, but if
/// no threads were previously parked waiting for this event to be signalled then only the next
/// thread to call `AutoResetEvent::wait()` on this instance will be let through without blocking.
pub struct AutoResetEvent {
    event: RawEvent,
}

impl Event for AutoResetEvent {
    /// Create a new [`AutoResetEvent`] that can be used to atomically signal one waiter at a time.
    fn new(state: State) -> AutoResetEvent {
        Self {
            event: RawEvent::new(state == State::Set),
        }
    }

    /// Triggers the underlying [`RawEvent`], either releasing one suspended waiter or allowing one
    /// future caller to exclusively obtain the event.
    fn set(&self) {
        self.event.set_one()
    }

    /// Set the state of the internal event to [`State::Unset`], regardless of its current status.
    fn reset(&self) {
        self.event.reset()
    }

    /// Check if the event has been signalled, and if not, block waiting for it to be set. When the
    /// event becomes available, its state is atomically set to [`State::Unset`], allowing only
    /// one waiter through.
    fn wait(&self) {
        self.event.unlock_one()
    }

    /// Check if the event has been signalled, and if not, block for `limit` waiting for it to be set.
    /// If and when the event becomes available, its state is atomically set to [`State::Unset`],
    /// allowing only one waiter through.
    ///
    /// Returns `true` if the event was originally set or if it was signalled within the specified
    /// duration, and `false` otherwise (if the timeout elapsed without the event becoming set).
    fn wait_for(&self, limit: Duration) -> bool {
        self.event.wait_one_for(limit)
    }

    /// Test if an `Event` is available without blocking, returning `false` immediately if it is
    /// not set. **This is _not_ a `peek()` function:** if the event's state was [`State::Set`], it
    /// is atomically reset to [`State::Unset`].
    ///
    /// Note that this is additionally _not_ the same as calling [`Event::wait_for()`] with a
    /// `Duration` of zero, as the calling thread never yields.
    fn wait0(&self) -> bool {
        self.event.try_unlock_one()
    }
}

/// A `ManualResetEvent` is an [`Event`] impl best understood as a "waitable boolean" that
/// efficiently synchronizes thread access to a shared state, allowing one or more threads to wait
/// for a signal from one or more other threads, where the signal could have either occurred in the
/// past or could come at any time in the future.
///
/// Unlike an `AutoResetEvent` which atomically allows one and only one waiter through
/// each time the underlying `[RawEvent]` is set, a `ManualResetEvent` unparks all past waiters and
/// allows all future waiters calling [`Event::wait()`] to continue without blocking (until
/// [`ManualResetEvent::reset()`] is called).
///
/// A `ManualResetEvent` is rarely appropriate for general purpose thread synchronization (à la
/// condition variables and mutexes), where exclusive access to a protected critical section is
/// usually desired, as if multiple threads are suspended/parked waiting for the event to be
/// signalled and then `Event::set()` is called, _all_ of the suspended threads will be unparked
/// and will resume. However, a `ManualResetEvent` shines when it comes to setting persistent
/// state indicators, such as a globally-shared abort flag.
pub struct ManualResetEvent {
    event: RawEvent,
}

impl Event for ManualResetEvent {
    /// Create a new [`ManualResetEvent`].
    fn new(state: State) -> ManualResetEvent {
        Self {
            event: RawEvent::new(state == State::Set),
        }
    }

    /// Puts the underlying [`RawEvent`] into a set state, releasing all suspended waiters (if any)
    /// and leaving the event set for future callers.
    fn set(&self) {
        self.event.set_all()
    }

    /// Set the state of the internal event to [`State::Unset`], regardless of its current status.
    fn reset(&self) {
        self.event.reset()
    }

    /// Check if the underlying event is in a set state or wait for its state to become
    /// [`State::Set`]. The event's state is not affected by this operation, i.e. it remains set
    /// for future callers even after this function call returns.
    fn wait(&self) {
        self.event.unlock_all()
    }

    /// Check if the underlying event is in a set state (and return immediately) or wait for it to
    /// become set, up to the limit specified by the `Duration` parameter.
    ///
    /// Returns `true` if the event was initially set or if it became set within the timelimit
    /// specified. Otherise returns `false` if the timeout elapsed without the event becoming
    /// available.
    fn wait_for(&self, limit: Duration) -> bool {
        self.event.wait_all_for(limit)
    }

    /// Test if an `Event` is available without blocking, returning `false` immediately if it is
    /// not set.
    ///
    /// Note that this is NOT the same as calling [`Event::wait_for()`] with a `Duration` of
    /// zero, as the calling thread never yields.
    fn wait0(&self) -> bool {
        self.event.try_unlock_all()
    }
}

impl RawEvent {
    fn new(state: bool) -> RawEvent {
        let event = RawEvent(ATOMIC_BOOL_INIT);
        event.0.store(state, Ordering::Relaxed);
        event
    }

    /// Parks the calling thread until the underlying event has unlocked
    unsafe fn suspend_one(&self) {
        plc::park(
            self as *const RawEvent as usize,
            || !self.try_unlock_one(),
            || {},
            |_, _| {},
            plc::DEFAULT_PARK_TOKEN,
            None,
        );
    }

    unsafe fn suspend_all(&self) {
        plc::park(
            self as *const RawEvent as usize,
            || !self.try_unlock_all(),
            || {},
            |_, _| {},
            plc::DEFAULT_PARK_TOKEN,
            None,
        );
    }

    /// Attempts to exclusively obtain the event. Returns true upon success.
    fn try_unlock_one(&self) -> bool {
        self.0.swap(false, Ordering::AcqRel)
    }

    /// Attempts to obtain the event (without locking out future callers). Returns true upon success.
    fn try_unlock_all(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }

    /// Trigger the event, releasing all waiters
    fn set_all(&self) {
        self.0.store(true, Ordering::Release);
        unsafe { plc::unpark_all(self as *const RawEvent as usize, plc::DEFAULT_UNPARK_TOKEN) };
    }

    fn unlock_one(&self) {
        if !self.try_unlock_one() {
            unsafe {
                self.suspend_one();
            }
        }
    }

    fn unlock_all(&self) {
        if !self.try_unlock_all() {
            unsafe {
                self.suspend_all();
            }
        }
    }

    /// Trigger the event, releasing one waiter
    fn set_one(&self) {
        let unpark_result = unsafe {
            plc::unpark_one(self as *const RawEvent as usize, |_| {
                plc::DEFAULT_UNPARK_TOKEN
            })
        };

        if unpark_result.unparked_threads == 0 {
            // Leave this event unlocked so another thread may obtain it later.  But keep in mind
            // another thread may have obtained the event while we were here, so only set it to
            // `true` if it is currently `false` (as we expect it to be).
            self.0.compare_and_swap(false, true, Ordering::Relaxed);
        }
    }

    /// Put the event in a locked (reset) state.
    fn reset(&self) {
        self.0.store(false, Ordering::Release);
    }

    fn wait_one_for(&self, limit: Duration) -> bool {
        let end = Instant::now() + limit;
        let wait_result = unsafe {
            plc::park(
                self as *const RawEvent as usize,
                || !self.try_unlock_one(),
                || {},
                |_, _| {},
                plc::DEFAULT_PARK_TOKEN,
                Some(end),
            )
        };

        wait_result != ParkResult::TimedOut
    }

    fn wait_all_for(&self, limit: Duration) -> bool {
        let end = Instant::now() + limit;
        let wait_result = unsafe {
            plc::park(
                self as *const RawEvent as usize,
                || !self.try_unlock_all(),
                || {},
                |_, _| {},
                plc::DEFAULT_PARK_TOKEN,
                Some(end),
            )
        };

        wait_result != ParkResult::TimedOut
    }
}

#[test]
fn sanity_check() {
    let event = RawEvent::new(true);
    assert_eq!(true, event.try_unlock_one());

    let event = RawEvent::new(false);
    assert_eq!(false, event.try_unlock_one());
}

#[test]
fn basic_locking() {
    let event = RawEvent::new(false);
    event.set_all();
    assert_eq!(true, event.try_unlock_one());
}

#[test]
fn basic_unlocking() {
    let event = RawEvent::new(true);
    event.reset();
    assert_eq!(false, event.try_unlock_one());
}

#[test]
fn basic_double_unlock() {
    let event = AutoResetEvent::new(State::Set);
    assert_eq!(true, event.wait0());
    assert_eq!(false, event.wait0());

    let event = ManualResetEvent::new(State::Set);
    assert_eq!(true, event.wait0());
    assert_eq!(true, event.wait0());
}

#[test]
fn suspend_and_resume() {
    // this is the main event we're trying to wait on
    let event1 = Arc::new(AutoResetEvent::new(State::Unset));
    // and this event is used to tell the main thread that the worker thread is ready for it
    let event2 = Arc::new(ManualResetEvent::new(State::Unset));
    let thread = {
        let event1 = event1.clone();
        let event2 = event2.clone();
        thread::spawn(move || {
            assert_eq!(false, event1.wait0());
            // signal to the first event that we are ready for event1 to be unlocked
            event2.set();
            event1.wait();
        })
    };
    event2.wait();
    event1.set();
    thread.join();
}

#[test]
/// Verify that when a thread is unlocked only one waiting thread gets through.
fn single_thread_release() {
    use std::sync::atomic::ATOMIC_USIZE_INIT;

    let event = Arc::new(AutoResetEvent::new(State::Unset));
    let event2 = Arc::new(AutoResetEvent::new(State::Unset)); // used to signal that a waiter has finished
    let succeed_count = Arc::new(ATOMIC_USIZE_INIT);
    succeed_count.store(0, Ordering::Relaxed);

    let create_waiter = || {
        let event = event.clone();
        let event2 = event2.clone();
        let succeed_count = succeed_count.clone();
        thread::spawn(move || {
            event.wait();
            succeed_count.fetch_add(1, Ordering::AcqRel);
            event2.set();
        })
    };

    // create 50 threads that will contend for the event
    for _ in 0..50 {
        create_waiter();
    }

    // hopefully let just one event through
    event.set();

    // yield for 100 time slices
    for _ in 0..100 {
        std::thread::yield_now();
    }

    event2.wait();
    assert_eq!(succeed_count.load(Ordering::Acquire), 1);
    event.set();
    event2.wait();
    assert_eq!(succeed_count.load(Ordering::Acquire), 2);
}
