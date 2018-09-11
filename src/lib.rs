extern crate parking_lot_core;

use parking_lot_core as plc;
use parking_lot_core::UnparkResult;
use std::sync::atomic::{AtomicBool, Ordering, ATOMIC_BOOL_INIT};

#[cfg(test)]
use std::thread::{spawn, Thread};
#[cfg(test)]
use std::sync::Arc;

struct RawEvent(AtomicBool); // true for set, false for unset

#[derive(Clone, Debug, PartialEq)]
pub enum State {
    /// The event is available and call(s) to [`RawEvent::unlock()`] will go through without
    /// blocking.
    Set,
    /// The event is unavailable and calls to [`RawEvent::unlock()`] will block until the event
    /// becomes set.
    Unset,
}

pub trait Event {
    fn new(initial_state: State) -> Self;
    fn set(&self);
    fn unset(&self);
    fn unlock(&self);
    fn try_unlock(&self) -> bool;
}

pub struct AutoResetEvent {
    event: RawEvent,
}

impl Event for AutoResetEvent {
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

    fn unset(&self) {
        self.event.unset()
    }

    fn unlock(&self) {
        self.event.unlock_one()
    }

    fn try_unlock(&self) -> bool {
        self.event.try_unlock_one()
    }
}

pub struct ManualResetEvent {
    event: RawEvent,
}

impl ManualResetEvent {
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

    fn unset(&self) {
        self.event.unset()
    }

    fn unlock(&self) {
        self.event.unlock_all()
    }

    fn try_unlock(&self) -> bool {
        self.event.try_unlock_all()
    }
}

impl RawEvent {
    fn new(state: bool) -> RawEvent {
        let event = RawEvent(ATOMIC_BOOL_INIT);
        event.0.store(state, Ordering::Relaxed);
        event
    }

    /// Blocks until the event is acquired.
    fn unlock(&self) {}

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

    /// Put the event in a locked (unset) state.
    fn unset(&self) {
        self.0.store(false, Ordering::Release);
    }
}

#[test]
fn try_lock_sanity_check() {
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
    event.unset();
    assert_eq!(false, event.try_unlock_one());
}

#[test]
fn basic_double_unlock() {
    let event = AutoResetEvent::new(State::Set);
    assert_eq!(true, event.try_unlock());
    assert_eq!(false, event.try_unlock());

    let event = ManualResetEvent::new(State::Set);
    assert_eq!(true, event.try_unlock());
    assert_eq!(true, event.try_unlock());
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
        spawn(move || {
            assert_eq!(false, event1.try_unlock());
            // signal to the first event that we are ready for event1 to be unlocked
            event2.set();
            event1.unlock();
        })
    };
    event2.unlock();
    event1.set();
    thread.join();
}

#[test]
/// Verify that when a thread is unlocked only one waiting thread gets through.
fn single_thread_release() {
    use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT};

    let event = Arc::new(AutoResetEvent::new(State::Unset));
    let event2 = Arc::new(AutoResetEvent::new(State::Unset)); // used to signal that a waiter has finished
    let succeed_count = Arc::new(ATOMIC_USIZE_INIT);
    succeed_count.store(0, Ordering::Relaxed);

    let create_waiter = || {
        let event = event.clone();
        let event2 = event2.clone();
        let succeed_count = succeed_count.clone();
        spawn(move || {
            event.unlock();
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

    event2.unlock();
    assert_eq!(succeed_count.load(Ordering::Acquire), 1);
    event.set();
    event2.unlock();
    assert_eq!(succeed_count.load(Ordering::Acquire), 2);
}
