//! `rsevents` is an implementation of WIN32's auto- and manual-reset events for the rust world.
//! Events are synchronization primitives (i.e. not implemented atop of mutexes) used to either
//! create other synchronization primitives with or for implementing signalling between threads.
//!
//! Events come in two different flavors: [`AutoResetEvent`] and [`ManualResetEvent`]. Internally,
//! both are implemented with the unsafe `RawEvent` and use the `parking_lot_core` crate to take
//! care of efficiently suspending (parking) threads while they wait for an event to become
//! signalled.
//!
//! An event is a synchronization primitive that is functionally the equivalent of an (optionally
//! gated) waitable boolean that allows for synchronization between threads. Unlike mutexes and
//! condition variables which are most often used to restrict access to a critical section, events
//! are more appropriate for efficiently signalling remote threads or waiting on a remote thread to
//! change state.

use parking_lot_core as plc;
use parking_lot_core::ParkResult;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

#[cfg(test)]
mod tests;

/// A wrapper around an atomic state that represents whether or not the event is available.
/// This isn't pinned and it seems that pinning is unnecessary because the lock may be moved so long
/// as it is not borrowed (for prior art, see rust's `src/sys/windows/locks/mutex.rs` which is
/// similarly directly exposed without pinning/boxing to make a movable mutex.
struct RawEvent(AtomicBool);

/// A representation of the state of an event, which can either be `Set` (i.e. signalled,
/// ready) or `Unset` (i.e. not ready).
#[derive(Clone, Debug, PartialEq)]
pub enum EventState {
    /// The event is available and call(s) to [`Awaitable::wait()`] will go through without
    /// blocking, i.e. the event is signalled.
    Set,
    /// The event is unavailable and calls to [`Awaitable::wait()`] will block until the event
    /// becomes set, i.e. the event is unsignalled.
    Unset,
}

#[doc(hidden)]
pub type State = EventState;

pub trait Awaitable {
    /// Check if the awaitable type is available, and if not, block waiting for it to become
    /// available.
    fn wait(&self);

    /// Check if the awaitable type is available, and if not, block for `limit` waiting for it to
    /// become available. Returns `true` if the `Awaitable` was originally set or if it became so
    /// within the specified duration and `false` otherwise (if the timeout elapsed without the
    /// `Awaitable` becoming set).
    fn wait_for(&self, limit: Duration) -> bool;

    /// Test if the awaitable type is available without blocking, return `false` immediately if it
    /// is not. This call may have side effects beyond merely returning the current state and should
    /// not be considered a `test()` or `peek()` function.
    /// Note that this is not the same as calling [`Awaitable::wait_for()`] with a `Duration` of
    /// zero, as the calling thread never yields.
    fn wait0(&self) -> bool;
}

/// An `AutoResetEvent` is a gated event that is functionally equivalent to a "waitable
/// boolean" and can be atomically waited upon and consumed to signal one and only one waiter at a
/// time, thereby guaranteeing exclusive signalling. This is not unlike a multi-producer,
/// multi-consumer non-broadcast `Channel<()>` with a buffer size of 1, except much more efficient
/// and lightweight.
///
/// `AutoResetEvent` can be used to implement other synchronization objects such as mutexes and
/// condition variables, but it is most appropriate for uses involving signalling between two or
/// more threads. Unlike a [`ManualResetEvent`], an `AutoResetEvent`'s `set` state is selectively
/// made visible to only one waiter at a time (including past waiters currently in a
/// suspended/parked state). When [`AutoResetEvent::set()`] is called, at most one thread blocked in
/// a call to [`Awaitable::wait()`] will be let through (hence the "gated" description). If a
/// previously parked thread was awakened, then the event's state remains unset for all future
/// callers, but if no threads were previously parked waiting for this event to be signalled then
/// only the next thread to call [`AutoResetEvent::wait()`] on this instance will be let through
/// without blocking (and with the `set()` call returning immediately).
///
/// Auto-reset events are thread-safe and may be wrapped in an [`Arc`](std::sync::Arc) or declared
/// as a static global to easily share access across threads.
pub struct AutoResetEvent {
    event: RawEvent,
}

impl AutoResetEvent {
    /// Create a new [`AutoResetEvent`] that can be used to atomically signal one waiter at a time.
    pub const fn new(state: EventState) -> AutoResetEvent {
        Self {
            event: RawEvent::new(matches!(state, EventState::Set)),
        }
    }

    /// Triggers the underlying `RawEvent`, either releasing one suspended waiter or allowing one
    /// future caller to exclusively obtain the event.
    pub fn set(&self) {
        self.event.set_one()
    }

    /// Set the state of the internal event to [`EventState::Unset`], regardless of its current
    /// status.
    pub fn reset(&self) {
        self.event.reset()
    }
}

impl Awaitable for AutoResetEvent {
    /// Check if the event has been signalled, and if not, block waiting for it to be set. When the
    /// event becomes available, its state is atomically set to [`EventState::Unset`], allowing only
    /// one waiter through.
    fn wait(&self) {
        self.event.unlock_one()
    }

    /// Check if the event has been signalled, and if not, block for `limit` waiting for it to be set.
    /// If and when the event becomes available, its state is atomically set to
    /// [`EventState::Unset`], allowing only this one waiter through.
    ///
    /// Returns `true` if the event was originally set or if it was signalled within the specified
    /// duration, and `false` otherwise (if the timeout elapsed without the event becoming set).
    fn wait_for(&self, limit: Duration) -> bool {
        self.event.wait_one_for(limit)
    }

    /// Test if an event is available without blocking, returning `false` immediately if it is
    /// not set. **This is _not_ a `peek()` function:** if the event's state was
    /// [`EventState::Set`], it is atomically reset to [`EventState::Unset`].
    ///
    /// Note that this is additionally _not_ the same as calling [`Awaitable::wait_for()`] with a
    /// `Duration` of zero, as the calling thread never yields.
    fn wait0(&self) -> bool {
        self.event.try_unlock_one()
    }
}

/// A `ManualResetEvent` is an event type best understood as a "waitable boolean" that efficiently
/// synchronizes thread access to a shared state, allowing one or more threads to wait for a signal
/// from one or more other threads, where the signal could have either occurred in the past or
/// could come at any time in the future.
///
/// Unlike an [`AutoResetEvent`] which atomically allows one and only one waiter through each time
/// the underlying `RawEvent` is set, a `ManualResetEvent` unparks all past waiters and allows
/// all future waiters calling [`Awaitable::wait()`] to continue without blocking (until
/// [`ManualResetEvent::reset()`] is called).
///
/// A `ManualResetEvent` is rarely appropriate for general purpose thread synchronization (à la
/// condition variables and mutexes), where exclusive access to a protected critical section is
/// usually desired, as if multiple threads are suspended/parked waiting for the event to be
/// signalled and then [`ManualResetEvent::set()`] is called, _all_ of the suspended threads will be
/// unparked and will resume. However, a `ManualResetEvent` shines when it comes to setting
/// persistent state indicators, such as a globally-shared abort flag.
///
/// Manual-reset events are thread-safe and may be wrapped in an [`Arc`](std::sync::Arc) or declared
/// as a static global to easily share access across threads.
pub struct ManualResetEvent {
    event: RawEvent,
}

impl ManualResetEvent {
    /// Create a new [`ManualResetEvent`].
    pub const fn new(state: EventState) -> ManualResetEvent {
        Self {
            event: RawEvent::new(matches!(state, EventState::Set)),
        }
    }

    /// Puts the [`ManualResetEvent`] into a set state, releasing all suspended waiters (if any)
    /// and leaving the event set for future callers.
    pub fn set(&self) {
        self.event.set_all()
    }

    /// Set the state of the [`ManualResetEvent`] to [`EventState::Unset`], regardless of its
    /// current state.
    pub fn reset(&self) {
        self.event.reset()
    }
}

impl Awaitable for ManualResetEvent {
    /// Check if the underlying event is in a set state or wait for its state to become
    /// [`EventState::Set`]. The event's state is not affected by this operation, i.e. it remains
    /// set for future callers even after this function call returns.
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

    /// Test if an event is available without blocking, returning `false` immediately if it is
    /// not set.
    ///
    /// Note that this is not the same as calling [`Awaitable::wait_for()`] with a `Duration` of
    /// zero, as the calling thread never yields.
    fn wait0(&self) -> bool {
        self.event.try_unlock_all()
    }
}

impl RawEvent {
    const fn new(state: bool) -> RawEvent {
        RawEvent(AtomicBool::new(state))
    }

    /// Attempts to exclusively obtain the event. Returns true upon success. Called internally by
    /// [`suspend_one()`](Self::suspend_one) when determining if a thread should be parked/suspended
    /// or if that's not necessary.
    fn try_unlock_one(&self) -> bool {
        self.0.swap(false, Ordering::Acquire)
    }

    /// Attempts to obtain the event (without locking out future callers). Returns true upon success.
    fn try_unlock_all(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }

    /// Parks the calling thread until the underlying event has unlocked. If the event is set during
    /// this call, the park aborts/returns early so that no event sets are missed. Consumes the
    /// event's set state in case of early return.
    unsafe fn suspend_one(&self) {
        plc::park(
            self as *const RawEvent as usize, // key for keyed event
            || !self.try_unlock_one(), // whether or not to go through with the park, run while
                                       // queue is locked
            || {}, // callback before parking, run after queue is unlocked
            |_, _| {}, // timeout handler, run while queue is locked
            plc::DEFAULT_PARK_TOKEN,
            None, // timeout
        );
    }

    /// Parks the calling thread until the underlying event has unlocked. If the event is set during
    /// this call, the park aborts/returns early so that no event sets are missed. Unlike
    /// [`suspend_one()`](Self::suspend_one), does not consume the event's set state in case of
    /// early return.
    unsafe fn suspend_all(&self) {
        plc::park(
            self as *const RawEvent as usize, // key for keyed event
            || !self.try_unlock_all(), // whether or not to go through with the park, run while
                                       // queue is locked
            || {}, // callback before parking, run after queue is unlocked
            |_, _| {}, // timeout handler, run while queue is locked
            plc::DEFAULT_PARK_TOKEN,
            None, // timeout
        );
    }

    /// Trigger the event, releasing one waiter
    fn set_one(&self) {
        unsafe {
            // The unpark callback happens with the plc queue locked, so we guarantee that the logic
            // here happens either completely before or completely after the logic in the callback
            // passed to plc::park() in suspend_one().
            plc::unpark_one(self as *const RawEvent as usize, |unpark_result| {
                // This has to be done here with the plc queue locked so that a simultaneous call
                // into plc::park() will not suspend a thread after we've tried unfruitfully to
                // awaken one but before we've had a chance to set the internal state, causing the
                // set_one() call to be missed.

                if unpark_result.unparked_threads == 0 {
                    // Since the wakeup resulted in no threads being unparked, set the state to unlocked to
                    // ensure that the event isn't missed.
                    self.0.store(true, Ordering::Release);
                } else {
                    // There's no need to guarantee synchronization of code before/after the
                    // set/wait() call points when the event wasn't available.
                    self.0.store(false, Ordering::Relaxed);
                }
                plc::DEFAULT_UNPARK_TOKEN
            })
        };
    }

    /// Trigger the event, releasing all waiters
    fn set_all(&self) {
        if self.0.swap(true, Ordering::Release) == false {
            // The event was previously unavailable
            unsafe {
                plc::unpark_all(self as *const RawEvent as usize, plc::DEFAULT_UNPARK_TOKEN)
            };
        }
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

    /// Put the event in a locked (reset) state.
    fn reset(&self) {
        // Calling reset() does not imply any strict ordering of code before or after a matching
        // (try_)unlock() call, so we use Relaxed semantics.
        self.0.store(false, Ordering::Relaxed);
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
