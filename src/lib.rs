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
use std::sync::atomic::{AtomicU8, Ordering};
use std::time::{Duration, Instant};

#[cfg(test)]
mod tests;

/// The event is available when this bit is set, otherwise it is unavailable.
const AVAILABLE_BIT: u8 = 0x01;
/// There are one or more threads waiting to obtain the event.
const WAITING_BIT: u8 = 0x02;

/// A wrapper around an atomic state that represents whether or not the event is available.
/// This isn't pinned and it seems that pinning is unnecessary because the lock may be moved so long
/// as it is not borrowed (for prior art, see rust's `src/sys/windows/locks/mutex.rs` which is
/// similarly directly exposed without pinning/boxing to make a movable mutex.
///
/// The lowest two bits of the u8 state are used, 0b010 represents the WAITING bit which is set when
/// a thread is parked or about to park, and 0b001 represents the AVAILABLE bit, set when the event
/// is available and cleared otherwise.
///
/// The following combinations are possible:
/// * 0b00: Unavailable
///   The event is not available and no threads are waiting on it. It can be "fast set" without
///   going through the plc lock.
/// * 0b01: Available
///   The event is available and there are no threads waiting on it. It can be "fast obtained"
///   without going through the plc lock.
/// * 0b10: Unavailable w/ Parked Waiters
///   The event is unavailable and there are one or more threads parked or trying to park to wait
///   for the event to become available. We must go through the plc lock to preferentially "give"
///   the event to a waiting thread.
/// * 0b11: Available w/ Parked Threads
///   The event is available but there are parked threads waiting for it. This is not a valid state
///   and no function should end with this being the quiescent state.
///
struct RawEvent(AtomicU8);

/// A representation of the state of an event, which can either be `Set` (i.e. signalled,
/// ready) or `Unset` (i.e. not ready).
#[derive(Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum EventState {
    /// The event is available and call(s) to [`Awaitable::wait()`] will go through without
    /// blocking, i.e. the event is signalled.
    Set,
    /// The event is unavailable and calls to [`Awaitable::wait()`] will block until the event
    /// becomes set, i.e. the event is unsignalled.
    Unset,
}

#[doc(hidden)]
/// This is for backwards compatibility with earlier `rsevents` releases, which used the less
/// specific (and much more likely to conflict) name `State` instead of `EventState`.
pub type State = EventState;

pub trait Awaitable {
    /// Check for and obtain the awaitable type if it is available; if not, block waiting for it to
    /// become available.
    fn wait(&self);

    /// Check for/obtain the awaitable type if it is available, and if not, block for `limit`
    /// waiting for it to become available.
    /// Returns `true` if the `Awaitable` was originally set or if it became so within the specified
    /// duration and `false` otherwise (i.e. if the timeout elapsed without the `Awaitable` type
    /// becoming set/available).
    fn wait_for(&self, limit: Duration) -> bool;

    /// Attempt to obtain the `Awaitable` type in a potentially lock-free, wait-free manor,
    /// returning `false` if it's currently unavailable.
    /// **This call may have side effects beyond merely returning the current state and must
    /// not be considered the equivalent of a `test()` or `peek()` function.**
    ///
    /// Note that this may not be the same as calling [`Awaitable::wait_for()`] with a `Duration` of
    /// zero, as the implementing type may use a different approach to ensure that the calling
    /// thread does not block.
    fn wait0(&self) -> bool {
        // The default implementation of this method is to just call `wait_for()` with a zero wait.
        // The function should be overridden if a better alternative is possible.
        return self.wait_for(Duration::ZERO);
    }
}

/// An `AutoResetEvent` is a gated event that is functionally equivalent to an "awaitable
/// boolean" and can be atomically waited upon and consumed to signal one and only one waiter at a
/// time, thereby guaranteeing exclusive signalling. This is not unlike a multi-producer,
/// multi-consumer non-broadcast `Channel<()>` with a buffer size of 1, except much more efficient
/// and lightweight.
///
/// `AutoResetEvent` can be used to implement other synchronization objects such as mutexes and
/// condition variables, but it is most appropriate for uses involving signalling between two or
/// more threads. Unlike a [`ManualResetEvent`], an `AutoResetEvent`'s `set` state is selectively
/// made visible to only one waiter at a time (including both past waiters currently in a
/// suspended/parked state and future waiters that haven't yet made a call to `Awaitable::wait()` or
/// similar).
///
/// When [`AutoResetEvent::set()`] is called, at most one thread blocked in a call to
/// [`Awaitable::wait()`] will be let through: if a previously parked thread was awakened, then the
/// event's state remains unset for all other past/future callers (until another call to
/// `AutoResetEvent::set()`), but if no threads were previously parked waiting for this event to be
/// signalled then only the next thread to call [`AutoResetEvent::wait()`] against this instance
/// will be let through without blocking. Regardless of whether or not there are any threads
/// currently waiting, the call to `set()` always returns immediately (i.e. it does not block until
/// another thread attempts to obtain the event).
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
            event: RawEvent::new(match state {
                EventState::Set => AVAILABLE_BIT,
                EventState::Unset => 0,
            })
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
    /// event becomes available to this thread, its state is atomically set to
    /// [`EventState::Unset`], allowing only this one waiter through until another call to
    /// [`AutoResetEvent::set()`] is made.
    fn wait(&self) {
        self.event.unlock_one()
    }

    /// Check if the event has been signalled, and if not, block for `limit` waiting for it to be set.
    /// If and when the event becomes available, its state is atomically set to
    /// [`EventState::Unset`], allowing only this one waiter through.
    ///
    /// Returns `true` if the event was originally set or if it was signalled within the specified
    /// duration, and `false` otherwise (i.e. the timeout elapsed without the event becoming set).
    fn wait_for(&self, limit: Duration) -> bool {
        self.event.wait_one_for(limit)
    }

    /// "Wait" on the `AutoResetEvent` event without blocking, immediately returning `true` if the
    /// event was signalled for this thread and `false` if it wasn't set.
    /// **This is _not_ a `peek()` function:** if the event's state was [`EventState::Set`], it is
    /// atomically reset to [`EventState::Unset`], locking out all other callers.
    ///
    /// Note that this is similar but not identical to calling [`AutoResetEvent::wait_for()`] with a
    /// `Duration` of zero, as the calling thread never blocks or yields.
    fn wait0(&self) -> bool {
        // In case of miri or if testing under ARM, make sure that a top-level wait0() call from
        // outside the implementation code returns a deterministic result.
        #[cfg(any(test, miri))]
        return self.event.test_try_unlock_one();
        #[cfg(not(any(test, miri)))]
        return self.event.try_unlock_one();
    }
}

/// A `ManualResetEvent` is an event type best understood as an "awaitable boolean" that efficiently
/// synchronizes thread access to a shared state, allowing one or more threads to wait for a signal
/// from one or more other threads, where the signal could have either occurred in the past or could
/// come at any time in the future.
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
    /// Create a new [`ManualResetEvent`] with the initial [`EventState`] set to `state`.
    pub const fn new(state: EventState) -> ManualResetEvent {
        Self {
            event: RawEvent::new(match state {
                EventState::Set => AVAILABLE_BIT,
                EventState::Unset => 0,
            })
        }
    }

    /// Puts the [`ManualResetEvent`] into a set state, releasing all suspended waiters (if any)
    /// and leaving the event set for future callers to [`ManualResetEvent::wait()`] and co.
    pub fn set(&self) {
        self.event.set_all()
    }

    /// Set the state of the [`ManualResetEvent`] to [`EventState::Unset`], regardless of its
    /// current state. This will cause future calls to [`ManualResetEvent::wait()`] to block until
    /// the event is set (via [`ManualResetEvent::set()`]).
    pub fn reset(&self) {
        self.event.reset()
    }
}

impl Awaitable for ManualResetEvent {
    /// Check if the underlying event is in a set state or wait for its state to become
    /// [`EventState::Set`]. In contrast with [`AutoResetEvent::wait()`], the event's state is not
    /// affected by this operation, i.e. it remains set for future callers even after this function
    /// call returns, until a call to [`ManualResetEvent::reset()`] is made.
    fn wait(&self) {
        self.event.unlock_all()
    }

    /// Check if the underlying event is in a set state (and return immediately) or wait for it to
    /// become set, up to the limit specified by the `Duration` parameter.
    ///
    /// Returns `true` if the event was initially set or if it became set within the timeout
    /// specified, otherwise returns `false` if the timeout elapsed without the event becoming
    /// available.
    fn wait_for(&self, limit: Duration) -> bool {
        self.event.wait_all_for(limit)
    }

    /// Test if an event is available without blocking, returning `false` immediately if it is
    /// not set.
    ///
    /// Note that this is not the same as calling [`ManualResetEvent::wait_for()`] with a `Duration` of
    /// zero, as the calling thread never yields.
    fn wait0(&self) -> bool {
        self.event.try_unlock_all()
    }
}

impl RawEvent {
    const fn new(state: u8) -> RawEvent {
        RawEvent(AtomicU8::new(state))
    }

    #[inline]
    /// Attempts to exclusively obtain the event. Returns true upon success. Called internally by
    /// [`suspend_one()`](Self::suspend_one) when determining if a thread should be parked/suspended
    /// or if that's not necessary.
    fn try_unlock_one(&self) -> bool {
        // Obtains the event if it is both available and there are no threads waiting on it.
        self.0.compare_exchange_weak(AVAILABLE_BIT, 0, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[cfg(any(test, miri))]
    /// This entry point is used to deterministically determine if the event could be obtained
    /// without any spurious failures. We don't override the actual behavior of try_unlock_one() so
    /// that any internal functions calling into it can still be tested against both normal and
    /// spurious failure modes.
    fn test_try_unlock_one(&self) -> bool {
        self.0.compare_exchange(AVAILABLE_BIT, 0, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[inline]
    /// Attempts to obtain the event (without locking out future callers). Returns true upon success.
    fn try_unlock_all(&self) -> bool {
        // Obtains the event if it is available, with no preconditions.
        (self.0.load(Ordering::Acquire) & AVAILABLE_BIT) != 0
    }

    /// Parks the calling thread until the underlying event has unlocked. If the event is set during
    /// this call, the park aborts/returns early so that no event sets are missed. Consumes the
    /// event's set state in case of early return.
    ///
    /// Returns `true` only if the thread has obtained the thread, otherwise returns `false` (only
    /// possible in the case of a timeout).
    unsafe fn suspend_one(&self, timeout: Option<Duration>) -> bool {
        let timeout = timeout.map(|duration| Instant::now() + duration);
        let mut state = self.0.load(Ordering::Relaxed);
        loop {
            // The only way a thread can obtain the event _before_ it is parked/put to sleep is to
            // check on the state before setting the WAITING bit for itself, otherwise it can't know
            // if there are any other threads waiting so it can't clear the WAITING bit, and if it
            // can't clear the WAITING bit, it can't obtain the event.
            if (state & AVAILABLE_BIT) != 0 {
                // The lock is available; try to obtain it even if the WAITING bit is set by
                // another thread.
                match self.0.compare_exchange_weak(state, state & !AVAILABLE_BIT, Ordering::Acquire, Ordering::Relaxed) {
                    Ok(_) => {
                        // The lock was obtained; there may or may not be other threads suspended.
                        return true;
                    }
                    Err(s) => {
                        // Another thread contended with this call, loop to try again.
                        state = s;
                        continue;
                    }
                }
            }
            else if (state & WAITING_BIT) == 0 {
                // There are no other threads waiting, so we need to set the WAITING bit ourselves
                // before we try to park the thread.
                match self.0.compare_exchange_weak(state, state | WAITING_BIT, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        // We set the WAITING bit and can continue with attempting to park this
                        // thread.
                    },
                    Err(s) => {
                        // Another thread contended with this call, loop to try again.
                        state = s;
                        continue;
                    }
                }
            } else {
                // The event isn't available and another thread has already marked it as pending, so
                // we are good to go.
            }

            // This callback is run with the plc queue locked, before the thread is parked. If it
            // returns false, the park is aborted. We can't opportunistically claim the event here
            // even if it is available, because we don't know if there are other suspended threads,
            // which means we can't clear the WAITING bit in case we were the last thread.
            let before_suspend = || -> bool {
                self.0.load(Ordering::Relaxed) == WAITING_BIT
            };

            // This callback is run with the plc queue locked, which is the only time we can safely
            // clear the WAITING bit (because `before_suspend` checks the WAITING bit with the queue
            // locked as well), making it possible to abort/retry the park() call if there's any
            // contention.
            let on_timeout = |_, last_thread| {
                if last_thread {
                    self.0.fetch_and(!WAITING_BIT, Ordering::Relaxed);
                }
            };

            match plc::park(
                self as *const RawEvent as usize, // key for keyed event
                before_suspend,
                || {}, // callback before parking, run after queue is unlocked
                on_timeout,
                plc::DEFAULT_PARK_TOKEN,
                timeout,
            ) {
                // before_suspend() detected a change in the state that indicates the lock may have
                // become available (or the WAITING bit could have been cleared because another
                // thread, which was the last actually parked thread, was awoken).
                // Loop to retry so we never miss a set() call.
                ParkResult::Invalid => state = self.0.load(Ordering::Relaxed),
                // The timeout was reached before the thread could be obtained.
                ParkResult::TimedOut => return false,
                // The thread was awoken by another thread calling into unlock_one().
                ParkResult::Unparked(_) => return true,
            }
        }
    }

    /// Parks the calling thread until the underlying event has unlocked. If the event is set during
    /// this call, the park aborts/returns early so that no event sets are missed. Unlike
    /// [`suspend_one()`](Self::suspend_one), does not consume the event's set state in case of
    /// early return.
    unsafe fn suspend_all(&self, timeout: Option<Duration>) -> bool {
        let timeout = timeout.map(|duration| Instant::now() + duration);
        let mut state = self.0.load(Ordering::Relaxed);
        loop {
            // The only way a thread can obtain the event _before_ it is parked/put to sleep is to
            // check on the state before setting the WAITING bit for itself, otherwise it can't know
            // if there are any other threads waiting so it can't clear the WAITING bit, and if it
            // can't clear the WAITING bit, it can't directly obtain the event for itself.
            if (state & AVAILABLE_BIT) != 0 {
                // The event has become available. We can return right away; we don't care about
                // anything else.
                return true;
            }
            else if (state & WAITING_BIT) == 0 {
                // There are no other threads waiting, so we need to set the WAITING bit ourselves
                // before we try to park the thread.
                match self.0.compare_exchange_weak(state, state | WAITING_BIT, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        // We set the WAITING bit without contention and can move on to trying to
                        // park this thread.
                    },
                    Err(s) => {
                        // Another thread contended with this call, loop to try again.
                        state = s;
                        continue;
                    }
                }
            } else {
                // The event isn't available and another thread has already marked it as pending, so
                // we are good to go.
            }

            // This callback is run with the plc queue locked, before the thread is parked. If it
            // returns false, the park is aborted. We can't opportunistically claim the event here
            // even if it is available, because we don't know if there are other suspended threads,
            // which means we can't clear the WAITING bit in case we were the last thread.
            let before_suspend = || -> bool {
                self.0.load(Ordering::Relaxed) == WAITING_BIT
            };

            // This callback is run with the plc queue locked, which is the only time we can safely
            // clear the WAITING bit (because `before_suspend` checks the WAITING bit with the queue
            // locked as well), making it possible to abort/retry the park() call if there's any
            // contention.
            let on_timeout = |_, last_thread| {
                if last_thread {
                    self.0.fetch_and(!WAITING_BIT, Ordering::Relaxed);
                }
            };

            match plc::park(
                self as *const RawEvent as usize, // key for keyed event
                before_suspend,
                || {}, // callback before parking, run after queue is unlocked
                on_timeout,
                plc::DEFAULT_PARK_TOKEN,
                timeout,
            ) {
                // before_suspend() detected a change in the state that indicates the lock may have
                // become available (or the WAITING bit could have been cleared because another
                // thread, which was the last actually parked thread, was awoken).
                // Loop to retry so we never miss a set() call.
                ParkResult::Invalid => state = self.0.load(Ordering::Relaxed),
                // The timeout was reached before the thread could be obtained.
                ParkResult::TimedOut => return false,
                // The thread was awoken by another thread calling into unlock_all().
                ParkResult::Unparked(_) => return true,
            }
        }
    }

    /// Trigger the event, releasing one waiter
    fn set_one(&self) {
        let mut state = self.0.load(Ordering::Relaxed);
        loop {
            match state {
                0b00 => {
                    // There are no parked/suspended threads so we are able to "fast set" the event
                    // without worrying about synchronizing with threads parked or about to park.
                    match self.0.compare_exchange_weak(0, AVAILABLE_BIT, Ordering::Release, Ordering::Relaxed) {
                        Ok(_) => return,
                        Err(s) => {
                            // We raced with a thread trying to park or another call to set(). Loop
                            // to figure out what happened.
                            state = s;
                            continue;
                        },
                    }
                },
                0b01 => {
                    // This was a call to set_one() on an event that was already set; we don't need to
                    // "do" anything but we need to touch the shared memory location to ensure
                    // memory ordering.
                    //
                    // It may be possible to forego this, but I'm not sure if that's wise. It is true
                    // that a thread awoken after two back-to-back set() calls is guaranteed to see at
                    // least _something_ new without an explicit Release here, but there's no guarantee
                    // that there will ever be any more set() calls afterwards, meaning whatever was
                    // written by the thread making the second set() call may never wind up being
                    // observed by a thread that fast-obtains the event in a wait() call.
                    match self.0.compare_exchange_weak(state, state, Ordering::Release, Ordering::Relaxed) {
                        Ok(_) => return,
                        Err(s) => {
                            state = s;
                            continue;
                        },
                    }
                },
                0b10 => {
                    // A thread is waiting to obtain this event, so we can't fast set it and must
                    // instead go through the plc queue lock.
                    break;
                },
                0b11 => {
                    // This shouldn't happen as we never set the event (which makes it available for
                    // grabs by any past or future waiter) if there are threads waiting on it.
                    // Instead, we manually hand off the event to another thread below with
                    // plc::unpark_one().
                    debug_assert!(false, "AVAILABLE and WAITING bits set!");
                },
                _ => {
                    unreachable!("We only use the lowest two bits of the AtomicU8 state!");
                },
            }
        }

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
                    // This can happen if there were two simultaneous calls to set_one() with only
                    // one thread parked or if there were no threads parked but a thread trying to
                    // park (which then didn't happen when we changed the state above and it failed
                    // the park validation callback).
                    // It's not only safe but actually required to stomp the WAITING bit because we
                    // have the plc queue locked - contending threads (about to park but not yet
                    // parked) will retry. If we don't stomp the WAITING bit and there was only one
                    // thread _about_ to park but not yet parked, it would loop after the park
                    // validation callback failed, but the WAITING bit wouldn't have been cleared
                    // and it won't be able to obtain the event.
                    self.0.store(AVAILABLE_BIT, Ordering::Release);
                } else if !unpark_result.have_more_threads {
                    // Clear the WAITING bit. Don't stomp the AVAILABLE bit in case we raced with
                    // another set() call.
                    // This makes it possible for the next call to set_one() to fast-set the event
                    // without going through the plc lock and triggers a retry in any threads trying
                    // to park.
                    self.0.fetch_and(!WAITING_BIT, Ordering::Release);
                } else {
                    // One thread was unparked but there are others still waiting. Subsequent
                    // set_one() calls will still need to go through the plc lock. We need to write
                    // to the shared memory address to guarantee Release semantics.
                    self.0.fetch_or(WAITING_BIT, Ordering::Release);
                }
                plc::DEFAULT_UNPARK_TOKEN
            })
        };
    }

    /// Trigger the event, releasing all waiters
    fn set_all(&self) {
        // Stomp the WAITING bit (if set) so that no other thread wastes time trying to unpark
        // threads since we're going to unlock them all.
        let prev_state = self.0.swap(AVAILABLE_BIT, Ordering::Release);
        if (prev_state & WAITING_BIT) == 0 {
            // No threads were suspended/about to be suspended so we can just return. Or maybe there
            // _are_ other threads suspended but we raced with a simultaneous call into set_all()
            // and that other thread is going to handle waking them.
            return;
        }

        let _unparked = unsafe {
            plc::unpark_all(self as *const RawEvent as usize, plc::DEFAULT_UNPARK_TOKEN)
        };

        // NOTE: _unparked may equal zero if there were no threads fully parked but there was a
        // thread _about_ to park until changing the state above caused its validation callback to
        // fail and then on retry they just obtained the available lock and returned.
    }

    fn unlock_one(&self) {
        if !self.try_unlock_one() {
            unsafe {
                self.suspend_one(None);
            }
        }
    }

    fn unlock_all(&self) {
        if !self.try_unlock_all() {
            unsafe {
                self.suspend_all(None);
            }
        }
    }

    /// Put the event in a locked (reset) state.
    fn reset(&self) {
        // Clear the AVAILABLE bit without touching the WAITING bit.
        // Calling reset() does not imply any strict ordering of code before or after a matching
        // (try_)unlock() call, so we use Relaxed semantics.
        self.0.fetch_and(!AVAILABLE_BIT, Ordering::Relaxed);
    }

    fn wait_one_for(&self, limit: Duration) -> bool {
        if self.try_unlock_one() {
            return true;
        }

        unsafe {
            self.suspend_one(Some(limit))
        }
    }

    fn wait_all_for(&self, limit: Duration) -> bool {
        if self.try_unlock_all() {
            return true;
        }

        unsafe {
            self.suspend_all(Some(limit))
        }
    }
}
