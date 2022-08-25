# rsevents

[![crates.io](https://img.shields.io/crates/v/rsevents.svg)](https://crates.io/crates/rsevents)
[![docs.rs](https://docs.rs/rsevents/badge.svg)](https://docs.rs/latest/rsevents)

This crate contains a cross-platform implementation of auto and manual reset events similar to those found in Microsoft Windows, implemented on top of the core parking lot crate as a cross-platform futex abstraction.

## About `rsevents`

An event is best compared to an awaitable boolean, and can have either of two states: set and unset.
Callers may directly wait on the event itself, foregoing the need for an associated condition variable and mutex.
Depending on the specific type of the event, an event can also be thought of as an efficient implementation of a multi-producer, multi-consumer `Channel<()>` (with a manual-reset event being a broadcast version of the same channel).

As with WIN32 events, rsevents come in two flavors, [`AutoResetEvent`](https://docs.rs/rsevents/latest/rsevents/struct.AutoResetEvent.html) and [`ManualResetEvent`](https://docs.rs/rsevents/latest/rsevents/struct.ManualResetEvent.html), which differ in their behavior when it comes to setting (aka signalling) an event.
An `AutoResetEvent`, once signalled, permits exactly one (and only one) past or future caller waiting on the same event to unblock, whereas a `ManualResetEvent` lacks such fine-grained control and is either signalled and unblocked for all past/future waiters or none (until its state is manually/explicitly changed). Their usages differ tremendously so make sure you are using the correct event type for your needs!

## Example

The following code is an example wherein the main thread dispatches work to a pool of spawned threads, which is then claimed by the first available thread.
It demonstrates some of the unique properties of auto-reset events (thread-at-a-time signalling, memory coherence between threads calling `event.set()` and threads calling `event.wait()`, efficient blocking while waiting for work, and waiting with a time limit).
The unergonomic usage of raw pointers (for the `SHARED` thread message variable) is merely to illustrate the safety guarantees of auto-reset events - you are free to wrap your shared state in an `RwLock` or a simple wrapper type asserting `Sync`/`Send` exposing a nicer API if convenient.

```rust
use std::time::Duration;
use rsevents::{Awaitable, AutoResetEvent, EventState};

#[derive(Clone, Copy, Debug)]
enum ThreadMessage {
    /// Used in lieu of wrapping `ThreadMessage` in an `Option`
    None,
    /// Hands off a value to a worker thread for processing
    Input(u32),
}

// Events are cheap: each one is only a single byte!
static TASK_READY: AutoResetEvent = AutoResetEvent::new(EventState::Unset);
static DISPATCHED: AutoResetEvent = AutoResetEvent::new(EventState::Unset);

pub fn main() {
    // The events above synchronize access to this !Sync, !Send shared state
    static mut SHARED: ThreadMessage = ThreadMessage::None;

    const THREAD_COUNT: usize = 3;
    let mut threads = Vec::with_capacity(THREAD_COUNT);
    for thread_idx in 0..THREAD_COUNT {
        let join_handle = std::thread::spawn(move || {
            loop {
                // Wait efficiently for the main thread to signal _one_ (and
                // only one) worker thread at a time.
                if !TASK_READY.wait_for(Duration::from_millis(500)) {
                    // When there's not enough work, let the thread pool drain
                    break;
                }

                // This is safe because our events guarantee that
                // * one thread will be accessing this variable at a time
                // * shared memory will be consistent betwixt a call to
                //   event.set() from one thread and a call to event.wait()
                //   from another.
                let work_msg = unsafe { *(&SHARED as *const ThreadMessage) };

                // Signal to the main thread that we've taken the value and that
                // it can overwrite `shared` at its leisure. Afterwards,
                // processing can take as long as it needs.
                DISPATCHED.set();

                match work_msg {
                    ThreadMessage::None =>
                        unreachable!("The AutoResetEvent guarantees against this"),
                    ThreadMessage::Input(value) =>
                        eprintln!("Thread {thread_idx} handling value {value}"),
                }
            }
        });
        threads.push(join_handle);
    }

    // Generate some "random" values at an interval, dispatching each exactly
    // once to exactly one worker thread.
    for value in [4, 8, 15, 16, 23, 42] {
        unsafe {
            // It's perfectly safe to access - and even write - to SHARED here
            // because our two events guarantee exclusive access (as
            // AutoResetEvents wake one thread at a time) and take care of
            // synchronizing the memory plus any cache coherence issues between
            // the writing thread (this one) and the reading worker thread.
            *(&mut SHARED as * mut _) = ThreadMessage::Input(value);
        }

        // Signal a currently idle or the next idle worker thread to handle this
        // value.
        TASK_READY.set();

        // Remember that work is usually dispatched faster than it can be
        // handled!
        // Wait for a worker thread to signal it has received the payload and we
        // can stomp the `SHARED` value and dispatch work to the next worker.
        DISPATCHED.wait();
    }

    // Wait for the thread pool to drain and exit
    for jh in threads {
        jh.join().expect("Worker thread panicked!");
    }
    eprintln!("All work completed - exiting!")
}
```

## Types

Structs [`ManualResetEvent`](https://docs.rs/rsevents/latest/rsevents/struct.ManualResetEvent.html) and [`AutoResetEvent`](https://docs.rs/rsevents/latest/rsevents/struct.AutoResetEvent.html) both implement the [`Awaitable`](https://docs.rs/rsevents/latest/rsevents/trait.Awaitable.html) trait, which exposes an API that permits waiting indefinitely, waiting for zero time, and waiting for a fixed time limit (`Duration`) for an event to be triggered.
Dependent crates building their own synchronization primitives on `rsevents` types should similarly implement `Awaitable` to expose a unified interface for awaiting on objects (and should re-export the `Awaitable` trait (or all of `rsevents`) so that end users do not have to separately add a dependency on `rsevents` to their `Cargo.toml`).

See [the documentation](https://docs.rs/rsevents/latest/rsevents/) for more info.

## When to use

Generally speaking, a mutex or condition variable should always be preferred when it comes to protecting a critical section and ensuring exclusive access due to their well-understood synchronization paradigms and wide support.
However, there are other times when a synchronization primitve _not_ coupled to an explicit critical section or protected data is required, in which case it similarly does not make sense to use a mutex and a critical section when a single alternative synchronization primitive is what is actually required.

Events are somewhat like a hypothetical multi-producer, multi-consumer `RwLock` that doesn't own the data it protects.
Auto-reset events (like `AutoResetEvent`) are great for *signalling* and often used to easily build other synchronization primitives themselves without needing to use futexes or pay the price of one or more mutexes.

As such, events afford more freedom than the standard library synchronization primitives like `Mutex`, `RwLock`, or `CondVar`, but are also tools you have to be much more careful while using - with some exceptions.

Manual reset events (like `ManualResetEvent`) are actually incredibly easy and flexible to use for broadcasting a signal to all threads (affecting both already-waiting and not-yet-waiting threads) and are incredibly convenient for waiting indefinitely or for a fixed length of time on some non-thread-safe condition (such as a global abort indicator).

## About

rsevents is written and maintained by Mahmoud Al-Qudsi \<mqudsi@neosmart.net\> of NeoSmart
Technologies \<[https://neosmart.net/](https://neosmart.net)> and released to the general public
under the terms of the MIT public license.
