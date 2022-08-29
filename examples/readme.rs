//! This example illustrates the use of [`AutoResetEvent`] to dispatch work to
//! one worker at a time from a thread pool, with the events guaranteeing memory
//! consistency, efficient wait, wait-with-timeout, and exclusive dispatch.
//!
//! [`AutoResetEvent`]: rsevents::AutoResetEvent

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
