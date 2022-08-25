use std::sync::RwLock;
use rsevents::{Awaitable, AutoResetEvent, EventState};

#[derive(Default, Copy, Clone)]
enum ThreadMessage {
    // Used in lieu of wrapping `ThreadMessage` in an `Option`
    #[default]
    None,
    // Indicates that all worker threads should abort
    Abort,
    // Hands off a value to a worker thread for processing
    Input(u32),
}

static TASK_READY: AutoResetEvent = AutoResetEvent::new(EventState::Unset);
static DISPATCHED: AutoResetEvent = AutoResetEvent::new(EventState::Unset);

pub fn main() {
    let shared: RwLock<ThreadMessage> = RwLock::new(ThreadMessage::None);
    std::thread::scope(|scope| {
        const THREAD_COUNT: usize = 3;
        for thread_idx in 0..THREAD_COUNT {
            let thread_idx = thread_idx;
            let shared = &shared;
            scope.spawn(move || {
                loop {
                    // Wait efficiently for the main thread to signal
                    // _one_ (and only one) worker thread to do something
                    // with the shared state.
                    TASK_READY.wait();

                    let shared = {
                        *shared.try_read().expect("AutoResetEvent provides synchronization")
                    };

                    // Signal to the main thread that we've taken the value
                    // and that it can overwrite `shared` at its leisure. Processing
                    // afterwards can take as long as it needs.
                    DISPATCHED.set();

                    match shared {
                        ThreadMessage::None => unreachable!(),
                        ThreadMessage::Abort => break,
                        ThreadMessage::Input(value) =>
                            eprintln!("Thread {thread_idx} handling value {value}"),
                    }
                }

                eprintln!("Thread {thread_idx} exiting");
            });
        }

        // Generate some "random" values at an interval, dispatching each
        // exactly once to exactly one worker thread.
        for value in [4, 8, 15, 16, 23, 42] {
            {
                let mut shared = shared.try_write()
                    .expect("AutoResetEvent provides synchronization");
                *shared = ThreadMessage::Input(value);
            }
            // Signal a currently idle or the next idle worker thread to
            // handle this value.
            TASK_READY.set();

            // Wait for a worker thread to signal it has received the
            // payload and we can stomp the `shared` value.
            DISPATCHED.wait();
        }

        // Signal all threads to exit
        for _ in 0..THREAD_COUNT {
            {
                let mut shared = shared.try_write().expect("AutoResetEvent provides synchronization");
                *shared = ThreadMessage::Abort;
            }
            TASK_READY.set();
            DISPATCHED.wait();
        }

        // The spawned threads are automatically joined at the end of the
        // scope.
    });

    eprintln!("All work completed - exiting!")
}
