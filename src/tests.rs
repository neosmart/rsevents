use crate::*;
use std::sync::Arc;
use std::sync::atomic::AtomicUsize;
use std::thread;

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
    // This is the main event we're trying to wait on
    let event1 = Arc::new(AutoResetEvent::new(State::Unset));
    // And this event is used to tell the main thread that the worker thread is ready for it
    let event2 = Arc::new(ManualResetEvent::new(State::Unset));
    let thread = {
        let event1 = event1.clone();
        let event2 = event2.clone();
        thread::spawn(move || {
            assert_eq!(false, event1.wait0());
            // Signal to the first event that we are ready for event1 to be unlocked
            event2.set();
            event1.wait();
        })
    };
    event2.wait();
    event1.set();
    thread.join().ok();
}

#[test]
/// Verify that when a thread is unlocked only one waiting thread gets through.
fn single_thread_release() {
    let event = Arc::new(AutoResetEvent::new(State::Unset));
    // event2 is used to signal that a waiter has finished
    let event2 = Arc::new(AutoResetEvent::new(State::Unset));
    let succeed_count = Arc::new(AtomicUsize::new(0));
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

    // Create 50 threads that will contend for the event
    for _ in 0..50 {
        create_waiter();
    }

    // Hopefully let just one event through
    event.set();

    // Yield for 100 time slices
    for _ in 0..100 {
        std::thread::yield_now();
    }

    event2.wait();
    assert_eq!(succeed_count.load(Ordering::Acquire), 1);
    event.set();
    event2.wait();
    assert_eq!(succeed_count.load(Ordering::Acquire), 2);
}
