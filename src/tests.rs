use crate::*;
use std::sync::Arc;
use std::thread;

#[test]
fn sanity_check_set() {
    let event = RawEvent::new(true);
    assert_eq!(true, event.try_unlock_one());
}

#[test]
fn sanity_check_unset() {
    let event = RawEvent::new(false);
    assert_eq!(false, event.try_unlock_one());
}

#[test]
fn basic_set_unlock_one() {
    let event = RawEvent::new(false);
    event.set_one();
    assert_eq!(true, event.try_unlock_one());
}

#[test]
fn basic_set_unlock_all() {
    let event = RawEvent::new(false);
    event.set_one();
    assert_eq!(true, event.try_unlock_all());
    assert_eq!(true, event.try_unlock_all());
}

#[test]
fn basic_reset_one() {
    let event = RawEvent::new(true);
    event.reset();
    assert_eq!(false, event.try_unlock_one());
}

#[test]
fn basic_reset_all() {
    let event = RawEvent::new(true);
    event.reset();
    assert_eq!(false, event.try_unlock_all());
}

#[test]
fn basic_double_unlock_auto() {
    let event = AutoResetEvent::new(EventState::Set);
    assert_eq!(true, event.wait0());
    assert_eq!(false, event.wait0());
}

#[test]
fn basic_double_unlock_manual() {
    let event = ManualResetEvent::new(EventState::Set);
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
    thread.join().unwrap();
}

#[test]
/// Verify that when an [`AutoResetEvent`] is made available only one waiting thread gets through at
/// a time, and verify cache coherence of unsynchronized access to a non-atomic variable is
/// maintained by the calls to set() and wait().
fn auto_reset_cache_coherence() {
    const THREAD_COUNT: usize = 20;
    let event = Arc::new(AutoResetEvent::new(State::Unset));
    // event2 is used to signal that a waiter has finished
    let event2 = Arc::new(AutoResetEvent::new(State::Unset));

    // We are not using an atomic here to ensure that AutoResetEvent set/wait()
    // pairs guarantee memory order.
    static mut SUCCEED_COUNT: usize = 0_usize;

    let create_waiter = || {
        let event = event.clone();
        let event2 = event2.clone();
        thread::spawn(move || {
            // Wait for exclusive access
            event.wait();
            unsafe { SUCCEED_COUNT += 1; }
            // Allow another thread in
            event2.set();
        })
    };

    // Create 50 threads that will contend for the event
    let mut join_handles = Vec::new();
    for _ in 0..THREAD_COUNT {
        join_handles.push(create_waiter());
    }

    // Hopefully let just one event through, observing the initial value
    event.set();

    // Yield for 100 time slices
    for _ in 0..100 {
        std::thread::yield_now();
    }

    for i in 0..THREAD_COUNT {
        event2.wait();
        assert_eq!(unsafe { SUCCEED_COUNT }, i + 1);
        event.set();
    }

    for jh in join_handles {
        jh.join().unwrap();
    }
}
