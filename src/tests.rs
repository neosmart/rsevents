use crate::*;
use std::sync::Arc;
use std::thread;

#[test]
fn sanity_check_set() {
    let event = RawEvent::new(AVAILABLE_BIT);
    assert_eq!(true, event.test_try_unlock_one());
}

#[test]
fn sanity_check_unset() {
    let event = RawEvent::new(0);
    assert_eq!(false, event.test_try_unlock_one());
}

#[test]
fn basic_set_unlock_one() {
    let event = RawEvent::new(0);
    event.set_one();
    assert_eq!(true, event.test_try_unlock_one());
}

#[test]
fn basic_set_unlock_all() {
    let event = RawEvent::new(0);
    event.set_one();
    assert_eq!(true, event.try_unlock_all());
    assert_eq!(true, event.try_unlock_all());
}

#[test]
fn basic_reset_one() {
    let event = RawEvent::new(AVAILABLE_BIT);
    event.reset();
    assert_eq!(false, event.test_try_unlock_one());
}

#[test]
fn basic_reset_all() {
    let event = RawEvent::new(AVAILABLE_BIT);
    event.reset();
    assert_eq!(false, event.try_unlock_all());
}

#[test]
fn basic_double_unlock_auto() {
    let event = AutoResetEvent::new(State::Set);
    assert_eq!(true, event.wait0());
    assert_eq!(false, event.wait0());
}

#[test]
fn basic_double_unlock_manual() {
    let event = ManualResetEvent::new(State::Set);
    assert_eq!(true, event.wait0());
    assert_eq!(true, event.wait0());
}

#[test]
fn auto_event_timeout() {
    let event = AutoResetEvent::new(EventState::Unset);
    assert_eq!(false, event.wait_for(Duration::from_micros(200)));
}

#[test]
fn manual_event_timeout() {
    let event = ManualResetEvent::new(EventState::Unset);
    assert_eq!(false, event.wait_for(Duration::from_micros(200)));
}

#[test]
fn saturating_set() {
    let event = AutoResetEvent::new(EventState::Unset);
    event.set();
    event.set();
    assert_eq!(true, event.wait0());
    assert_eq!(false, event.wait0());
}

#[test]
fn auto_event_no_timeout() {
    let thread_spawned = Arc::new(ManualResetEvent::new(EventState::Unset));
    let event = Arc::new(AutoResetEvent::new(EventState::Unset));
    let thread = {
        let thread_spawned = thread_spawned.clone();
        let event = event.clone();
        thread::spawn(move || {
            thread_spawned.set();
            // assert_eq!(false, event.wait0());
            event.wait_for(Duration::from_secs(1))
        })
    };
    // Try to avoid the event being available when the thread first checks by sleeping
    // until the thread has been spawned.
    thread_spawned.wait();
    thread::sleep(Duration::from_millis(200));
    event.set();

    assert!(matches!(thread.join(), Ok(true)));
}

#[test]
fn manual_event_no_timeout() {
    let thread_spawned = Arc::new(ManualResetEvent::new(EventState::Unset));
    let event = Arc::new(ManualResetEvent::new(EventState::Unset));
    let thread = {
        let thread_spawned = thread_spawned.clone();
        let event = event.clone();
        thread::spawn(move || {
            thread_spawned.set();
            // assert_eq!(false, event.wait0());
            event.wait_for(Duration::from_secs(1))
        })
    };
    // Try to avoid the event being available when the thread first checks by sleeping
    // until the thread has been spawned.
    thread_spawned.wait();
    thread::sleep(Duration::from_millis(200));
    event.set();

    assert!(matches!(thread.join(), Ok(true)));
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
    use tiny_rng::{Rand, Rng};

    const THREAD_COUNT: usize = 20;
    static EVENT1: AutoResetEvent = AutoResetEvent::new(State::Unset);
    static EVENT2: AutoResetEvent = AutoResetEvent::new(State::Unset);

    // We are not using an atomic here to test whether or not AutoResetEvent set/wait()
    // pairs guarantee memory order.
    static mut SUCCEED_COUNT: usize = 0_usize;

    let create_waiter = move |i: usize| {
        thread::spawn(move || {
            // eprintln!("Thread {} spawned", i);
            // Wait for exclusive access
            if !EVENT1.wait_for(Duration::from_secs_f32(1.5)) {
                panic!("Worker thread {} timed out waiting for EVENT1", i);
            }
            unsafe {
                SUCCEED_COUNT += 1;
            }
            // Allow another thread in
            EVENT2.set();
            // eprintln!("Worker thread {} set EVENT2", i);
        })
    };

    // Create threads that will contend for the event, but don't create them all at once.
    // This hopefully lets us test a mix of fast obtain, try-park-but-obtain, and park-then-obtain
    // scenarios.

    let spawner = thread::spawn(move || {
        let mut join_handles = Vec::new();
        for i in 0..THREAD_COUNT {
            let mut rng = Rng::from_seed(i as u64);
            join_handles.push(create_waiter(i));
            thread::sleep(Duration::from_micros(rng.rand_range_u64(0, 300)));
            std::thread::yield_now();
        }
        // eprintln!("Spawned {} threads", THREAD_COUNT);

        join_handles
    });

    // Hopefully let just one event through, observing the initial value
    EVENT1.set();

    // Yield for 100 time slices
    for _ in 0..100 {
        std::thread::yield_now();
    }

    for i in 0..THREAD_COUNT {
        if !EVENT2.wait_for(Duration::from_secs(4)) {
            panic!("Timeout waiting for worker thread {} EVENT2.", i);
        }
        assert_eq!(unsafe { SUCCEED_COUNT }, i + 1);
        EVENT1.set();
    }

    let join_handles = spawner.join().unwrap();
    for jh in join_handles {
        jh.join().unwrap();
    }
}
