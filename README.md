# rsevents

[![crates.io](https://img.shields.io/crates/v/rsevents.svg)](https://https://crates.io/crates/rsevents)
[![docs.rs](https://docs.rs/rsevents/badge.svg)](https://docs.rs/crate/rsevents)

This crate contains a cross-platform implementation of auto and manual reset events similar to those
found in Microsoft Windows, implemented on top of the core parking lot crate.

## About Events

An event is best compared to a waitable boolean, and can have either of two states: set and unset.
Callers may directly wait on the event itself, foregoing the need for an associated condition
variable and mutex.

Events come in two flavors, `AutoResetEvent` and `ManualResetEvent`, which differ in their behavior
when it comes to setting (aka signalling) an event. An `AutoResetEvent`, once signalled, permits
exactly one (and only one) past or future caller to unblock while waiting for the same event,
whereas a `ManualResetEvent` lacks such fine-grained control and is either signalled and unblocked
for all past/future waiters or none (until its state is toggled).

## Example

```rust
// create a new, initially unset event
let event = AutoResetEvent::new(State::Unset);

// and wrap it in an ARC to allow sharing across thread boundaries
let event = Arc::new(event);

// create a worker thread to complete some task
{
	let shared = event.clone();
	std::thread::spawn(|| {
		// perform some task
		...
		// and signal to ONE waiting thread that the result is ready
		shared.set();
	});
}

...

// wait for the spawned thread to finish the queued work
event.wait();

```

## Types

Structs `ManualResetEvent` and `AutoResetEvent`, both implementing the trait `Event` which exposes
an API that permits waiting indefinitely, waiting for zero time, and waiting for a fixed time limit
(`Duration`) for an event to be triggered.

See the documentation for more info.

## When to use

Generally speaking, a mutex or condition variable should always be preferred when it comes to
protecting a critical section and ensuring exclusive access due to their well-understood
synchronization paradigms and wide support. However, there are other times when a synchronization
primitve _not_ coupled to an explicit critical section or protected data is required, in which case
it similarly does not make sense to use a mutex and a critical section when a single alternative
synchronization primitive is what is actually required.

Any time you find yourself needing a `Mutex<bool>` and an associated condition variable to
set/test/clear a boolean flag to synchronize state across threads, you should reach for either a
manual- or auto-reset event instead.

## About

rsevents is written and maintained by Mahmoud Al-Qudsi \<mqudsi@neosmart.net\> of NeoSmart
Technologies \<https://neosmart.net/\> and released to the general public under the terms of the MIT
public license.
