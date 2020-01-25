//! [VClock](https://gitlab.com/ufoot/vclock) is an experimental vector clock implementated in [Rust](https://www.rust-lang.org/).
//!
//! It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
//! In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.
//!
//! ![VClock icon](https://gitlab.com/ufoot/vclock/raw/master/vclock.png)
//!
//! # Examples
//!
//! Basic usage:
//!
//! ```
//! use vclock::VClock;
//!
//! let c1 = VClock::new("a");     // c1 is now a:1
//! let mut c2 = VClock::new("b"); // c2 is now b:1
//! c2.incr("a");                  // c1 is now a:1,b:1
//! assert!(c1 < c2, "c1 is a parent of c2");
//! ```
//!
//! Here is how to generate a conflict:
//!
//! ```
//! use vclock::VClock;
//!
//! let mut c1: VClock<&str>=VClock::default();
//!
//! c1.incr("a");
//! c1.incr("a");
//! c1.incr("a");
//! c1.incr("a");
//! c1.incr("b"); // c1 is now a:4, b:1
//!
//! let c2 = c1.next("a"); // c2 is now a:5,b:1
//! let c3 = c1.next("b"); // c3 is now a:4,b:2
//!
//! // Now let's assert there is a relationship c1 -> c2 and c1 -> c3.
//! // By relationship, we mean that there is a forward path of updates
//! // using incr() or next() from one member to the other.
//! assert!(c1<=c2, "c1={} is a parent of c2={}", c1, c2);
//! assert!(c2>=c1, "c2={} is a child of c1={}", c2, c1);
//! assert!(c1<=c3, "c1={} c1 is a parent of c3={}", c1, c3);
//! assert!(c3>=c1, "c3={} c1 is a child of c1={}", c3, c1);
//!
//! // But there is no relationship between c2 and c3.
//! // In a distributed system with concurrent updates of an object,
//! // this allows the detection of a conflict.
//! assert!(!(c2<=c3), "c2={} is not a parent of c3={}", c2, c3);
//! assert!(!(c2>=c3), "c2={} is not a child of c3={}", c2, c3);
//! assert!(!(c3<=c2), "c3={} is not a parent of c2={}", c3, c2);
//! assert!(!(c3>=c2), "c3={} is not a child of c2={}", c3, c2);
//! ```
//!
//! Also, two objects having a different history path, but the same
//! final state, will be considered the same. It is up to the program
//! to ensure only one agent updates a given key:
//!
//! ```
//! use vclock::VClock;
//!
//! let mut c1 = VClock::new("a"); // c1 is now a:1
//! let mut c2 = VClock::new("b"); // c2 is now b:1
//! c1.incr("c"); // c1 is now a:1, c:1
//! c1.incr("b"); // c1 is now a:1, b:1, c:1
//! c2.incr("a"); // c2 is now a:1, b:1, which is a value c1 never had
//! c2.incr("c"); // c2 is now a:1, b:1, c:1
//!
//! // The following test shows clocks are considered the same.
//! // In a distributed system using vector clocks, only one agent
//! // would update a given key, and when updating this key, it should
//! // ensure than there is no conflict with the latest version it had locally.
//! assert_eq!(c1, c2, "c1={} and c2={} represent the same final state", c1, c2);
//! ```
//!
//! A typical conflict resolution:
//!
//! ```
//! use std::collections::HashMap;
//! use vclock::VClock;
//!
//! // A dummy object with maintains a vector clock along with some data,
//! // here just a byte, to avoid complexifying the example with other issues.
//! #[derive(Default)]
//! struct Obj<'a> {
//!     vc: VClock<&'a str>,
//!     val: u8,
//! }
//!
//! impl<'a> Obj<'a> {
//!     // Update the data stored within the object. If there's no conflict,
//!     // the data is updated, the clock is set to the last value received,
//!     // and the function returns None.
//!     // If there is a conflict, then the previous data is returned, along
//!     // with the merged clock.
//!     fn update(
//!         &mut self,
//!         remote_clock: &VClock<&'a str>,
//!         val: u8,
//!     ) -> Option<(u8, VClock<&str>)> {
//!         if &self.vc < remote_clock {
//!             // Update value, no conflict
//!             self.vc = remote_clock.clone();
//!             self.val = val;
//!             None
//!         } else {
//!             // History conflict, update the clock, return the value,
//!             // and let the caller deal with it.
//!             Some((self.val, self.vc.merge(remote_clock)))
//!         }
//!     }
//! }
//!
//! let mut obj = Obj::default();
//! let mut h1 = HashMap::<&str,u64>::new();
//! h1.insert("a", 42);
//! let c1 = VClock::<&str>::from(h1);
//! assert_eq!(None, obj.update(&c1, 10), "no history, no problem");
//!
//! let mut h2 = HashMap::<&str,u64>::new();
//! h2.insert("a", 42);
//! h2.insert("b", 10);
//! let c2 = VClock::<&str>::from(h2);
//! assert_eq!(None, obj.update(&c2, 100), "forward history, updating");
//!
//! let mut h3 = HashMap::<&str,u64>::new();
//! h3.insert("a", 43);
//! h3.insert("b", 9);
//! let c3 = VClock::<&str>::from(h3);
//! let mut h4 = HashMap::<&str,u64>::new();
//! h4.insert("a", 43);
//! h4.insert("b", 10);
//! let c4 = VClock::<&str>::from(h4);
//! assert_eq!(Some((100, c4)), obj.update(&c3, 50), "conflict between keys");
//! ```

mod base;
pub use base::*;
