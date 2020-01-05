//! [VClock](https://gitlab.com/ufoot/vclock) is an experimental vector clock implementated in [Rust](https://www.rust-lang.org/).
//!
//! It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
//! In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.
//!
//! ![VClock icon](https://gitlab.com/ufoot/vclock/raw/master/vclock.png)

mod base;
pub use base::*;
