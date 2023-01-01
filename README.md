# VClock

[VClock](https://gitlab.com/liberecofr/vclock) is an experimental vector clock implemented in [Rust](https://www.rust-lang.org/).

It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.

![VClock icon](https://gitlab.com/liberecofr/vclock/raw/master/vclock.png)

# Status

For now this is a toy project, clearly *NOT* suitable for production use.

[![Build Status](https://gitlab.com/liberecofr/vclock/badges/master/pipeline.svg)](https://gitlab.com/liberecofr/vclock/pipelines)

# Usage

```rust
use vclock::VClock;

let c1 = VClock::new("a");     // c1 is now a:1
let mut c2 = VClock::new("b"); // c2 is now b:1
c2.incr("a");                  // c1 is now a:1,b:1
assert!(c1 < c2, "c1 is a parent of c2");
```

# Links

* [crate](https://crates.io/crates/vclock) on crates.io
* [doc](https://docs.rs/vclock/) on docs.rs
* [source](https://gitlab.com/liberecofr/vclock/tree/master) on gitlab.com

# License

VClock is licensed under the [MIT](https://gitlab.com/liberecofr/vclock/blob/main/LICENSE) license.
