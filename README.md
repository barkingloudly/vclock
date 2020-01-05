# VClock

[VClock](https://gitlab.com/ufoot/vclock) is an experimental vector clock implemented in [Rust](https://www.rust-lang.org/).

It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.

![VClock icon](https://gitlab.com/ufoot/vclock/raw/master/vclock.png)

# Status

For now this is a toy project, clearly *NOT* suitable for production use.

[![Build Status](https://gitlab.com/ufoot/vclock/badges/master/pipeline.svg)](https://gitlab.com/ufoot/vclock/pipelines)

# Usage

[TODO...]

# License

VClock is licensed under the [MIT](https://gitlab.com/ufoot/vclock/blob/master/LICENSE) license.
