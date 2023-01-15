// Copyright (C) 2023 Christian Mauduit <ufoot@ufoot.org>

//! [VClock](https://gitlab.com/liberecofr/vclock) is a vector clock implementated in [Rust](https://www.rust-lang.org/).
//!
//! It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
//! In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.
//!
//! ![VClock icon](https://gitlab.com/liberecofr/vclock/raw/master/vclock.png)
//!
//! # Examples
//!
//! Basic usage:
//!
//! ```
//! use vclock::VClock;
//!
//! let c1 = VClock::<&str, u64>::new("a");  // c1 is now a:0
//! let mut c2 = VClock::new("b");           // c2 is now b:0
//! c2.incr(&"a");                           // c1 is now a:0,b:0
//! assert!(c1 < c2, "c1 should be a child of c2");
//! ```
//!
//! Here is how to generate a conflict:
//!
//! ```
//! use vclock::VClock;
//!
//! let mut c1: VClock<&str>=VClock::default();
//!
//! c1.incr(&"a");
//! c1.incr(&"a");
//! c1.incr(&"a");
//! c1.incr(&"a");
//! c1.incr(&"b"); // c1 is now a:3, b:0
//!
//! let c2 = c1.clone().next(&"a"); // c2 is now a:4,b:0
//! let c3 = c1.clone().next(&"b"); // c3 is now a:3,b:1
//!
//! // Now let's assert there is a relationship c1 -> c2 and c1 -> c3.
//! // By relationship, we mean that there is a forward path of updates
//! // using incr() or next() from one member to the other.
//! assert!(c1<=c2, "c1={} should be a child of c2={}", c1, c2);
//! assert!(c2>=c1, "c2={} should be a parent of c1={}", c2, c1);
//! assert!(c1<=c3, "c1={} c1 should be a child of c3={}", c1, c3);
//! assert!(c3>=c1, "c3={} c1 should be a parent of c1={}", c3, c1);
//!
//! // But there is no relationship between c2 and c3.
//! // In a distributed system with concurrent updates of an object,
//! // this allows the detection of a conflict.
//! assert!(!(c2<=c3), "c2={} should not be a child of c3={}", c2, c3);
//! assert!(!(c2>=c3), "c2={} should not be a parent of c3={}", c2, c3);
//! assert!(!(c3<=c2), "c3={} should not be a child of c2={}", c3, c2);
//! assert!(!(c3>=c2), "c3={} should not be a parent of c2={}", c3, c2);
//! ```
//!
//! Also, two objects having a different history path, but the same
//! final state, will be considered the same. It is up to the program
//! to ensure only one agent updates a given key:
//!
//! ```
//! use vclock::VClock;
//!
//! let mut c1 = VClock::<&str, u64>::new("a"); // c1 is now a:0
//! let mut c2 = VClock::<&str, u64>::new("b"); // c2 is now b:0
//! c1.incr(&"c"); // c1 is now a:0, c:0
//! c1.incr(&"b"); // c1 is now a:0, b:0, c:0
//! c2.incr(&"a"); // c2 is now a:0, b:0, which is a value c1 never had
//! c2.incr(&"c"); // c2 is now a:0, b:0, c:0
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
//! struct Obj {
//!     vc: VClock<String>,
//!     val: u8,
//! }
//!
//! impl Obj {
//!     // Update the data stored within the object. If there's no conflict,
//!     // the data is updated, the clock is set to the last value received,
//!     // and the function returns None.
//!     // If there is a conflict, then the previous data is returned, along
//!     // with the merged clock.
//!     fn update(
//!         &mut self,
//!         remote_clock: &VClock<String>,
//!         val: u8,
//!     ) -> Option<(u8, VClock<String>)> {
//!         if &self.vc < remote_clock {
//!             // Update value, no conflict
//!             self.vc = remote_clock.clone();
//!             self.val = val;
//!             None
//!         } else {
//!             // History conflict, update the clock, return the value,
//!             // and let the caller deal with it.
//!             Some((self.val, self.vc.clone().combine(remote_clock)))
//!         }
//!     }
//! }
//!
//! let mut obj = Obj::default();
//! let mut h1 = HashMap::<String, usize>::new();
//! h1.insert("a".to_string(), 42);
//! let c1 = VClock::<String>::from(h1);
//! assert_eq!(None, obj.update(&c1, 10), "no history, no problem");
//!
//! let mut h2 = HashMap::<String, usize>::new();
//! h2.insert("a".to_string(), 42);
//! h2.insert("b".to_string(), 10);
//! let c2 = VClock::<String>::from(h2);
//! assert_eq!(None, obj.update(&c2, 100), "forward history, updating");
//!
//! let mut h3 = HashMap::<String, usize>::new();
//! h3.insert("a".to_string(), 43);
//! h3.insert("b".to_string(), 9);
//! let c3 = VClock::<String>::from(h3);
//! let mut h4 = HashMap::<String, usize>::new();
//! h4.insert("a".to_string(), 43);
//! h4.insert("b".to_string(), 10);
//! let c4 = VClock::<String>::from(h4);
//! assert_eq!(Some((100, c4)), obj.update(&c3, 50), "conflict between keys");
//! ```
//!
//! Use custom types:
//!
//! ```
//! use vclock::VClock;
//! use num_bigint::BigUint;
//! use std::hash::Hash;
//!
//! #[derive(Hash, Eq, PartialEq, Clone)]
//! struct Coord{
//!     x: isize,
//!     y: isize,
//! }
//!
//! let key = Coord{x: 1, y: 2};
//! let mut c1 = VClock::<Coord, BigUint>::default();
//! c1.incr(&key); // BigUint, can grow infinitely... (almost)
//! ```

#[cfg(feature = "bigint")]
use num_bigint::BigUint;
use std::clone::Clone;
use std::cmp::Eq;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Add, AddAssign};

/// A vector clock using a u8 counter.
///
/// # Examples
///
/// ```
/// use vclock::VClock8;
///
/// // key type can be inferred
/// let mut c = VClock8::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(1), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
pub type VClock8<K> = VClock<K, u8>;

/// A vector clock using a u16 counter.
///
/// # Examples
///
/// ```
/// use vclock::VClock16;
///
/// // key type can be inferred
/// let mut c = VClock16::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(1), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
pub type VClock16<K> = VClock<K, u16>;

/// A vector clock using a u32 counter.
///
/// # Examples
///
/// ```
/// use vclock::VClock32;
///
/// // key type can be inferred
/// let mut c = VClock32::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(1), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
pub type VClock32<K> = VClock<K, u32>;

/// A vector clock using a u64 counter.
///
/// # Examples
///
/// ```
/// use vclock::VClock64;
///
/// // key type can be inferred
/// let mut c = VClock64::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(1), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
pub type VClock64<K> = VClock<K, u64>;

/// A vector clock using a u128 counter.
///
/// # Examples
///
/// ```
/// use vclock::VClock128;
///
/// // key type can be inferred
/// let mut c = VClock128::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(1), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
pub type VClock128<K> = VClock<K, u128>;

/// A vector clock using a bigint counter.
///
/// Requires feature "bigint".
///
/// # Examples
///
/// ```
/// use vclock::VClockBig;
///
/// // key type can be inferred
/// let mut c = VClockBig::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// c.incr(&"b");
/// assert_eq!(2, c.get(&"a").unwrap().to_u64_digits()[0]);
/// assert_eq!(1, c.get(&"b").unwrap().to_u64_digits()[0]);
/// assert_eq!(None, c.get(&"c"));
/// ```
#[cfg(feature = "bigint")]
pub type VClockBig<K> = VClock<K, BigUint>;

/// VClock encapsulates the vector clock data. Internally it's just
/// a simple hash map containing integers.
///
/// # Examples
///
/// ```
/// use vclock::VClock;
///
/// let mut c: VClock<&str>=VClock::default();
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"a");
/// c.incr(&"b");
/// assert_eq!(Some(3), c.get(&"a"));
/// assert_eq!(Some(0), c.get(&"b"));
/// assert_eq!(None, c.get(&"c"));
/// ```
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct VClock<K = usize, I = usize>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    c: HashMap<K, I>,
}

impl<K, I> VClock<K, I>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    /// Initialize a new vector clock with only one contributor.
    /// It is useful to avoid the new() then incr() pattern, as it
    /// performs both operations at once, without copying anything.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let c = VClock::<&str, u16>::new("foo"); // c is now foo:0
    /// assert_eq!("{len: 1, weight: 1, max: {\"foo\": 0}}", format!("{}", c));
    /// ```
    pub fn new(key: K) -> VClock<K, I> {
        let mut first = VClock {
            c: HashMap::<K, I>::default(),
        };
        first.c.insert(key, I::default());
        first
    }

    /// Returns the counter associated to a given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::new("foo"); // c is now foo:0
    /// c.incr(&"foo"); // c is now foo:1
    /// c.incr(&"bar"); // c is now foo:1, bar:0
    /// assert_eq!(1, c.get(&"foo").unwrap());
    /// assert_eq!(0, c.get(&"bar").unwrap());
    /// assert_eq!(None, c.get(&"unknown"));
    /// ```
    pub fn get(&self, key: &K) -> Option<I> {
        match self.c.get(key) {
            Some(v) => Some(v.clone()),
            None => None,
        }
    }

    /// Returns the number of elements in a VClock.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::<&str, u8>::default();
    /// assert_eq!(0, c.len());
    /// c.incr(&"foo");
    /// assert_eq!(1, c.len());
    /// c.incr(&"foo");
    /// assert_eq!(1, c.len());
    /// c.incr(&"bar");
    /// assert_eq!(2, c.len());
    /// ```
    pub fn len(&self) -> usize {
        return self.c.len();
    }

    /// Returns the total of all values, plus the number of values.
    ///
    /// This is mostly a debugging feature. You should not use this to compare
    /// clocks. If a < b then a.weight() < b.weight() but the reciprocity is not true.
    /// However it can be useful to have this information when auditing behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::<&str, u32>::default();
    /// assert_eq!(0, c.weight());
    /// c.incr(&"foo");
    /// assert_eq!(1, c.weight());
    /// c.incr(&"foo");
    /// assert_eq!(2, c.weight());
    /// c.incr(&"foo");
    /// assert_eq!(3, c.weight());
    /// c.incr(&"bar");
    /// assert_eq!(4, c.weight());
    /// c.incr(&"bar");
    /// assert_eq!(5, c.weight());
    /// ```
    pub fn weight(&self) -> I {
        let mut weight = I::default();
        for (_, v) in &(self.c) {
            weight += v.clone() + I::from(1);
        }
        weight
    }

    /// Returns the max key,value pair.
    ///
    /// This is mostly a debugging feature. You should not use this to compare
    /// clocks. If a < b then a.max() <= b.max() but the reciprocity is not true.
    /// However it can be useful to have this information when auditing behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::default();
    /// assert_eq!(None, c.max());
    /// c.incr(&"foo");
    /// assert_eq!((&"foo", 0), c.max().unwrap());
    /// c.incr(&"foo");
    /// assert_eq!((&"foo", 1), c.max().unwrap());
    /// c.incr(&"bar");
    /// assert_eq!((&"foo", 1), c.max().unwrap());
    /// ```
    pub fn max(&self) -> Option<(&K, I)> {
        let mut max_value = I::default();
        let mut max_key: Option<&K> = None;
        for (k, v) in &(self.c) {
            if max_value <= v.clone() {
                max_key = Some(&k);
                max_value = v.clone();
            }
        }
        match max_key {
            Some(k) => Some((k, max_value)),
            _ => None,
        }
    }

    /// Increment a vector clock in-place.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::<&str, u64>::new("foo"); // c is now foo:0
    /// c.incr(&"foo"); // c is now foo:1
    /// c.incr(&"bar"); // c is now foo:1, bar:0
    /// assert_eq!("{len: 2, weight: 3, max: {\"foo\": 1}}", format!("{}", c));
    /// ```
    pub fn incr(&mut self, key: &K) {
        let value = match self.c.get(key) {
            Some(v) => v.clone() + I::from(1),
            None => I::default(),
        };
        self.c.insert(key.clone(), value);
    }

    /// Increments a vector clock. This is pretty much the same as incr
    /// but it takes ownership on the vector clock.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let c1 = VClock::<&str, u16>::new("a");
    /// let c2 = c1.clone().next(&"a").next(&"b");
    /// assert_eq!(1, c2.get(&"a").unwrap());
    /// assert_eq!(0, c2.get(&"b").unwrap());
    /// ```
    pub fn next(mut self, key: &K) -> VClock<K, I> {
        self.incr(key);
        self
    }

    /// Merge a key with another one, in-place, taking the max of all history points.
    ///
    /// If there is a parentship between a and b, just take the greater of both.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c1 = VClock::<&str, u32>::new("a");
    /// let c2 = VClock::<&str, u32>::new("b");
    /// c1.merge(&c2);
    /// assert_eq!(Some(0), c1.get(&"a"));
    /// assert_eq!(Some(0), c1.get(&"b"));
    /// ```
    pub fn merge(&mut self, other: &VClock<K, I>) {
        // copy all the existing keys for other, which are not the key we increment
        for (k, v) in &(other.c) {
            // insert the key only if it's bigger than what we had
            if match self.c.get(k) {
                Some(v2) => v2 < v,
                None => true,
            } {
                self.c.insert(k.clone(), v.clone());
            }
        }
    }

    /// Combine a key with another one, taking ownership.
    ///
    /// If there is a parentship between a and b, just take the greater of both.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let c1 = VClock::new("a");
    /// let c2 = VClock::new("b").next(&"b");
    /// let c3 = VClock::new("c");
    /// let c4 = c1.combine(&c2).combine(&c3);
    /// assert_eq!(0, c4.get(&"a").unwrap());
    /// assert_eq!(1, c4.get(&"b").unwrap());
    /// assert_eq!(0, c4.get(&"c").unwrap());
    /// ```
    pub fn combine(mut self, other: &VClock<K, I>) -> VClock<K, I> {
        self.merge(other);
        self
    }
}

/// Vector clocks are partially ordered, and this is exactly what they
/// are useful for. If the order is explicitly returned, it means one
/// can fast-forward or fast-rewind from one point to the other in history.
/// If not, that is, if None is returned, it means there is a conflict, and
/// no way to directly go to one point from the other.
impl<K, I> std::cmp::PartialOrd for VClock<K, I>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    /// Compares the vector clock with another one. Note that really,
    /// this is a partial order, if both a<=b and a>=b return false,
    /// it means there is no direct parentship link between clocks.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    /// use std::cmp::Ordering;
    ///
    /// // Two vector clocks holding same values are equal.
    /// let mut c1 = VClock::<&str, u32>::new("a");
    /// let mut c2 = VClock::<&str, u32>::new("a");
    /// assert_eq!(Some(Ordering::Equal), c1.partial_cmp(&c2));
    /// assert!(c1 <= c2);
    ///
    /// // Two vector clocks with a direct parentship are ordered.
    /// c2.incr(&"a");
    /// assert_eq!(Some(Ordering::Less), c1.partial_cmp(&c2));
    /// assert_eq!(Some(Ordering::Greater), c2.partial_cmp(&c1));
    /// assert!(c1 < c2);
    /// assert!(c2 > c1);
    ///
    /// // Two vector clocks without a direct parentship are not ordered.
    /// c1.incr(&"b");
    /// assert_eq!(None, c1.partial_cmp(&c2));
    /// assert_eq!(None, c2.partial_cmp(&c1));
    /// assert!(!(c1 < c2));
    /// assert!(!(c2 > c1));
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut has_less: bool = false;
        let mut has_greater: bool = false;

        for (k, v) in &(self.c) {
            match other.c.get(k) {
                Some(other_v) => {
                    if v > other_v {
                        if !has_less {
                            has_greater = true;
                        } else {
                            return None;
                        }
                    }
                    if v < other_v {
                        if !has_greater {
                            has_less = true;
                        } else {
                            return None;
                        }
                    }
                }
                None => {
                    if !has_less {
                        has_greater = true;
                    } else {
                        return None;
                    }
                }
            }
        }

        for (k, v) in &(other.c) {
            match self.c.get(k) {
                Some(self_v) => {
                    if v > self_v {
                        if !has_greater {
                            has_less = true;
                        } else {
                            return None;
                        }
                    }
                    if v < self_v {
                        if !has_less {
                            has_greater = true;
                        } else {
                            return None;
                        }
                    }
                }
                None => {
                    if !has_greater {
                        has_less = true;
                    } else {
                        return None;
                    }
                }
            }
        }
        if has_less && !has_greater {
            return Some(Ordering::Less);
        }
        if has_greater && !has_less {
            return Some(Ordering::Greater);
        }
        if has_less && has_greater {
            // Normally this should be useless as there are shortcuts
            // before setting has_greater or has_less. But better be safe than sorry.
            return None;
        }
        Some(Ordering::Equal)
    }
}

impl<K, I> From<HashMap<K, I>> for VClock<K, I>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    /// Build a vector clock from a hash map containing u64 values.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    /// use std::collections::HashMap;
    ///
    /// let mut m = HashMap::new();
    /// m.insert("a", 3u64);
    /// m.insert("b", 5u64);
    /// let c = VClock::from(m);
    /// assert_eq!(2, c.len());
    /// assert_eq!(3, c.get(&"a").unwrap());
    /// assert_eq!(5, c.get(&"b").unwrap());
    /// ```
    fn from(src: HashMap<K, I>) -> VClock<K, I> {
        VClock { c: src }
    }
}

impl<K, I> From<VClock<K, I>> for HashMap<K, I>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    /// Build a vector clock from a hash map containing u64 values.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    /// use std::collections::HashMap;
    ///
    /// let mut c = VClock::default();
    /// c.incr(&"a");
    /// c.incr(&"a");
    /// c.incr(&"b");
    /// let m = HashMap::from(c);
    /// assert_eq!(2, m.len());
    /// assert_eq!(Some(&1), m.get(&"a"));
    /// assert_eq!(Some(&0), m.get(&"b"));
    /// ```
    fn from(src: VClock<K, I>) -> HashMap<K, I> {
        src.c
    }
}

impl<K, I> std::fmt::Display for VClock<K, I>
where
    K: Eq + Hash + Clone + std::fmt::Display,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone + std::fmt::Display,
{
    /// Pretty print the vector clock, it does not dump all the data,
    /// only a few key values.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let mut c = VClock::<&str, usize>::default();
    /// assert_eq!("{len: 0, weight: 0}", format!("{}", c));
    /// c.incr(&"a");
    /// assert_eq!("{len: 1, weight: 1, max: {\"a\": 0}}", format!("{}", c));
    /// c.incr(&"b");
    /// c.incr(&"b");
    /// assert_eq!("{len: 2, weight: 3, max: {\"b\": 1}}", format!("{}", c));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let weight = self.weight();
        let max = self.max();
        match max {
            Some(m) => write!(
                f,
                "{{len: {}, weight: {}, max: {{\"{}\": {}}}}}",
                self.c.len(),
                weight,
                m.0,
                m.1
            ),
            None => write!(f, "{{len: {}, weight: {}}}", self.c.len(), weight),
        }
    }
}

impl<K, I> std::default::Default for VClock<K, I>
where
    K: Eq + Hash + Clone,
    I: Add<I, Output = I> + AddAssign<I> + From<u8> + Ord + Default + Clone,
{
    /// Return a VClock with no history at all.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    ///
    /// let c1: VClock<&str, u64> = VClock::default();
    /// assert_eq!(0, c1.len());
    /// assert_eq!(0, c1.weight());
    /// ```
    fn default() -> VClock<K, I> {
        VClock {
            c: HashMap::<K, I>::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_vclock_default() {
        // let _ = VClock::default(); // does not work
        let _ = VClock::<i16>::default();
        let _ = VClock::<i8, BigUint>::default();
    }

    #[test]
    fn test_vclock_new() {
        let vc1 = VClock::new(17);
        assert_eq!(None, vc1.get(&0));
        assert_eq!(Some(0), vc1.get(&17));

        let vc2 = VClock::<u32>::new(17u32);
        assert_eq!(None, vc2.get(&0u32));
        assert_eq!(Some(0usize), vc2.get(&17u32));

        let vc3 = VClock::<i64, u8>::new(17i64);
        assert_eq!(None, vc3.get(&0i64));
        assert_eq!(Some(0u8), vc3.get(&17i64));

        let vc4 = VClock::<i64, i16>::new(17i64);
        assert_eq!(None, vc4.get(&0i64));
        assert_eq!(Some(0i16), vc4.get(&17i64));
    }

    #[test]
    fn test_vclock_incr() {
        let mut vc = VClock::<i16>::default();
        assert_eq!(None, vc.get(&0));

        vc.incr(&2);
        assert_eq!(None, vc.get(&0));
        assert_eq!(Some(0), vc.get(&2));

        vc.incr(&2);
        assert_eq!(None, vc.get(&0));
        assert_eq!(Some(1), vc.get(&2));

        vc.incr(&3);
        assert_eq!(None, vc.get(&0));
        assert_eq!(Some(1), vc.get(&2));
        assert_eq!(Some(0), vc.get(&3));
    }

    #[test]
    fn test_vclock_next() {
        let vc = VClock::<i16>::default();
        assert_eq!(None, vc.get(&0));

        let vc2 = vc.clone().next(&2);
        assert_eq!(None, vc.get(&0));
        assert_eq!(None, vc.get(&2));
        assert_eq!(Some(0), vc2.get(&2));

        let vc3 = vc.clone().next(&3);
        assert_eq!(None, vc.get(&0));
        assert_eq!(None, vc.get(&2));
        assert_eq!(None, vc.get(&3));
        assert_eq!(Some(0), vc2.get(&2));
        assert_eq!(Some(0), vc3.get(&3));

        let vc3i = vc3.clone().next(&3);
        assert_eq!(None, vc.get(&0));
        assert_eq!(None, vc.get(&2));
        assert_eq!(None, vc.get(&3));
        assert_eq!(Some(0), vc2.get(&2));
        assert_eq!(Some(1), vc3i.get(&3));
    }

    #[test]
    fn test_vclock_debug() {
        let vc = VClock::<i16>::default();
        let vca = vc.next(&42);
        let vcb = vca.next(&42);
        let vcc = vcb.next(&42);
        let repr = format!("{:?}", vcc);
        assert_eq!("VClock { c: {42: 2} }", repr);
    }

    #[test]
    fn test_vclock_compare() {
        let mut vca = VClock::<u32>::default();
        let mut vcb = VClock::<u32>::default();
        assert_eq!(vca, vcb);
        assert_eq!(Some(Ordering::Equal), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Equal), vcb.partial_cmp(&vca));
        vcb.incr(&2);
        assert_eq!(Some(Ordering::Less), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Greater), vcb.partial_cmp(&vca));
        vca.incr(&2);
        assert_eq!(Some(Ordering::Equal), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Equal), vcb.partial_cmp(&vca));
        vca.incr(&2);
        assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
        vca.incr(&3);
        vca.incr(&3);
        vca.incr(&3);
        vcb.incr(&3);
        vcb.incr(&3);
        vcb.incr(&3);
        assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
        vca.incr(&4);
        assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
        assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
        vcb.incr(&4);
        vcb.incr(&4);
        assert_eq!(None, vca.partial_cmp(&vcb));
        assert_eq!(None, vcb.partial_cmp(&vca));
    }

    #[test]
    fn test_vclock_fmt() {
        let mut k = VClock::<i32>::default();
        assert_eq!(String::from("{len: 0, weight: 0}"), format!("{}", k));
        k.incr(&42);
        assert_eq!(
            String::from("{len: 1, weight: 1, max: {\"42\": 0}}"),
            format!("{}", k)
        );
        k.incr(&421);
        k.incr(&421);
        k.incr(&421);
        assert_eq!(
            String::from("{len: 2, weight: 4, max: {\"421\": 2}}"),
            format!("{}", k)
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_vclock_serde_json() {
        let vc = VClock::<i32>::new(42);
        let js = serde_json::json!(&vc).to_string();
        assert_eq!("{\"c\":{\"42\":0}}", js);
        let obj: Result<VClock<i32>, serde_json::Error> = serde_json::from_str(&js);
        match obj {
            Ok(v) => {
                assert_eq!(vc, v);
            }
            Err(_) => unreachable!(),
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_vclock_serde_cbor() {
        let vc = VClock::<i32>::new(42);
        let buf: Vec<u8> = serde_cbor::to_vec(&vc).unwrap();
        let obj: VClock<i32> = serde_cbor::from_slice(&buf).unwrap();
        assert_eq!(vc, obj);
    }

    #[test]
    fn test_vclock_bigint() {
        let mut vc1 = VClock::<&str, BigUint>::default();
        assert_eq!(None, vc1.get(&"not here"));
        vc1.incr(&"k1");
        vc1.incr(&"k1");
        vc1.incr(&"k1");
        assert_eq!("{len: 1, weight: 3, max: {\"k1\": 2}}", format!("{}", &vc1));
        let vc2 = vc1.clone().next(&"k2");
        assert!(vc1 < vc2);
    }

    #[cfg(feature = "bigint")]
    #[test]
    fn test_vclock_big_type() {
        let mut vc1 = VClockBig::default();
        assert_eq!(None, vc1.get(&"not here"));
        vc1.incr(&"k1");
        vc1.incr(&"k1");
        vc1.incr(&"k1");
        assert_eq!("{len: 1, weight: 3, max: {\"k1\": 2}}", format!("{}", &vc1));
        let vc2 = vc1.clone().next(&"k2");
        assert!(vc1 < vc2);
    }
}
