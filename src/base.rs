extern crate serde;

use std::cmp::Ordering;
use std::collections::HashMap;

use serde::{Deserialize, Serialize};

/// VClock encapsulates the vector clock data. Internally it's just
/// a simple hash map containing integers.
///
/// # Examples
///
/// ```
/// use vclock::VClock;
//
/// let mut c1: VClock<&str>=VClock::default();
/// c1.incr("a");
/// c1.incr("a");
/// c1.incr("a");
/// c1.incr("a");
/// c1.incr("b");
/// // c1 is now a:4, b:1
/// ```
#[derive(Debug, PartialEq, Serialize, Deserialize, Clone)]
pub struct VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
{
    c: HashMap<K, u64>,
}

impl<K> VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
{
    /// Initialize a new vector clock with only one contributor.
    /// It is useful to avoid the new() then incr() pattern, as it
    /// performs both operations at once, without copying anything.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let c = VClock::new("foo"); // c is now foo:1
    /// assert_eq!("{len:1,total:1,max:{\"foo\":1}}", format!("{}", c));
    /// ```
    pub fn new(key: K) -> VClock<K> {
        let mut first = VClock {
            c: HashMap::<K, u64>::default(),
        };
        first.c.insert(key, 1);
        first
    }

    /// Increment a vector clock in-place.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let mut c = VClock::new("foo"); // c is now foo:1
    /// c.incr("foo"); // c is now foo:2
    /// c.incr("bar"); // c is now foo:2, bar:1
    /// assert_eq!("{len:2,total:3,max:{\"foo\":2}}", format!("{}", c));
    /// ```
    pub fn incr(&mut self, key: K) {
        let value = match self.c.get(&key) {
            Some(v) => v + 1,
            None => 1,
        };
        self.c.insert(key, value);
    }

    /// Returns the counter associated to a given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let mut c = VClock::new("foo"); // c is now foo:1
    /// c.incr("foo"); // c is now foo:2
    /// c.incr("bar"); // c is now foo:2, bar:1
    /// assert_eq!(2u64, c.get("foo").unwrap());
    /// assert_eq!(1u64, c.get("bar").unwrap());
    /// assert_eq!(None, c.get("unknown"));
    /// ```
    pub fn get(&self, key: K) -> Option<u64> {
        match self.c.get(&key) {
            Some(v) => Some(*v),
            None => None,
        }
    }

    /// Returns the number of elements in a VClock.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let mut c = VClock::default();
    /// assert_eq!(0, c.len());
    /// c.incr("foo");
    /// assert_eq!(1, c.len());
    /// c.incr("foo");
    /// assert_eq!(1, c.len());
    /// c.incr("bar");
    /// assert_eq!(2, c.len());
    /// ```
    pub fn len(&self) -> usize {
        return self.c.len();
    }

    /// Returns the total of all values.
    ///
    /// This is mostly a debugging feature. You should not use this to compare
    /// clocks. If a < b then a.total() < b.total() but the reciprocity is not true.
    /// However it can be useful to have this information when auditing behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let mut c = VClock::default();
    /// assert_eq!(0, c.total());
    /// c.incr("foo");
    /// assert_eq!(1, c.total());
    /// c.incr("foo");
    /// assert_eq!(2, c.total());
    /// c.incr("bar");
    /// assert_eq!(3, c.total());
    /// ```
    pub fn total(&self) -> u64 {
        let mut total: u64 = 0;
        for (_, v) in &(self.c) {
            total += *v;
        }
        total
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
    //
    /// let mut c = VClock::default();
    /// assert_eq!(None, c.max());
    /// c.incr("foo");
    /// assert_eq!((&"foo",1), c.max().unwrap());
    /// c.incr("foo");
    /// assert_eq!((&"foo",2), c.max().unwrap());
    /// c.incr("bar");
    /// assert_eq!((&"foo",2), c.max().unwrap());
    /// ```
    pub fn max(&self) -> Option<(&K, u64)> {
        let mut max_value: u64 = 0;
        let mut max_key: Option<&K> = None;
        for (k, v) in &(self.c) {
            if max_value < *v {
                max_key = Some(&k);
                max_value = *v;
            }
        }
        match max_key {
            Some(k) => Some((k, max_value)),
            _ => None,
        }
    }
}

/// Clone trait is required for key on those methods as they actually
/// do duplicate keys to create a new clock. While technically speaking,
/// it might be doable to not do this, and keep references on keys, in
/// practice it builds up interdependencies between keys and induces
/// a lot of micro management of references and lifetimes.
impl<K> VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::clone::Clone,
{
    /// Increments a vector clock and does a fresh copy. There's no default
    /// implementation of Copy for the vector clock as, indeed, copying it
    /// can be expensive so it's not a good practice to copy it.
    /// However, when incrementing, we might want to actually get a fresh
    /// copy, as typically this incremented clock might refer to a new object.
    pub fn next(&self, key: K) -> VClock<K> {
        // create a new copy
        let mut nxt = VClock::<K>::default();
        // copy all the existing keys, which are not the key we increment
        for (k, v) in &(self.c) {
            if &key != k {
                nxt.c.insert(k.clone(), *v);
            }
        }
        // increment and copy the key we want to increment, specifically
        let value = match self.c.get(&key) {
            Some(v) => v + 1,
            None => 1,
        };
        nxt.c.insert(key.clone(), value);
        // pass the copy
        nxt
    }

    /// Merge two keys, taking the max of all history points.
    ///
    /// If there is a parentship between a and b, merge simply
    /// returns the greater of both. Merge creates a new object
    /// with clones of all keys, so it can be a costly operation
    /// on big keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vclock::VClock;
    //
    /// let c1 = VClock::new("a");
    /// let c2 = VClock::new("b");
    /// let c3 = c1.merge(&c2);
    /// assert_eq!(1u64, c3.get("a").unwrap());
    /// assert_eq!(1u64, c3.get("b").unwrap());
    /// ```
    pub fn merge(&self, other: &VClock<K>) -> VClock<K> {
        // create a new copy
        let mut nxt = VClock::<K>::default();
        // copy all the existing keys, which are not the key we increment
        for (k, v) in &(self.c) {
            nxt.c.insert(k.clone(), *v);
        }
        // copy all the existing keys for other, which are not the key we increment
        for (k, v) in &(other.c) {
            // insert the key only if it's bigger than what we had
            if match self.c.get(k) {
                Some(v2) => v2 < v,
                None => true,
            } {
                nxt.c.insert(k.clone(), *v);
            }
        }
        // pass the copy
        nxt
    }
}

/// Vector clocks are partially ordered, and this is exactly what they
/// are useful for. If the order is explicitly returned, it means one
/// can fast-forward or fast-rewind from one point to the other in history.
/// If not, that is, if None is returned, it means there is a conflict, and
/// no way to directly go to one point from the other.
impl<K> std::cmp::PartialOrd for VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
{
    /// Compares the vector clock with another one. Note that really,
    /// this is a partial order, if both a<=b and a>=b return false,
    /// it means there is no direct parentship link between clocks.
    ///
    /// ```
    /// use vclock::VClock;
    /// use std::cmp::Ordering;
    ///
    /// // Two vector clocks holding same values are equal.
    /// let mut c1 = VClock::new("a");
    /// let mut c2 = VClock::new("a");
    /// assert_eq!(Some(Ordering::Equal), c1.partial_cmp(&c2));
    /// assert!(c1 <= c2);
    ///
    /// // Two vector clocks with a direct parentship are ordered.
    /// c2.incr("a");
    /// assert_eq!(Some(Ordering::Less), c1.partial_cmp(&c2));
    /// assert_eq!(Some(Ordering::Greater), c2.partial_cmp(&c1));
    /// assert!(c1 < c2);
    /// assert!(c2 > c1);
    ///
    /// // Two vector clocks without a direct parentship are not ordered.
    /// c1.incr("b");
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

impl<K> From<HashMap<K, u64>> for VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
{
    /// Build a vector clock from a hash map containing u64 values.
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
    /// assert_eq!(3, c.get("a").unwrap());
    /// assert_eq!(5, c.get("b").unwrap());
    /// ```
    fn from(src: HashMap<K, u64>) -> VClock<K> {
        VClock { c: src }
    }
}

impl<K> std::fmt::Display for VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::fmt::Display,
{
    /// Pretty print the vector clock, it does not dump all the data,
    /// only a few key values.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut total: u64 = 0;
        let mut max_value: u64 = 0;
        let mut max_key: Option<&K> = None;
        for (k, v) in &(self.c) {
            total += *v;
            if max_value < *v {
                max_key = Some(&k);
                max_value = *v;
            }
        }
        match max_key {
            Some(v) => write!(
                f,
                "{{len:{},total:{},max:{{\"{}\":{}}}}}",
                self.c.len(),
                total,
                v,
                max_value
            ),
            None => write!(f, "{{len:{},total:{}}}", self.c.len(), total),
        }
    }
}

impl<K> std::default::Default for VClock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
{
    /// Return a VClock with no history at all.
    fn default() -> VClock<K> {
        VClock {
            c: HashMap::<K, u64>::new(),
        }
    }
}

#[cfg(test)]
#[test]
fn test_vclock_default() {
    let _ = VClock::<i16>::default();
}

#[test]
fn test_vclock_new() {
    let vc = VClock::<i16>::new(17);
    assert_eq!(None, vc.get(0));
    assert_eq!(Some(1), vc.get(17));
}

#[test]
fn test_vclock_incr() {
    let mut vc = VClock::<i16>::default();
    assert_eq!(None, vc.get(0));

    vc.incr(2);
    assert_eq!(None, vc.get(0));
    assert_eq!(Some(1), vc.get(2));

    vc.incr(2);
    assert_eq!(None, vc.get(0));
    assert_eq!(Some(2), vc.get(2));

    vc.incr(3);
    assert_eq!(None, vc.get(0));
    assert_eq!(Some(2), vc.get(2));
    assert_eq!(Some(1), vc.get(3));
}

#[test]
fn test_vclock_next() {
    let vc = VClock::<i16>::default();
    assert_eq!(None, vc.get(0));

    let vc2 = vc.next(2);
    assert_eq!(None, vc.get(0));
    assert_eq!(None, vc.get(2));
    assert_eq!(Some(1), vc2.get(2));

    let vc3 = vc.next(3);
    assert_eq!(None, vc.get(0));
    assert_eq!(None, vc.get(2));
    assert_eq!(None, vc.get(3));
    assert_eq!(Some(1), vc2.get(2));
    assert_eq!(Some(1), vc3.get(3));

    let vc3i = vc3.next(3);
    assert_eq!(None, vc.get(0));
    assert_eq!(None, vc.get(2));
    assert_eq!(None, vc.get(3));
    assert_eq!(Some(1), vc2.get(2));
    assert_eq!(Some(1), vc3.get(3));
    assert_eq!(Some(2), vc3i.get(3));
}

#[test]
fn test_vclock_debug() {
    let vc = VClock::<i16>::default();
    let vca = vc.next(42);
    let vcb = vca.next(42);
    let vcc = vcb.next(42);
    let repr = format!("{:?}", vcc);
    assert_eq!("VClock { c: {42: 3} }", repr);
}

#[test]
fn test_vclock_compare() {
    let mut vca = VClock::<u32>::default();
    let mut vcb = VClock::<u32>::default();
    assert_eq!(vca, vcb);
    assert_eq!(Some(Ordering::Equal), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Equal), vcb.partial_cmp(&vca));
    vcb.incr(2);
    assert_eq!(Some(Ordering::Less), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Greater), vcb.partial_cmp(&vca));
    vca.incr(2);
    assert_eq!(Some(Ordering::Equal), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Equal), vcb.partial_cmp(&vca));
    vca.incr(2);
    assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
    vca.incr(3);
    vca.incr(3);
    vca.incr(3);
    vcb.incr(3);
    vcb.incr(3);
    vcb.incr(3);
    assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
    vca.incr(4);
    assert_eq!(Some(Ordering::Greater), vca.partial_cmp(&vcb));
    assert_eq!(Some(Ordering::Less), vcb.partial_cmp(&vca));
    vcb.incr(4);
    vcb.incr(4);
    assert_eq!(None, vca.partial_cmp(&vcb));
    assert_eq!(None, vcb.partial_cmp(&vca));
}

#[test]
fn test_vclock_fmt() {
    let mut k = VClock::<i32>::default();
    assert_eq!(String::from("{len:0,total:0}"), format!("{}", k));
    k.incr(42);
    assert_eq!(
        String::from("{len:1,total:1,max:{\"42\":1}}"),
        format!("{}", k)
    );
    k.incr(421);
    k.incr(421);
    k.incr(421);
    assert_eq!(
        String::from("{len:2,total:4,max:{\"421\":3}}"),
        format!("{}", k)
    );
}

#[test]
fn test_vclock_serde_json() {
    let vc = VClock::<i32>::new(42);
    let js = serde_json::json!(&vc).to_string();
    assert_eq!("{\"c\":{\"42\":1}}", js);
    let obj: Result<VClock<i32>, serde_json::Error> = serde_json::from_str(&js);
    match obj {
        Ok(v) => {
            assert_eq!(vc, v);
        }
        Err(e) => panic!(e),
    }
}

#[test]
fn test_vclock_serde_cbor() {
    let vc = VClock::<i32>::new(42);
    let buf: Vec<u8> = serde_cbor::to_vec(&vc).unwrap();
    let obj: VClock<i32> = serde_cbor::from_slice(&buf).unwrap();
    assert_eq!(vc, obj);
}
