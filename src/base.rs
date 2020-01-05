extern crate serde;

use std::cmp::Ordering;
use std::collections::HashMap;

use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Vclock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::marker::Copy,
    K: std::fmt::Display,
    K: std::fmt::Debug,
    K: std::default::Default,
{
    c: HashMap<K, i64>,
}

/// Vector clock useful to track what is the most up-to-date version of something,
/// knowing that several actors are contributing. The idea is that for each key
/// the number of updates is kept.
impl<K> Vclock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::marker::Copy,
    K: std::fmt::Display,
    K: std::fmt::Debug,
    K: std::default::Default,
{
    /// Initialize a new vector clock with only one contributor.
    /// It is useful to avoid the new() then incr() pattern, as it
    /// performs both operations at once, without copying anything.
    pub fn new(key: K) -> Vclock<K> {
        let mut first = Vclock {
            c: HashMap::<K, i64>::default(),
        };
        first.c.insert(key, 1);
        first
    }

    /// Increment a vector clock in-place.
    pub fn incr(&mut self, key: K) {
        self.c.insert(
            key,
            match self.c.get(&key) {
                Some(v) => v + 1,
                None => 1,
            },
        );
    }

    /// Increments a vector clock and does a fresh copy. There's no default
    /// implementation of Copy for the vector clock as, indeed, copying it
    /// can be expensive so it's not a good practice to copy it.
    /// However, when incrementing, we might want to actually get a fresh
    /// copy, as typically this incremented clock might refer to a new object.
    pub fn next(&self, key: K) -> Vclock<K> {
        // create a new copy
        let mut nxt = Vclock::<K>::default();
        // copy all the existing keys, which are not the key we increment
        for (k, v) in &(self.c) {
            if &key != k {
                nxt.c.insert(*k, *v);
            }
        }
        // increment and copy the key we want to increment, specifically
        nxt.c.insert(
            key,
            match self.c.get(&key) {
                Some(v) => v + 1,
                None => 1,
            },
        );
        // pass the copy
        nxt
    }

    /// Returns the counter associated to a given key.
    pub fn get(&self, key: K) -> Option<i64> {
        match self.c.get(&key) {
            Some(v) => Some(*v),
            None => None,
        }
    }
}

/// Vector c are partially ordered, and this is exactly what they
/// are useful for. If the order is explicitly returned, it means one
/// can fast-forward or fast-rewind from one point to the other in history.
/// If not, that is, if None is returned, it means there is a conflict, and
/// no way to directly go to one point from the other.
impl<K> std::cmp::PartialOrd for Vclock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::marker::Copy,
    K: std::fmt::Display,
    K: std::fmt::Debug,
    K: std::default::Default,
{
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

impl<K> std::fmt::Display for Vclock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::marker::Copy,
    K: std::fmt::Display,
    K: std::fmt::Debug,
    K: std::default::Default,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut total: i64 = 0;
        let mut max_value: i64 = 0;
        let mut max_key: K = std::default::Default::default();
        for (k, v) in &(self.c) {
            total += *v;
            if max_value < *v {
                max_key = *k;
                max_value = *v;
            }
        }
        write!(
            f,
            "{{len:{},total:{},max:{{{}:{}}}}}",
            self.c.len(),
            total,
            max_key,
            max_value
        )
    }
}

impl<K> std::default::Default for Vclock<K>
where
    K: std::cmp::Eq,
    K: std::hash::Hash,
    K: std::marker::Copy,
    K: std::fmt::Display,
    K: std::fmt::Debug,
    K: std::default::Default,
{
    fn default() -> Vclock<K> {
        Vclock {
            c: HashMap::<K, i64>::new(),
        }
    }
}

#[cfg(test)]
#[test]
fn test_vclock_default() {
    let _ = Vclock::<i16>::default();
}

#[test]
fn test_vclock_new() {
    let vc = Vclock::<i16>::new(17);
    assert_eq!(None, vc.get(0));
    assert_eq!(Some(1), vc.get(17));
}

#[test]
fn test_vclock_incr() {
    let mut vc = Vclock::<i16>::default();
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
    let vc = Vclock::<i16>::default();
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
    let vc = Vclock::<i16>::default();
    let vca = vc.next(42);
    let vcb = vca.next(42);
    let vcc = vcb.next(42);
    let repr = format!("{:?}", vcc);
    assert_eq!("Vclock { c: {42: 3} }", repr);
}

#[test]
fn test_vclock_compare() {
    let mut vca = Vclock::<u32>::default();
    let mut vcb = Vclock::<u32>::default();
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
    let mut k = Vclock::<i32>::default();
    assert_eq!(String::from("{len:0,total:0,max:{0:0}}"), format!("{}", k));
    k.incr(42);
    assert_eq!(String::from("{len:1,total:1,max:{42:1}}"), format!("{}", k));
    k.incr(421);
    k.incr(421);
    k.incr(421);
    assert_eq!(
        String::from("{len:2,total:4,max:{421:3}}"),
        format!("{}", k)
    );
}

#[test]
fn test_vclock_serde_json() {
    let vc = Vclock::<i32>::new(42);
    let js = serde_json::json!(&vc).to_string();
    assert_eq!("{\"c\":{\"42\":1}}", js);
    let obj: Result<Vclock<i32>, serde_json::Error> = serde_json::from_str(&js);
    match obj {
        Ok(v) => {
            assert_eq!(vc, v);
        }
        Err(e) => panic!(e),
    }
}

#[test]
fn test_vclock_serde_cbor() {
    let vc = Vclock::<i32>::new(42);
    let buf: Vec<u8> = serde_cbor::to_vec(&vc).unwrap();
    let obj: Vclock<i32> = serde_cbor::from_slice(&buf).unwrap();
    assert_eq!(vc, obj);
}
