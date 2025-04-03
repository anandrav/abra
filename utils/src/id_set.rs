use crate::hash::HashMap;
use std::{fmt, hash::Hash};

// elements are unique
// elements have unique IDs
// elements can be retrieved by their ID
// IDs are stable
// iteration is in order of insertion (and therefore stable)
//
// use cases:
// - assign unique integer IDs to values: T
// - intern data to save memory and avoid cloning
// - store values compactly
// - stable order of iteration without performance overhead of sorting
//
// requirements:
// - values must be immutable
#[derive(Default, Clone)]
pub struct IdSet<T: Hash + Eq> {
    map: HashMap<Ptr<T>, u32>,
    current_buf: Vec<T>,
    old_bufs: Vec<Vec<T>>,
    id_to_ptr: Vec<*const T>,
}

// TODO: allow more than just u32 for ID. Maybe u64, usize, and perhaps u16 or u8

/// wrapper around *const T w
#[derive(Copy, Clone)]
struct Ptr<T: Hash + Eq>(*const T);

impl<T: Hash + Eq> Hash for Ptr<T> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // SAFETY: self.0 must point to a valid T
        let t = unsafe { &*self.0 };
        t.hash(state);
    }
}

impl<T: Hash + Eq> PartialEq for Ptr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: self.0 and other.0 must point to a valid T
        let lhs = unsafe { &*self.0 };
        let rhs = unsafe { &*other.0 };
        lhs == rhs
    }
}

impl<T: Hash + Eq> Eq for Ptr<T> {}

impl<T: Hash + Eq> IdSet<T> {
    #[inline]
    pub fn new() -> Self {
        Self {
            map: HashMap::default(),
            current_buf: Vec::with_capacity(0),
            old_bufs: Vec::new(),
            id_to_ptr: Vec::new(),
        }
    }

    #[inline]
    pub fn insert(&mut self, value: T) -> u32 {
        let new_id: u32 = self.map.len() as u32;

        // alloc if necessary
        let capacity = self.current_buf.capacity();
        if self.current_buf.len() + 1 > capacity {
            let new_capacity = capacity.max(1) * 2;
            let new_buf = Vec::with_capacity(new_capacity);

            let old_buf = std::mem::replace(&mut self.current_buf, new_buf);
            self.old_bufs.push(old_buf);
        }

        // SAFETY: Since value_ref points to a T in current_buf, and current_buf is never re-allocated,
        // only moved, value_ref will always be valid as long as current_buf is not de-allocated.
        // Therefore, value_ref is always valid if it has the same lifetime as current_buf, which it does.
        self.current_buf.push(value);
        let value_ref: *const T = &self.current_buf[self.current_buf.len() - 1];
        let ptr = Ptr(value_ref);

        use std::collections::hash_map::Entry;
        match self.map.entry(ptr) {
            Entry::Occupied(entry) => {
                if value_ref == entry.key().0 {
                    *entry.get()
                } else {
                    self.current_buf.pop();
                    *entry.get()
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(new_id);
                self.id_to_ptr.push(value_ref);
                new_id
            }
        }
    }

    #[inline]
    fn try_get_value(&self, id: u32) -> Option<&T> {
        self.id_to_ptr.get(id as usize).map(|&ptr| unsafe { &*ptr })
    }

    #[inline]
    fn get_value(&self, id: u32) -> &T {
        self.try_get_value(id).unwrap()
    }

    #[inline]
    pub fn try_get_id(&self, value: &T) -> Option<u32> {
        // SAFETY: the call to .get() will hash and maybe compare `value`` for equality,
        // but the raw pointer to value is discarded after that
        self.map.get(&Ptr(value as *const T)).cloned()
    }

    // this will panic if value is not found
    #[inline]
    pub fn get_id(&self, value: &T) -> u32 {
        self.try_get_id(value).unwrap()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[inline]
    pub fn contains(&self, value: &T) -> bool {
        self.try_get_id(value).is_some()
    }

    #[inline]
    pub fn clear(&mut self) {
        self.map.clear();
        self.current_buf.clear();
        self.old_bufs.clear();
        self.id_to_ptr.clear();
    }
}

impl<T: Hash + Eq> std::ops::Index<u32> for IdSet<T> {
    type Output = T;

    #[inline]
    fn index(&self, id: u32) -> &Self::Output {
        self.get_value(id)
    }
}

// Iterator

pub struct Iter<'a, T> {
    inner: std::iter::Flatten<std::vec::IntoIter<std::slice::Iter<'a, T>>>,
}

impl<T: Hash + Eq> IdSet<T> {
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        let all_iters: Vec<_> = self
            .old_bufs
            .iter()
            .map(|buf| buf.iter())
            .chain(std::iter::once(self.current_buf.iter()))
            .collect();

        Iter {
            inner: all_iters.into_iter().flatten(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

// IntoIterator for &IdSet<T>

impl<'a, T: Hash + Eq> IntoIterator for &'a IdSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// IntoIterator that steals IdSet

pub struct IntoIter<T> {
    inner: std::iter::Flatten<std::vec::IntoIter<std::vec::IntoIter<T>>>,
}

impl<T: Hash + Eq> IntoIterator for IdSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let all_iters: Vec<_> = self
            .old_bufs
            .into_iter()
            .map(Vec::into_iter)
            .chain(std::iter::once(self.current_buf.into_iter()))
            .collect();

        IntoIter {
            inner: all_iters.into_iter().flatten(),
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

// Debug

impl<T: Hash + Eq> fmt::Debug for IdSet<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_get() {
        let mut set = IdSet::new();
        let a = "apple".to_string();
        let b = "banana".to_string();

        let id_a = set.insert(a.clone());
        let id_b = set.insert(b.clone());

        assert_ne!(id_a, id_b);
        assert_eq!(set.try_get_id(&a), Some(id_a));
        assert_eq!(set.try_get_id(&b), Some(id_b));
        assert!(set.contains(&a));
        assert!(set.contains(&b));
    }

    #[test]
    fn test_no_duplicates() {
        let mut set = IdSet::new();
        let a = "orange".to_string();

        let id1 = set.insert(a.clone());
        let id2 = set.insert(a.clone());

        assert_eq!(id1, id2);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_iteration_order_matches_insertion_order() {
        let mut set = IdSet::new();
        let items = vec!["a", "b", "c", "d", "e"];
        for &item in &items {
            set.insert(item.to_string());
        }

        let iterated: Vec<_> = set.iter().map(|s| s.as_str()).collect();
        assert_eq!(iterated, items);
    }

    #[test]
    fn test_clone_preserves_iteration_order() {
        let mut set = IdSet::new();
        let items = vec!["one", "two", "three"];
        for &item in &items {
            set.insert(item.to_string());
        }

        let clone = set.clone();

        let original: Vec<_> = set.iter().map(|s| s.as_str()).collect();
        let cloned: Vec<_> = clone.iter().map(|s| s.as_str()).collect();

        assert_eq!(original, cloned);
    }

    #[test]
    fn test_clear() {
        let mut set = IdSet::new();
        let id_a = set.insert("a".to_string());
        set.insert("b".to_string());
        set.insert("c".to_string());

        assert_eq!(set.len(), 3);
        set.clear();
        assert_eq!(set.len(), 0);
        assert!(set.iter().next().is_none());
        assert!(set.try_get_value(id_a).is_none());
    }

    #[test]
    fn test_empty() {
        let set: IdSet<String> = IdSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_large_number_of_inserts() {
        let mut set = IdSet::new();
        let count = 1000;
        for i in 0..count {
            let val = format!("item{}", i);
            let id = set.insert(val.clone());
            assert_eq!(set.try_get_id(&val), Some(id));
            assert_eq!(set[id], val);
        }
        assert_eq!(set.len(), count);
    }
}
