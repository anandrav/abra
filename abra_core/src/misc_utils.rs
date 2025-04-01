use std::{collections::HashMap, hash::Hash};

// TODO: If this data structure is useful and convenient, optimize the representation.
// Currently it's storing TWO copies of T and requires T to implement Clone
#[derive(Default)]
pub struct IdSet<T: Hash + Eq + Clone> {
    map: HashMap<T, u32>,
    buf: Vec<T>,
}

impl<T: Hash + Eq + Clone> IdSet<T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            buf: Vec::new(),
        }
    }

    pub fn insert(&mut self, value: T) -> u32 {
        use std::collections::hash_map::*;
        let new_id: u32 = self.map.len() as u32;
        match self.map.entry(value.clone()) {
            Entry::Occupied(occupied_entry) => *occupied_entry.get(),
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(new_id);
                self.buf.push(value);
                new_id
            }
        }
    }

    pub fn get(&self, value: &T) -> Option<&u32> {
        self.map.get(value)
    }
}

impl<T: Hash + Eq + Clone> std::ops::Index<&T> for IdSet<T> {
    type Output = u32;

    fn index(&self, index: &T) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T: Hash + Eq + Clone> IdSet<T> {
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.buf.iter()
    }
}

impl<T: Hash + Eq + Clone> IntoIterator for IdSet<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.buf.into_iter()
    }
}

impl<'a, T: Hash + Eq + Clone> IntoIterator for &'a IdSet<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.buf.iter()
    }
}
