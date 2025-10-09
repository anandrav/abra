/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// this is experimental

use std::cell::UnsafeCell;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::mem::{align_of, size_of};
use std::ptr::{self};

pub struct Arena {
    inner: UnsafeCell<ArenaInner>,
}

struct ArenaInner {
    current_buf: Vec<u8>,
    old_bufs: Vec<Vec<u8>>,
    offset: usize,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            inner: UnsafeCell::new(ArenaInner {
                current_buf: Vec::with_capacity(0),
                old_bufs: Vec::new(),
                offset: 0,
            }),
        }
    }

    pub fn add<T>(&self, value: T) -> Ar<'_, T> {
        let inner = unsafe { &mut *self.inner.get() };
        let align = align_of::<T>();
        let size = size_of::<T>();

        // Align the current offset
        let padding = (align - inner.offset % align) % align;
        let total_size = padding + size;

        // If buffer is too small, allocate a new one
        if inner.offset + total_size > inner.current_buf.capacity() {
            let new_capacity = inner.current_buf.capacity().max(1) * 2;
            let new_buf = Vec::with_capacity(new_capacity);
            let old_buf = std::mem::replace(&mut inner.current_buf, new_buf);
            inner.old_bufs.push(old_buf);
            inner.offset = 0;
        }

        // Ensure the buffer has enough len to hold the new data
        let start = inner.offset + padding;
        if inner.current_buf.len() < start + size {
            inner.current_buf.resize(start + size, 0);
        }

        let ptr = inner.current_buf[start..].as_mut_ptr() as *mut T;
        unsafe {
            ptr::write(ptr, value);
        }

        inner.offset = start + size;

        Ar::new(ptr)
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}


pub struct Ar<'a, T> {
    ptr: *mut T,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> Ar<'a, T> {
    fn new(ptr: *mut T) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }
}

impl<'a, T> Deref for Ar<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<'a, T> DerefMut for Ar<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

impl<'a, T> PartialEq for Ar<'a, T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<'a, T> PartialOrd for Ar<'a, T>
where
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
}

impl<'a, T> Ord for Ar<'a, T>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<'a, T> Eq for Ar<'a, T> where T: Eq {}

impl<'a, T> Hash for Ar<'a, T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<'a, T> Display for Ar<'a, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&**self, f)
    }
}

impl<'a, T> Debug for Ar<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_multiple_inserts() {
        let arena = Arena::new();
        let a = arena.add("apple".to_string());
        let b = arena.add("banana".to_string());
        let c = arena.add(123);

        assert_eq!(*a, "apple");
        assert_eq!(*b, "banana");
        assert_eq!(*c, 123);
    }

    #[test]
    fn test_ref_eq() {
        let arena = Arena::new();
        let a = arena.add("apple".to_string());
        let b = arena.add("apple".to_string());

        assert_eq!(a, b);
    }

    #[test]
    fn test_ref_mutation() {
        let arena = Arena::new();
        let mut a = arena.add("apple".to_string());
        *a = "hello".to_string();

        assert_eq!(*a, "hello");
    }
}
