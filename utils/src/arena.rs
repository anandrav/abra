/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// this is experimental

use std::borrow::{Borrow, BorrowMut};
use std::cell::UnsafeCell;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

pub struct Arena<T> {
    inner: UnsafeCell<ArenaInner<T>>,
}

struct ArenaInner<T> {
    current_buf: Vec<T>,
    old_bufs: Vec<Vec<T>>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            inner: ArenaInner {
                current_buf: Vec::new(),
                old_bufs: Vec::new(),
            }
                .into(),
        }
    }

    pub fn add(&self, value: T) -> Ar<'_, T> {
        let inner = unsafe { &mut *self.inner.get() };

        let capacity = inner.current_buf.capacity();
        if inner.current_buf.len() + 1 > capacity {
            let new_capacity = capacity.max(1) * 2;
            let new_buf = Vec::with_capacity(new_capacity);

            let old_buf = std::mem::replace(&mut inner.current_buf, new_buf);
            inner.old_bufs.push(old_buf);
        }

        // SAFETY: Since value_ref points to a T in current_buf, and current_buf is never re-allocated,
        // only moved, value_ref will always be valid as long as current_buf is not de-allocated.
        // Therefore, value_ref is always valid if it has the same lifetime as current_buf, which it does.
        inner.current_buf.push(value);
        let index = inner.current_buf.len() - 1;
        let value_ref: *mut T = &mut inner.current_buf[index];
        Ar::new(value_ref)
    }
}

impl<T> Default for Arena<T> {
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

impl<'a, T> Borrow<T> for Ar<'a, T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<'a, T> BorrowMut<T> for Ar<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T> AsRef<T> for Ar<'a, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<'a, T> AsMut<T> for Ar<'a, T> {
    fn as_mut(&mut self) -> &mut T {
        self
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

        assert_eq!(*a, "apple");
        assert_eq!(*b, "banana");
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
