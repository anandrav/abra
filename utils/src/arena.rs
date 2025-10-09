/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// this is experimental

use crate::id_set::IdSet;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

pub struct Arena<T> {
    data: Vec<T>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn add(&mut self, value: T) -> Ar<'_, T> {
        self.data.push(value);
        let ptr = self.data.last_mut().unwrap() as *mut T;
        Ar {
            ptr,
            _marker: PhantomData,
        }
    }

    pub fn get(&self, index: usize) -> &T {
        &self.data[index]
    }

    pub fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self.data[index]
    }
}

impl<T: Hash + Eq> std::ops::Index<usize> for Arena<T> {
    type Output = T;

    #[inline]
    fn index(&self, id: usize) -> &Self::Output {
        self.get(id)
    }
}

pub struct Ar<'a, T> {
    ptr: *mut T,
    _marker: PhantomData<&'a mut T>,
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
