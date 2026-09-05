use std::marker::PhantomData;

// This is a simple arena
// - backed by a Vec
// - typed indices
// Useful for when
// - you are making a graph of nodes with cycles
// Note
// - You cannot remove individual items after they have been added
struct Arena<T> {
    inner: Vec<T>,
}

// The typed index
struct Index<T> {
    index: usize,
    _tag: PhantomData<T>,
}

impl<T> Index<T> {
    fn new(index: usize) -> Self {
        Index {
            index,
            _tag: PhantomData,
        }
    }
}

impl<T> Arena<T> {
    fn new() -> Arena<T> {
        Arena { inner: Vec::new() }
    }

    fn add(&mut self, value: T) -> Index<T> {
        let index = self.inner.len();
        self.inner.push(value);
        Index::new(index)
    }
}

impl<T> std::ops::Index<Index<T>> for Arena<T> {
    type Output = T;

    fn index(&self, index: Index<T>) -> &Self::Output {
        &self.inner[index.index]
    }
}
