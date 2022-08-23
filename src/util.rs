macro_rules! vecdeque {
    () => (
        VecDeque::new()
    );
    ($elem:expr; $n:expr) => (
        $crate::vec::from_elem($elem, $n).to_iter().collect()
    );
    ($($x:expr),*) => (
        $crate::slice::into_vec(box [$($x),*]).to_iter().collect()
    );
    ($($x:expr,)*) => (vec![$($x),*].to_iter().collect())
}
