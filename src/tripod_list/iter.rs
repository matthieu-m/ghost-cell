use ghost_cell::GhostToken;

use super::{GhostNode, TripodList};

/// An iterator over a TripodList, self-sufficient once created as it carries its own token.
pub struct Iter<'a, 'brand, T> {
    token: &'a GhostToken<'brand>,
    head_tail: Option<(&'a GhostNode<'brand, T>, &'a GhostNode<'brand, T>)>,
}

impl<'a, 'brand, T> Iter<'a, 'brand, T> {
    /// Creates a new instance of the Iter.
    pub fn new(token: &'a GhostToken<'brand>, list: &'a TripodList<'brand, T>) -> Self {
        let head_tail = list.head_tail.as_ref().map(|head_tail| {
            (&*head_tail.0, &*head_tail.1)
        });

        Self { token, head_tail, }
    }

    //  Internal: creates an empty instance.
    pub(super) fn empty(token: &'a GhostToken<'brand>) -> Self {
        Self { token, head_tail: None, }
    }

    //  Internal: creates an instance over a slice of items.
    pub(super) fn slice(
        token: &'a GhostToken<'brand>,
        head_tail: Option<(&'a GhostNode<'brand, T>, &'a GhostNode<'brand, T>)>,
    )
        -> Self
    {
        Self { token, head_tail, }
    }
}

impl<'a, 'brand, T> Iterator for Iter<'a, 'brand, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.head_tail.take()?;

        let node = head.borrow(self.token);

        if head as *const _ != tail as *const _ {
            self.head_tail = node.next.as_ref().map(|n| {
                let n: &'a GhostNode<'_, _> = &*n;
                (n, tail)
            });
        } else {
            self.head_tail = None;
        }

        Some(&node.value)
    }
}

impl<'a, 'brand, T> DoubleEndedIterator for Iter<'a, 'brand, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.head_tail.take()?;

        let node = tail.borrow(self.token);

        if head as *const _ != tail as *const _ {
            self.head_tail = node.prev.as_ref().map(|n| {
                let n: &'a GhostNode<'_, _> = &*n;
                (head, n)
            });
        } else {
            self.head_tail = None;
        }

        Some(&node.value)
    }
}

#[cfg(test)]
mod tests {

use super::super::tests::with_list;
use super::*;

#[test]
fn empty() {
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut iterator = Iter::new(token, list);

        assert_eq!(None, iterator.next());
        assert_eq!(None, iterator.next_back());
    });
}

#[test]
fn forward() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut iterator = Iter::new(token, list);

        assert_eq!(Some("0"), iterator.next().map(String::as_str));
        assert_eq!(Some("1"), iterator.next().map(String::as_str));
        assert_eq!(Some("2"), iterator.next().map(String::as_str));
        assert_eq!(Some("3"), iterator.next().map(String::as_str));
        assert_eq!(None, iterator.next());
    });
}

#[test]
fn backward() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut iterator = Iter::new(token, list);

        assert_eq!(Some("3"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("2"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("1"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("0"), iterator.next_back().map(String::as_str));
        assert_eq!(None, iterator.next_back());
    });
}

#[test]
fn alternate() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut iterator = Iter::new(token, list);

        assert_eq!(Some("0"), iterator.next().map(String::as_str));
        assert_eq!(Some("3"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("1"), iterator.next().map(String::as_str));
        assert_eq!(Some("2"), iterator.next_back().map(String::as_str));
        assert_eq!(None, iterator.next());
        assert_eq!(None, iterator.next_back());
    });
}

#[test]
fn alternate_other() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut iterator = Iter::new(token, list);

        assert_eq!(Some("3"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("0"), iterator.next().map(String::as_str));
        assert_eq!(Some("2"), iterator.next_back().map(String::as_str));
        assert_eq!(Some("1"), iterator.next().map(String::as_str));
        assert_eq!(None, iterator.next_back());
        assert_eq!(None, iterator.next());
    });
}

} // mod tests
