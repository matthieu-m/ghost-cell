use core::{
    mem,
    ops::Range,
};

use ghost_cell::GhostToken;

use super::{Cursor, TripodTree};

/// An iterator over a TripodList, self-sufficient once created as it carries its own token.
pub struct Iter<'a, 'brand, T> {
    range: Range<usize>,
    cursor: Cursor<'a, 'brand, T>,
}

impl<'a, 'brand, T> Iter<'a, 'brand, T> {
    /// Creates a new instance of the Iter.
    pub fn new(token: &'a GhostToken<'brand>, tree: &'a TripodTree<'brand, T>) -> Self {
        let range = 0..tree.len(token);
        let cursor = tree.cursor(token);

        Self { range, cursor, }
    }

    //  Internal; converts position to element.
    fn at(&self, index: usize) -> Option<&'a T> {
        let mut cursor = self.cursor;
        cursor.move_to(index);
        cursor.current()
    }
}

impl<'a, 'brand, T> Iterator for Iter<'a, 'brand, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.range.next();
        next.and_then(|index| self.at(index))
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.range.size_hint() }

    fn count(self) -> usize { self.range.count() }

    fn last(mut self) -> Option<Self::Item> {
        let range = mem::replace(&mut self.range, 0..0);
        let next = range.last();
        next.and_then(|index| self.at(index))
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let next = self.range.nth(n);
        next.and_then(|index| self.at(index))
    }
}

impl<'a, 'brand, T> DoubleEndedIterator for Iter<'a, 'brand, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let next = self.range.next_back();
        next.and_then(|index| self.at(index))
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let next = self.range.nth_back(n);
        next.and_then(|index| self.at(index))
    }
}

impl<'a, 'brand, T> Clone for Iter<'a, 'brand, T> {
    fn clone(&self) -> Self { Self { range: self.range.clone(), cursor: self.cursor, } }
}

#[cfg(test)]
mod tests {

use super::super::tests::*;

const TREE: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];

#[test]
fn iter_next() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        let collected: Vec<&str> = iter.map(String::as_str).collect();

        assert_eq!(&["1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"][..], collected);
    });
}

#[test]
fn iter_size_hint() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        assert_eq!((15, Some(15)), iter.size_hint());
    });
}

#[test]
fn iter_count() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        assert_eq!(15, iter.count());
    });
}

#[test]
fn iter_last() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        assert_eq!(Some("F"), iter.last().map(String::as_str));
    });
}

#[test]
fn iter_nth() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        let collected: Vec<&str> = iter.step_by(3).map(String::as_str).collect();

        assert_eq!(&["1", "4", "7", "A", "D"][..], collected);
    });
}

#[test]
fn iter_next_back() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        let collected: Vec<&str> = iter.rev().map(String::as_str).collect();

        assert_eq!(&["F", "E", "D", "C", "B", "A", "9", "8", "7", "6", "5", "4", "3", "2", "1"][..], collected);
    });
}

#[test]
fn iter_nth_back() {
    with_tree(TREE, |token, tree| {
        let iter = tree.iter(token);

        let collected: Vec<&str> = iter.rev().step_by(3).map(String::as_str).collect();

        assert_eq!(&["F", "C", "9", "6", "3"][..], collected);
    });
}

} // mod tests
