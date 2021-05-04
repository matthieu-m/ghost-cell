//! A LinkedList, with externally supplied token.
//!
//! Unlike LinkedList, a TripodList has one additional pointer per node. In exchange, extra capabilities are unlocked.
//!
//! A number of operations normally implemented by traits cannot be successfully implemented on this collection due to
//! the requirement of supplying the GhostToken externally.

mod cursor;
mod iter;

pub use cursor::{Cursor, CursorMut};
pub use iter::Iter;

use core::{
    cell::Cell,
    mem,
};

use ghost_cell::{GhostCell, GhostToken};
use static_rc::StaticRc;

/// A safe implementation of a linked-list build upon `GhostCell` and `StaticRc`.
///
/// The `TripodList` contains 3 pointers per node, rather than 2 for a standard doubly linked list, the extra pointer
/// is used to temporarily anchor a node to the stack, guaranteeing its lifetime.
pub struct TripodList<'brand, T> {
    length: usize,
    head_tail: Option<(ThirdNodePtr<'brand, T>, ThirdNodePtr<'brand, T>)>,
}

impl<'brand, T> TripodList<'brand, T> {
    /// Creates a fresh instance.
    pub fn new() -> Self { Self::default() }

    /// Appends all elements of `other`, in order, to the back of this list.
    ///
    /// After this call, `other` is empty
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn append(&mut self, other: &mut Self, token: &mut GhostToken<'brand>) {
        let other_ht = if let Some(other_ht) = other.head_tail.take() {
            other_ht
        } else {
            return;
        };

        self.head_tail = if let Some(self_ht) = self.head_tail.take() {
            let (new_head, mid_tail) = self_ht;
            let (mid_head, new_tail) = other_ht;

            let tripod = mid_head.borrow(token).deploy();

            mid_tail.borrow_mut(token).next = Some(mid_head);
            tripod.borrow_mut(token).prev = Some(mid_tail);

            retract(tripod, token);

            Some((new_head, new_tail))
        } else {
            Some(other_ht)
        };

        self.length += other.length;
        other.length = 0;
    }

    /// Prepends all elements of `other`, in order, to the front of this list.
    ///
    /// After this call, `other` is empty
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn prepend(&mut self, other: &mut Self, token: &mut GhostToken<'brand>) {
        other.append(self, token);
        mem::swap(self, other);
    }

    /// Creates an iterator over self.
    pub fn iter<'a>(&'a self, token: &'a GhostToken<'brand>) -> Iter<'a, 'brand, T> {
        Iter::new(token, self)
    }

    /// Creates a cursor pointing to the front element.
    pub fn cursor_front<'a>(&'a self, token: &'a GhostToken<'brand>) -> Cursor<'a, 'brand, T> {
        Cursor::new_front(token, self)
    }

    /// Creates a mutable cursor pointing to the front element.
    pub fn cursor_front_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> CursorMut<'a, 'brand, T> {
        CursorMut::new_front(token, self)
    }

    /// Creates a cursor pointing to the back element.
    pub fn cursor_back<'a>(&'a self, token: &'a GhostToken<'brand>) -> Cursor<'a, 'brand, T> {
        Cursor::new_back(token, self)
    }

    /// Creates a mutable cursor pointing to the back element.
    pub fn cursor_back_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> CursorMut<'a, 'brand, T> {
        CursorMut::new_back(token, self)
    }

    /// Returns whether the list is empty, or not.
    pub fn is_empty(&self) -> bool { self.length == 0 }

    /// Returns the number of elements in the list.
    pub fn len(&self) -> usize { self.length }

    /// Clears the list, destroying all elements.
    ///
    /// #   Complexity
    ///
    /// This operation is O(N) in the number of elements.
    pub fn clear(&mut self, token: &mut GhostToken<'brand>) {
        while let Some(_) = self.pop_back(token) {}
    }

    /// Returns a reference to the front element of the list, if any.
    pub fn front<'a>(&'a self, token: &'a GhostToken<'brand>) -> Option<&'a T> {
        self.front_node().map(|node| &node.borrow(token).value)
    }

    /// Returns a mutable reference to the front element of the list, if any.
    pub fn front_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> Option<&'a mut T> {
        self.front_node().map(move |node| &mut node.borrow_mut(token).value)
    }

    /// Returns a reference to the back element of the list, if any.
    pub fn back<'a>(&'a self, token: &'a GhostToken<'brand>) -> Option<&'a T> {
        self.back_node().map(|node| &node.borrow(token).value)
    }

    /// Returns a mutable reference to the back element of the list, if any.
    pub fn back_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> Option<&'a mut T> {
        self.back_node().map(move |node| &mut node.borrow_mut(token).value)
    }

    /// Pushes an element to the front of the list.
    pub fn push_front(&mut self, value: T, token: &mut GhostToken<'brand>) {
        let (one, two) = Self::new_thirds(value, token);

        let head_tail = if let Some((head, tail)) = self.head_tail.take() {
            head.borrow_mut(token).prev = Some(one);
            two.borrow_mut(token).next = Some(head);

            (two, tail)
        } else {
            (one, two)
        };

        self.length += 1;
        self.head_tail = Some(head_tail);
    }

    /// Removes and returns the front element of the list, if any.
    pub fn pop_front(&mut self, token: &mut GhostToken<'brand>) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;
        let tripod = head.borrow(token).deploy();

        let (one, two) = if StaticRc::as_ptr(&head) == StaticRc::as_ptr(&tail) {
            (head, tail)
        } else {
            let next = head.borrow_mut(token).next.take()
                .expect("Non-tail should have a next node");
            let other_head = next.borrow_mut(token).prev.take()
                .expect("Non-head should have a previous node");

            self.head_tail = Some((next, tail));

            (head, other_head)
        };

        self.length -= 1;

        Some(Self::into_inner((one, two, tripod)))
    }

    /// Pushes an element to the back of the list.
    pub fn push_back(&mut self, value: T, token: &mut GhostToken<'brand>) {
        let (one, two) = Self::new_thirds(value, token);

        let head_tail = if let Some((head, tail)) = self.head_tail.take() {
            tail.borrow_mut(token).next = Some(one);
            two.borrow_mut(token).prev = Some(tail);

            (head, two)
        } else {
            (one, two)
        };

        self.length += 1;
        self.head_tail = Some(head_tail);
    }

    /// Removes and returns the back element of the list, if any.
    pub fn pop_back(&mut self, token: &mut GhostToken<'brand>) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;
        let tripod = tail.borrow(token).deploy();

        let (one, two) = if StaticRc::as_ptr(&head) == StaticRc::as_ptr(&tail) {
            (head, tail)
        } else {
            let prev = tail.borrow_mut(token).prev.take()
                .expect("Non-head should have a previous node");
            let other_tail = prev.borrow_mut(token).next.take()
                .expect("Non-tail should have a next node");

            self.head_tail = Some((head, prev));

            (other_tail, tail)
        };

        self.length -= 1;

        Some(Self::into_inner((one, two, tripod)))
    }

    /// Splits the list in two at the given index. Returns a list containing everything after the given index, inclusive.
    ///
    /// Returns None if the given index is out of bounds.
    ///
    /// #   Complexity
    ///
    /// This operations is O(min(`at`, N)), where N is the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn split_off(&mut self, at: usize, token: &mut GhostToken<'brand>) -> Self {
        assert!(at < self.length, "at ({}) >= self.len() ({})", at, self.length);

        //  This is not the most optimal implementation, but it works, and respects the promised algorithmic complexity.
        let mut cursor = self.cursor_front_mut(token);

        if at == 0 {
            cursor.move_prev();
        } else {
            for _ in 0..(at-1) {
                cursor.move_next();
            }
        }

        cursor.split_after()
    }

    /// Removes the element at the given index, and returns it, if the index is within bounds.
    ///
    /// #   Complexity
    ///
    /// This operations is O(min(`at`, N)), where N is the number of elements.
    ///
    /// No memory allocation occurs, and a single memory deallocation occurs.
    pub fn remove(&mut self, at: usize, token: &mut GhostToken<'brand>) -> T {
        assert!(at < self.length, "at ({}) >= self.len() ({})", at, self.length);

        //  This is not the most optimal implementation, but it works, and respects the promised algorithmic complexity.
        let mut cursor = self.cursor_front_mut(token);

        for _ in 0..at {
            cursor.move_next();
        }

        cursor.remove_current().expect("Element, since at < self.length")
    }

    //  Internal: returns a reference to the front node, if any.
    fn front_node(&self) -> Option<&GhostNode<'brand, T>> { self.head_tail.as_ref().map(|ht| &*ht.0) }

    //  Internal: returns a reference to the front node, if any.
    fn back_node(&self) -> Option<&GhostNode<'brand, T>> { self.head_tail.as_ref().map(|ht| &*ht.1) }

    //  Internal: creates a node with the value, and returns 2/3 of its pointers, the remaining tucked into its tripod field.
    fn new_thirds(value: T, token: &GhostToken<'brand>) -> (ThirdNodePtr<'brand, T>, ThirdNodePtr<'brand, T>) {
        let node = Node { value, prev: None, next: None, tripod: Cell::new(None), };
        let full = FullNodePtr::new(GhostNode::new(node));
        let (partial, tripod) = StaticRc::split::<2, 1>(full);

        partial.borrow(token).retract(tripod);

        StaticRc::split::<1, 1>(partial)
    }

    //  Internal: takes 3 1/3 pointers, reassemble them, and return their inner value.
    fn into_inner(thirds: ThirdTuple<'brand, T>) -> T {
        let partial = TwoThirdsNodePtr::join(thirds.0, thirds.1);
        let full = FullNodePtr::join(partial, thirds.2);
        let ghost_cell = FullNodePtr::into_inner(full);
        let node = GhostNode::into_inner(ghost_cell);

        //  If the node still has a prev and next, they are leaked.
        debug_assert!(node.prev.is_none());
        debug_assert!(node.next.is_none());
        debug_assert!(node.tripod.replace(None).is_none());

        node.value
    }
}

impl<'brand, T> Default for TripodList<'brand, T> {
    fn default() -> Self { Self { length: 0, head_tail: None, } }
}

//
//  Implementation
//

struct Node<'brand, T> {
    value: T,
    prev: Option<ThirdNodePtr<'brand, T>>,
    next: Option<ThirdNodePtr<'brand, T>>,
    tripod: Cell<Option<ThirdNodePtr<'brand, T>>>,
}

impl<'brand, T> Node<'brand, T> {
    //  Internal; deploys the tripod.
    fn deploy(&self) -> ThirdNodePtr<'brand, T> { self.tripod.take().expect("Tripod not to be None") }

    //  Internal; retracts the tripod.
    fn retract(&self, tripod: ThirdNodePtr<'brand, T>) {
        let previous = self.tripod.replace(Some(tripod));
        debug_assert!(previous.is_none());
    }
}

fn retract<'brand, T>(tripod: ThirdNodePtr<'brand, T>, token: &mut GhostToken<'brand>) {
    let previous = static_rc::lift_with_mut(Some(tripod), token, |tripod, token| {
        tripod.as_ref().expect("Some").borrow_mut(token).tripod.get_mut()
    });
    debug_assert!(previous.is_none(), "Node should not have any tripod to retract it!");

}

type GhostNode<'brand, T> = GhostCell<'brand, Node<'brand, T>>;
type ThirdNodePtr<'brand, T> = StaticRc<GhostNode<'brand, T>, 1, 3>;
type TwoThirdsNodePtr<'brand, T> = StaticRc<GhostNode<'brand, T>, 2, 3>;
type FullNodePtr<'brand, T> = StaticRc<GhostNode<'brand, T>, 3, 3>;
type ThirdTuple<'brand, T> = (ThirdNodePtr<'brand, T>, ThirdNodePtr<'brand, T>, ThirdNodePtr<'brand, T>);

#[cfg(test)]
mod tests {

use std::{
    panic::{self, AssertUnwindSafe},
    ops::Range,
};

use super::*;

#[track_caller]
fn assert_list_mut<'brand>(expected: &[&str], token: &mut GhostToken<'brand>, list: &mut TripodList<'brand, String>) {
    let actual = collect(list.iter(token));
    assert_eq!(expected, actual);

    assert_eq!(expected.len(), list.len());
    assert_eq!(expected.is_empty(), list.is_empty());

    list.clear(token);
}

#[track_caller]
pub(crate) fn assert_list<'brand>(expected: &[&str], token: &mut GhostToken<'brand>, mut list: TripodList<'brand, String>) {
    assert_list_mut(expected, token, &mut list);
}

#[track_caller]
fn assert_list_append(list: Vec<String>, append: Vec<String>, expected: &[&str]) {
    with_list_duo(list, append, |token, list, other| {
        list.append(other, token);

        assert_list_mut(expected, token, list);
        assert_list_mut(&[], token, other);
    });
}

#[test]
fn list_append() {
    //  Append empty list
    assert_list_append(create(0..0), create(0..0), &[]);
    assert_list_append(create(0..1), create(0..0), &["0"]);
    assert_list_append(create(0..4), create(0..0), &["0", "1", "2", "3"]);

    //  Append single element list
    assert_list_append(create(0..0), create(4..5), &["4"]);
    assert_list_append(create(0..1), create(4..5), &["0", "4"]);
    assert_list_append(create(0..4), create(4..5), &["0", "1", "2", "3", "4"]);

    //  Append multi element list
    assert_list_append(create(0..0), create(4..7), &["4", "5", "6"]);
    assert_list_append(create(0..1), create(4..7), &["0", "4", "5", "6"]);
    assert_list_append(create(0..4), create(4..7), &["0", "1", "2", "3", "4", "5", "6"]);
}

#[track_caller]
fn assert_list_split_off(list: Vec<String>, at: usize, expected_list: &[&str], expected_result: &[&str]) {
    with_list(list, |token, list| {
        let result = list.split_off(at, token);

        assert_list_mut(expected_list, token, list);
        assert_list(expected_result, token, result);
    });
}

#[test]
fn list_split_off() {
    assert_list_split_off(create(0..4), 0, &[], &["0", "1", "2", "3"]);
    assert_list_split_off(create(0..4), 1, &["0"], &["1", "2", "3"]);
    assert_list_split_off(create(0..4), 2, &["0", "1"], &["2", "3"]);
    assert_list_split_off(create(0..4), 3, &["0", "1", "2"], &["3"]);
}

#[test]
#[should_panic]
fn list_split_off_out_of_bounds() {
    with_list(create(0..4), |token, list| {
        list.split_off(4, token);
    });
}

#[track_caller]
fn assert_list_remove(list: Vec<String>, at: usize, expected_list: &[&str], expected_result: &str) {
    with_list(list, |token, list| {
        let result = list.remove(at, token);
        assert_eq!(expected_result, result);

        assert_list_mut(expected_list, token, list);
    });
}

#[test]
fn list_remove() {
    assert_list_remove(create(0..4), 0, &["1", "2", "3"], "0");
    assert_list_remove(create(0..4), 1, &["0", "2", "3"], "1");
    assert_list_remove(create(0..4), 2, &["0", "1", "3"], "2");
    assert_list_remove(create(0..4), 3, &["0", "1", "2"], "3");
}

#[test]
#[should_panic]
fn list_remove_out_of_bounds() {
    with_list(create(0..4), |token, list| {
        list.remove(4, token);
    });
}

pub(crate) fn create(range: Range<i32>) -> Vec<String> {
    range.map(|n| n.to_string()).collect()
}

pub(crate) fn collect<'a>(iter: Iter<'a, '_, String>) -> Vec<&'a str> {
    iter.map(String::as_str).collect()
}

pub(crate) fn with_list<T, R, F>(initial: Vec<T>, fun: F) -> R
where
    F: for<'brand> FnOnce(&mut GhostToken<'brand>, &mut TripodList<'brand, T>) -> R,
{
    GhostToken::new(|mut token| {
        let mut list = TripodList::new();
        
        for value in initial {
            list.push_back(value, &mut token);
        }

        let result = panic::catch_unwind(AssertUnwindSafe(|| fun(&mut token, &mut list)));

        list.clear(&mut token);

        result.expect("No Panic")
    })
}

pub(crate) fn with_list_duo<T, R, F>(first: Vec<T>, second: Vec<T>, fun: F) -> R
where
    F: for<'brand> FnOnce(&mut GhostToken<'brand>, &mut TripodList<'brand, T>, &mut TripodList<'brand, T>) -> R,
{
    GhostToken::new(|mut token| {
        let mut first_list = TripodList::new();
        let mut second_list = TripodList::new();

        for value in first {
            first_list.push_back(value, &mut token);
        }

        for value in second {
            second_list.push_back(value, &mut token);
        }

        let result = panic::catch_unwind(AssertUnwindSafe(|| fun(&mut token, &mut first_list, &mut second_list)));

        first_list.clear(&mut token);
        second_list.clear(&mut token);

        result.expect("No Panic")
    })
}

} // mod tests
