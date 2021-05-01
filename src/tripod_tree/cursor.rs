use core::{
    cmp,
    mem,
    ops::Range,
};

use ghost_cell::GhostToken;

use super::{GhostNode, QuarterNodePtr, Side, TripodTree};

/// A Cursor over the TripodTree.
///
/// The Cursor contains a "twilight" non-element between the leaves and the root, that is:
///
/// -   Going "up" from the root points the cursor to the "twilight" non-element.
/// -   Going "left", respectively "right", from any node without a "left" (resp. "right") sub-tree points the cursor
///     to the "twilight" non-element.
///
/// A cursor pointing to the "twilight" non-element cannot go "up", and going either "left" or "right" points the
/// cursor back to the root.
pub struct Cursor<'a, 'brand, T> {
    token: &'a GhostToken<'brand>,
    tree: &'a TripodTree<'brand, T>,
    node: Option<&'a GhostNode<'brand, T>>,
    index: usize,
}

//  Constant time cursor navigation.
impl<'a, 'brand, T> Cursor<'a, 'brand, T> {
    /// Creates a new cursor pointing at the root of the tree, if any.
    pub fn new(token: &'a GhostToken<'brand>, tree: &'a TripodTree<'brand, T>) -> Self {
        let (node, index) = Self::root_of(token, tree);

        Self { token, index, node, tree, }
    }

    /// Returns the index of the cursor, if any.
    ///
    /// If the cursor points to the "twilight" non-element, None is returned.
    pub fn index(&self) -> Option<usize> { self.node.map(|_| self.index) }

    /// Returns the range of indices covered by the sub-tree rooted at node the cursor is pointing at.
    ///
    /// If the cursor points to the new "twilight" non-element, None is returned.
    pub fn range(&self) -> Range<usize> {
        self.node.map(|node| {
            let left_size = node.borrow(self.token).left_size(self.token);
            let right_size = node.borrow(self.token).right_size(self.token);

            (self.index - left_size)..(self.index + right_size + 1)
        }).unwrap_or(0..0)
    }

    /// Moves the cursor to the root, if any.
    pub fn move_to_root(&mut self) { *self = Self::new(self.token, self.tree) }

    /// Moves the cursor to the parent node, if any.
    ///
    /// If the cursor points to the "twilight" non-element, nothing happens.
    pub fn move_up(&mut self) {
        let (node, index) = self.peek_up_node();

        self.index = index;
        self.node = node;
    }

    /// Moves the cursor to the left child.
    ///
    /// If the element the cursor points to has no left child, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_left(&mut self) {
        let (node, index) = self.peek_left_node();

        self.index = index;
        self.node = node;
    }

    /// Moves the cursor to the right child.
    ///
    /// If the element the cursor points to has no right child, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_right(&mut self) {
        let (node, index) = self.peek_right_node();

        self.index = index;
        self.node = node;
    }

    /// Moves the cursor to the child element on the design side.
    ///
    /// If the element the cursor points to has no such element, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_down(&mut self, side: Side) {
        let (node, index) = self.peek_down_node(side);

        self.index = index;
        self.node = node;
    }

    /// Attempts to move the cursor to the parent node, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no parent node, or is the "twilight" element, does not move.
    pub fn try_move_up(&mut self) -> Option<&'a T> {
        let (node, index) = self.peek_up_node();

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the left child, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no left child, or is the "twilight" element, does not move.
    pub fn try_move_left(&mut self) -> Option<&'a T> {
        let (node, index) = self.peek_left_node();

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the right child, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no right child, or is the "twilight" element, does not move.
    pub fn try_move_right(&mut self) -> Option<&'a T> {
        let (node, index) = self.peek_right_node();

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor down to the designed side, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor is pointing to has no child on that side, or is the "twilight" non-element, nothing
    /// happens and None is returned.
    pub fn try_move_down(&mut self, side: Side) -> Option<&'a T> {
        let (node, index) = self.peek_down_node(side);

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Returns a reference to the current element, if any.
    pub fn current(&self) -> Option<&'a T> { self.node.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the up element, if any.
    pub fn peek_up(&self) -> Option<&'a T> { self.peek_up_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the left child, if any.
    pub fn peek_left(&self) -> Option<&'a T> { self.peek_left_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the right child, if any.
    pub fn peek_right(&self) -> Option<&'a T> { self.peek_right_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the child element on the designed side, if any.
    pub fn peek_down(&self, side: Side) -> Option<&'a T> { self.peek_down_node(side).0.map(|node| &node.borrow(self.token).value) }

    //  Internal; extract the root and its index from the tree.
    fn root_of(token: &'a GhostToken<'brand>, tree: &'a TripodTree<'brand, T>) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        let root = tree.root.as_ref().map(|node| &**node);
        let index = root.map(|node| node.borrow(token).index(token)).unwrap_or(0);

        (root, index)
    }

    //  Internal; returns a reference to the up GhostNode, and the matching index.
    fn peek_up_node(&self) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        if let Some(node) = self.node {
            let node = node.borrow(self.token);
            let parent = node.up();

            let index = if let Some(parent) = parent {
                let parent = parent.borrow(self.token);

                if node.is_aliased(parent.left()) {
                    self.index + 1 + node.right_size(self.token)
                } else {
                    debug_assert!(node.is_aliased(parent.right()));
                    self.index - 1 - node.left_size(self.token)
                }
            } else {
                self.len()
            };

            (parent, index)
        } else {
            (self.node, self.len())
        }
    }

    //  Internal; returns a reference to the left GhostNode, and the matching index.
    fn peek_left_node(&self) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        if let Some(node) = self.node {
            let node = node.borrow(self.token);
            let dest = node.left();

            let index = if let Some(left) = dest {
                self.index - 1 - left.borrow(self.token).right_size(self.token)
            } else {
                self.len()
            };

            (dest, index)
        } else {
            Self::root_of(self.token, self.tree)
        }
    }

    //  Internal; returns a reference to the right GhostNode, and the matching index.
    fn peek_right_node(&self) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        if let Some(node) = self.node {
            let node = node.borrow(self.token);
            let dest = node.right();

            let index = if let Some(right) = dest {
                self.index + 1 + right.borrow(self.token).left_size(self.token)
            } else {
                self.len()
            };

            (dest, index)
        } else {
            Self::root_of(self.token, self.tree)
        }
    }

    //  Internal; returns a reference to the child GhostNode on the designed side, and the matching index.
    fn peek_down_node(&self, side: Side) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        if let Some(node) = self.node {
            let node = node.borrow(self.token);
            let dest = node.child(side);

            let index = if let Some(dest) = dest {
                let opposite_size = dest.borrow(self.token).child_size(side.opposite(), self.token);

                match side {
                    Side::Left => self.index - 1 - opposite_size,
                    Side::Right => self.index + 1 + opposite_size,
                }
            } else {
                self.len()
            };

            (dest, index)
        } else {
            Self::root_of(self.token, self.tree)
        }
    }
}

//  Logarithmic cursor navigation.
impl<'a, 'brand, T> Cursor<'a, 'brand, T> {
    /// Creates a new cursor pointing at the front element of the tree, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn new_front(token: &'a GhostToken<'brand>, tree: &'a TripodTree<'brand, T>) -> Self {
        let mut cursor = Self::new(token, tree);

        while let Some(_) = cursor.try_move_left() {}

        debug_assert_eq!(0, cursor.index);

        cursor
    }

    /// Creates a new cursor pointing at the back element of the tree, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn new_back(token: &'a GhostToken<'brand>, tree: &'a TripodTree<'brand, T>) -> Self {
        let mut cursor = Self::new(token, tree);

        while let Some(_) = cursor.try_move_right() {}

        debug_assert_eq!(cursor.len() - 1, cursor.index);

        cursor
    }

    /// Moves the cursor to the front element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_to_front(&mut self) { *self = Self::new_front(self.token, self.tree); }

    /// Moves the cursor to the back element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_to_back(&mut self) { *self = Self::new_back(self.token, self.tree); }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, then the cursor moves to the "twilight" non-element, which exists between the root
    /// and the leaves.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_next(&mut self) {
        let (node, index) = self.peek_next_node();

        self.index = index;
        self.node = node;
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, then the cursor moves to the "twilight" non-element, which exists between the root
    /// and the leaves.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_prev(&mut self) {
        let (node, index) = self.peek_prev_node();

        self.index = index;
        self.node = node;
    }

    /// Moves the cursor to the element at the given index.
    ///
    /// If there is no such element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    ///
    /// #   Panics
    ///
    /// If `at` is strictly greater than `tree.len()`.
    pub fn move_to(&mut self, at: usize) {
        self.node = self.peek_at_node(at);

        self.index = at;
    }

    /// Attempts to move the cursor to the next element, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no next element, or is the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn try_move_next(&mut self) -> Option<&'a T> {
        let (node, index) = self.peek_next_node();

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the previous element, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no previous element, or is the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn try_move_prev(&mut self) -> Option<&'a T> {
        let (node, index) = self.peek_prev_node();

        if let Some(_) = node {
            self.index = index;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the element at the given index, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If there is not such element, or the cursor points to the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    ///
    /// #   Panics
    ///
    /// If `at` is strictly greater than `tree.len()`.
    pub fn try_move_to(&mut self, at: usize) -> Option<&'a T> {
        self.node?;

        let node = self.peek_at_node(at);

        if let Some(_) = node {
            self.index = at;
            self.node = node;
            self.current()
        } else {
            None
        }
    }

    /// Returns a reference to the next element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_next(&self) -> Option<&'a T> { self.peek_next_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the previous element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_prev(&self) -> Option<&'a T> { self.peek_prev_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the element at the given index, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_at(&self, at: usize) -> Option<&'a T> { self.peek_at_node(at).map(|node| &node.borrow(self.token).value) }

    //  Internal; returns the length of the tree.
    fn len(&self) -> usize { self.tree.len(self.token) }

    //  Internal; returns a reference to the GhostNode at the next index.
    fn peek_next_node(&self) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        let index = if let Some(_) = self.node {
            self.index + 1
        } else {
            0
        };

        (self.peek_at_node(index), index)
    }

    //  Internal; returns a reference to the GhostNode at the previous index.
    fn peek_prev_node(&self) -> (Option<&'a GhostNode<'brand, T>>, usize) {
        let index = if let Some(_) = self.node {
            self.index.checked_sub(1).unwrap_or_else(|| self.len())
        } else {
            self.len().checked_sub(1).unwrap_or(0)
        };

        (self.peek_at_node(index), index)
    }

    //  Internal; returns a reference to the GhostNode at the specific index.
    //
    //  Panics if the index is "too" out of bounds; returns the "twilight" non-element if the index is only 1 out of bounds.
    fn peek_at_node(&self, at: usize) -> Option<&'a GhostNode<'brand, T>> {
        let length = self.len();

        assert!(at <= length, "at ({}) > self.tree.len() ({})", at, length);

        if at == length {
            return None;
        }

        if at == self.index {
            return self.node;
        }

        let mut cursor = match (self.node, self.tree.root.as_ref().map(|n| &**n)) {
            (Some(_), Some(root)) => {
                let root_index = root.borrow(self.token).index(self.token);

                if at >= root_index && root_index > self.index {
                    Cursor::new(self.token, self.tree)
                } else if at <= root_index && root_index < self.index {
                    Cursor::new(self.token, self.tree)
                } else {
                    self.clone()
                }
            },
            (Some(_), None) => self.clone(),
            (None, Some(_)) => Cursor::new(self.token, self.tree),
            (None, None) => unreachable!("at >= length, then"),
        };

        //  In this case, move start to the first common ancestor of start and the node at index `at`.
        if self.index == cursor.index {
            while !cursor.range().contains(&at) {
                cursor.move_up();
            }
        }

        //  From then on, we are guaranteed that `cursor` is pointing to an ancestor of `at`, so it's somewhere down.
        let mut max_iteration = length + 1;
        loop {
            use cmp::Ordering::*;

            let index = cursor.index;
            debug_assert!(cursor.range().contains(&at), "{:?} does not contain {}", cursor.range(), at);

            match at.cmp(&index) {
                Less => {
                    cursor.move_left();
                    debug_assert!(cursor.index < index);
                },
                Equal => break,
                Greater => {
                    cursor.move_right();
                    debug_assert!(cursor.index > index);
                },
            }

            debug_assert!(max_iteration > 0);
            max_iteration = max_iteration.saturating_sub(1);
        }

        debug_assert_eq!(at, cursor.index);

        cursor.node
    }
}

impl<'a, 'brand, T> Clone for Cursor<'a, 'brand, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, 'brand, T> Copy for Cursor<'a, 'brand, T> {}

/// A mutable cursor over the TripodTree.
///
/// A mutable cursor allows freely moving back-and-forth amongst the elements of the tree, and mutate the tree as any
/// point.
///
/// Cursors index the tree in a logically circular way. To accomodate this, there is a "twilight" non-element
/// represented by `None` between the root and leaves of the tree.
///
/// #   Warning.
///
/// This cursor mutates the tree as it iterates. Although the tree is left in a safe state by construction, forgoing the
/// drop of this cursor -- unless it points to the "twilight" non-element -- will leave the tree in an unusable state.
///
/// Any further mutable operation on the tree, including calling `clear`, is at risk of panicking.
pub struct CursorMut<'a, 'brand, T> {
    token: &'a mut GhostToken<'brand>,
    tree: &'a mut TripodTree<'brand, T>,
    node: Option<QuarterNodePtr<'brand, T>>,
    index: usize,
}

//  Constant time cursor navigation.
impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Creates a new instance pointing to the front element of the tree, if any.
    pub fn new(token: &'a mut GhostToken<'brand>, tree: &'a mut TripodTree<'brand, T>) -> Self {
        let (node, index) = Self::root_of(token, tree);
        let node = node.map(|node| node.borrow(token).deploy());

        Self { token, index, node, tree, }
    }

    /// Returns a read-only cursor pointing to the current element.
    pub fn as_cursor(&self) -> Cursor<'_, 'brand, T> {
        let token = &*self.token;
        let index = self.index;
        let node = self.node.as_ref().map(|rc| &**rc);
        let tree = &*self.tree;

        Cursor { token, index, node, tree, }
    }

    /// Returns the index of the element pointed to by the cursor in the tree.
    ///
    /// If the cursor currently points to the "twilight" non-element, returns None.
    pub fn index(&self) -> Option<usize> { self.node.as_ref().map(|_| self.index) }

    /// Returns the range of indices covered by the sub-tree rooted at node the cursor is pointing at.
    ///
    /// If the cursor points to the new "twilight" non-element, None is returned.
    pub fn range(&self) -> Range<usize> { self.as_cursor().range() }

    /// Moves the cursor to the parent element, if any.
    ///
    /// If the cursor points to the "twilight" non-element, nothing happens.
    pub fn move_up(&mut self) {
        let (node, index) = self.peek_up_node();
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Moves the cursor to the left element.
    ///
    /// If the element the cursor points to has no left element, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_left(&mut self) {
        let (node, index) = self.peek_left_node();
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Moves the cursor to the right element.
    ///
    /// If the element the cursor points to has no right element, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_right(&mut self) {
        let (node, index) = self.peek_right_node();
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Moves the cursor to the child element on the design side.
    ///
    /// If the element the cursor points to has no such element, moves to the "twilight" non-element.
    ///
    /// If the cursor points to the "twilight" non-element, moves to the root instead, if any.
    pub fn move_down(&mut self, side: Side) {
        let (node, index) = self.peek_down_node(side);
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Attempts to move the cursor to the parent element, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no parent element, or is the "twilight" element, nothing
    /// happens and None is returned.
    pub fn try_move_up(&mut self) -> Option<&mut T> {
        let (node, index) = self.peek_up_node();

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the left child, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no left child, or is the "twilight" non-element, nothing
    /// happens and None is returned.
    pub fn try_move_left(&mut self) -> Option<&mut T> {
        let (node, index) = self.peek_left_node();

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the right child, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no right child, or is the "twilight" non-element, nothing
    /// happens and None is returned.
    pub fn try_move_right(&mut self) -> Option<&mut T> {
        let (node, index) = self.peek_right_node();

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor down to the designed side, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor is pointing to has no child on that side, or is the "twilight" non-element, nothing
    /// happens and None is returned.
    pub fn try_move_down(&mut self, side: Side) -> Option<&mut T> {
        let (node, index) = self.peek_down_node(side);

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Returns a reference to the current element, if any.
    pub fn current(&mut self) -> Option<&mut T> {
        let tripod = self.node.as_ref()?;
        Some(&mut tripod.borrow_mut(self.token).value)
    }

    /// Returns a reference to the up element, if any.
    pub fn peek_up(&self) -> Option<&T> { self.peek_up_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the left element, if any.
    pub fn peek_left(&self) -> Option<&T> { self.peek_left_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the right element, if any.
    pub fn peek_right(&self) -> Option<&T> { self.peek_right_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the child element on the designed side, if any.
    pub fn peek_down(&self, side: Side) -> Option<&T> { self.peek_down_node(side).0.map(|node| &node.borrow(self.token).value) }

    //  Internal; move to the root node.
    fn move_to_root(&mut self) {
        //  If list empty, no root to move to.
        if self.tree.is_empty() {
            return;
        }

        //  If pointing at root, no need to move.
        if self.node.is_some() && self.peek_up().is_none() {
            return;
        }

        let root_tripod = self.tree.root.as_ref().map(|node| self.deploy_tripod(node));
        let root_index = root_tripod.as_ref().map(|tripod| tripod.borrow(self.token).index(self.token)).unwrap_or(0);

        self.switch_tripod(root_tripod, root_index);
    }

    //  Internal; move to the front node.
    fn move_to_front(&mut self) {
        self.move_to_root();

        while let Some(_) = self.try_move_left() {}
    }

    //  Internal; move to the back node.
    fn move_to_back(&mut self) {
        self.move_to_root();

        while let Some(_) = self.try_move_right() {}
    }

    //  Internal; extract the root and its index from the tree.
    fn root_of<'b>(token: &'b GhostToken<'brand>, tree: &'b TripodTree<'brand, T>) -> (Option<&'b GhostNode<'brand, T>>, usize) {
        let root = tree.root.as_ref().map(|node| &**node);
        let index = root.map(|node| node.borrow(token).index(token)).unwrap_or(0);

        (root, index)
    }

    //  Internal; deploys a tripod.
    fn deploy_tripod(&self, node: &GhostNode<'brand, T>) -> QuarterNodePtr<'brand, T> { node.borrow(self.token).deploy() }

    //  Internal; deploys a tripod.
    fn retract_tripod(&mut self, node: QuarterNodePtr<'brand, T>) {
        super::retract(node, self.token);
    }

    //  Internal; replace the current tripod with another, retracting the former if any.
    fn switch_tripod(&mut self, new_tripod: Option<QuarterNodePtr<'brand, T>>, index: usize) {
        self.index = index;

        if let Some(tripod) = mem::replace(&mut self.node, new_tripod) {
            super::retract(tripod, self.token);
        }
    }

    //  Internal; returns a reference to the up GhostNode, and the matching index.
    fn peek_up_node(&self) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_up_node()
    }

    //  Internal; returns a reference to the left GhostNode, and the matching index.
    fn peek_left_node(&self) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_left_node()
    }

    //  Internal; returns a reference to the right GhostNode, and the matching index.
    fn peek_right_node(&self) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_right_node()
    }

    //  Internal; returns a reference to the child GhostNode on the designed side, and the matching index.
    fn peek_down_node(&self, side: Side) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_down_node(side)
    }
}

//  Logarithmic cursor navigation.
impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Creates a new cursor pointing at the front element of the tree, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn new_front(token: &'a mut GhostToken<'brand>, tree: &'a mut TripodTree<'brand, T>) -> Self {
        let mut cursor = Self::new(token, tree);

        while let Some(_) = cursor.try_move_left() {}

        debug_assert_eq!(0, cursor.index);

        cursor
    }

    /// Creates a new cursor pointing at the back element of the tree, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn new_back(token: &'a mut GhostToken<'brand>, tree: &'a mut TripodTree<'brand, T>) -> Self {
        let mut cursor = Self::new(token, tree);

        while let Some(_) = cursor.try_move_right() {}

        debug_assert_eq!(cursor.len() - 1, cursor.index);

        cursor
    }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, then the cursor moves to the "twilight" non-element, which exists between the root
    /// and the leaves.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_next(&mut self) {
        let (node, index) = self.peek_next_node();
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, then the cursor moves to the "twilight" non-element, which exists between the root
    /// and the leaves.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn move_prev(&mut self) {
        let (node, index) = self.peek_prev_node();
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, index);
    }

    /// Moves the cursor to the element at the given index.
    ///
    /// If there is no such element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    ///
    /// #   Panics
    ///
    /// If `at` is strictly greater than `tree.len()`.
    pub fn move_to(&mut self, at: usize) {
        if self.index == at {
            return;
        }

        let node = self.peek_at_node(at);
        let new_tripod = node.map(|node| self.deploy_tripod(node));

        self.switch_tripod(new_tripod, at);
    }

    /// Attempts to move the cursor to the next element, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no next element, or is the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn try_move_next(&mut self) -> Option<&mut T> {
        let (node, index) = self.peek_next_node();

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the previous element, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If the element the cursor points to has no previous element, or is the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn try_move_prev(&mut self) -> Option<&mut T> {
        let (node, index) = self.peek_prev_node();

        if let Some(_) = node {
            let new_tripod = node.map(|node| self.deploy_tripod(node));
            self.switch_tripod(new_tripod, index);
            self.current()
        } else {
            None
        }
    }

    /// Attempts to move the cursor to the element at the given index, if any.
    ///
    /// Returns a reference to the pointed to element, in case of success.
    ///
    /// If there is not such element, or the cursor points to the "twilight" element, does not move.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    ///
    /// #   Panics
    ///
    /// If `at` is strictly greater than `tree.len()`.
    pub fn try_move_to(&mut self, at: usize) -> Option<&mut T> {
        self.node.as_ref()?;

        if self.index == at {
            return self.current();
        }

        let node = self.peek_at_node(at);

        if let Some(node) = node {
            let new_tripod = Some(self.deploy_tripod(node));

            self.switch_tripod(new_tripod, at);
            self.current()
        } else {
            None
        }
    }

    /// Returns a reference to the next element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_next(&self) -> Option<&T> { self.peek_next_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the previous element, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_prev(&self) -> Option<&T> { self.peek_prev_node().0.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the element at the given index, if any.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of element.
    /// -   Space: O(1).
    pub fn peek_at(&self, at: usize) -> Option<&T> { self.peek_at_node(at).map(|node| &node.borrow(self.token).value) }

    //  Internal; returns the length of the tree.
    fn len(&self) -> usize { self.tree.len(self.token) }

    //  Internal; returns a reference to the GhostNode at the next index.
    fn peek_next_node(&self) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_next_node()
    }

    //  Internal; returns a reference to the GhostNode at the previous index.
    fn peek_prev_node(&self) -> (Option<&GhostNode<'brand, T>>, usize) {
        self.as_cursor().peek_prev_node()
    }

    //  Internal; returns a reference to the GhostNode at the specific index.
    //
    //  Panics if the index is "too" out of bounds; returns the "twilight" non-element if the index is only 1 out of bounds.
    fn peek_at_node(&self, at: usize) -> Option<&GhostNode<'brand, T>> {
        self.as_cursor().peek_at_node(at)
    }
}

//  Edit cursor operations.
impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Inserts a new element in the tree after the current one.
    ///
    /// See `splice_after` for the details.
    ///
    /// A single memory allocation is performed.
    pub fn insert_after(&mut self, value: T) {
        let mut other = TripodTree::singleton(value, self.token);
        self.splice_after(&mut other);
    }

    /// Inserts a new element in the tree before the current one.
    ///
    /// See `splice_before` for the details.
    ///
    /// A single memory allocation is performed.
    pub fn insert_before(&mut self, value: T) {
        let mut other = TripodTree::singleton(value, self.token);
        self.splice_before(&mut other);
    }

    /// Removes the current element from the tree.
    ///
    /// See `remove_current_as_tree` for details.
    ///
    /// A single memory deallocation is performed.
    pub fn remove_current(&mut self) -> Option<T> {
        let removed = self.remove_current_as_tree();
        debug_assert!(removed.len(self.token) <= 1, "{} > 1", removed.len(self.token));

        removed.root.map(|root| { TripodTree::node_into_inner(root, self.token) })
    }

    /// Removes the current element from the tree and returns it as a `TripodTree`.
    ///
    /// The removed element is returned, and the cursor is moved to point to the next element, if any.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then no element is removed and `None` is returned.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of elements.
    /// -   Space: O(1).
    ///
    /// No memory allocation nor deallocation occur.
    pub fn remove_current_as_tree(&mut self) -> TripodTree<'brand, T> {
        //  Short circuit if not interesting.
        if self.node.is_none() {
            return TripodTree::new();
        }

        self.describe_self("remove_current_as_tree (begin)");

        //  Memorize index, to restore it.
        let index = self.index;

        //  Push node down until it's a leaf in the deepest sub-tree, recursively => O(log N).
        self.sift_down();

        //  Remove leaf, fixing up parents if any.
        let current_tripod = self.node.take().expect("There should be a node");

        let _current_size = current_tripod.borrow(self.token).size;
        debug_assert_eq!(1, _current_size, "And this node should be a leaf");

        let current = if let Some(parent) = current_tripod.borrow_mut(self.token).up.take() {
            let parent_tripod = self.deploy_tripod(&parent);

            let parent_side = current_tripod.borrow(self.token).is_child_of(parent.borrow(self.token)).expect("Child!");
            let current = parent_tripod.borrow_mut(self.token).replace_child(parent_side, parent).expect("Current!");

            self.adjust_size(&parent_tripod);

            //  Removing the left leaf means the parent takes its place, index-wise.
            //  Removing the right leaf and switching to the parent, however, requires adjusting the index.
            if parent_side == Side::Right {
                self.index -= 1;
            }

            //  O(log N).
            self.rebalance_tree_single(parent_tripod);

            self.move_to(index);

            current
        } else {
            //  The node is the current root, and it's a leaf => no-one else here!
            self.tree.root.take().expect("Non-empty!")
        };

        self.retract_tripod(current_tripod);

        self.describe_self("remove_current_as_tree (end)");

        TripodTree::from_quarter(current, self.token)
    }

    /// Inserts a new tree in the tree after the current one.
    ///
    /// Although the cursor remains pointed to the same element, the position of the element may have changed
    /// drastically due to rebalancing.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new tree is inserted at the front.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of elements.
    /// -   Space: O(1).
    ///
    /// No memory allocation nor deallocation occur.
    pub fn splice_after(&mut self, other: &mut TripodTree<'brand, T>) {
        //  We'll be getting back to this index.
        let original = self.index();

        self.splice_impl(Side::Right, other);

        self.move_to(original.unwrap_or_else(|| self.len()));

        debug_assert_eq!(original, self.index());
    }

    /// Inserts a new tree in the tree before the current one.
    ///
    /// Although the cursor remains pointed to the same element, the position of the element may have changed
    /// drastically due to rebalancing.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new tree is inserted at the back.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of elements.
    /// -   Space: O(1).
    ///
    /// No memory allocation nor deallocation occur.
    pub fn splice_before(&mut self, other: &mut TripodTree<'brand, T>) {
        //  We'll be getting back to this index.
        let original = self.index();
        let other_size = other.len(self.token);

        self.splice_impl(Side::Left, other);

        self.move_to(original.map(|n| n + other_size).unwrap_or_else(|| self.len()));

        debug_assert_eq!(original.map(|n| n + other_size), self.index());
    }

    /// Splits the tree into two after the current element.
    ///
    /// Returns a tree consisting of everything after the current element.
    ///
    /// If the cursor is pointing at the "twilight" non-element, returns everything.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log² N) in the number of elements.
    /// -   Space: O(1).
    ///
    /// No memory allocation nor deallocation occur.
    pub fn split_after(&mut self) -> TripodTree<'brand, T> {
        let result = self.split_impl(Side::Right);

        self.move_to_back();

        result
    }

    /// Splits the tree into two before the current element.
    ///
    /// Returns a tree consisting of everything before the current element.
    ///
    /// If the cursor is pointing at the "twilight" non-element, returns everything.
    ///
    /// #   Complexity
    ///
    /// -   Time: O(log N) in the number of elements.
    /// -   Space: O(1).
    ///
    /// No memory allocation nor deallocation occur.
    pub fn split_before(&mut self) -> TripodTree<'brand, T> {
        let result = self.split_impl(Side::Left);

        self.move_to_front();

        result
    }

    //  Internal; sift down current index, until it's a leaf, by pushing it alongst the deepest path.
    //
    //  Complexity: Time O(log N), Space O(1).
    fn sift_down(&mut self) {
        //  O(log N) iterations, each doing O(1) work.
        loop {
            let current_tripod = self.node.take().expect("Non-twilight");

            let _current_size = current_tripod.borrow(self.token).size;
            let left_size = current_tripod.borrow(self.token).left_size(self.token);
            let right_size = current_tripod.borrow(self.token).right_size(self.token);

            debug_assert_eq!(_current_size, 1 + left_size + right_size,
                "sift_down - {} != 1 + {} + {}", _current_size, left_size, right_size);

            //  Leaf!
            if left_size == 0 && right_size == 0 {
                self.node = Some(current_tripod);
                return;
            }

            //  Going down
            let side = if left_size > right_size { Side::Left } else { Side::Right };
            self.swap_child_from(side, current_tripod);
        }
    }

    //  Internal; splice_before/after, without any guarantee with regard to the position of the index.
    //
    //  Complexity: Time O(log² N), Space O(1).
    fn splice_impl(&mut self, side: Side, other: &mut TripodTree<'brand, T>) {
        self.describe_self("splice_impl (begin)");

        let other_root = if let Some(other_root) = other.root.take() {
            other_root
        } else {
            self.describe_self("splice_impl (end) (empty)");
            return;
        };

        if self.tree.is_empty() {
            self.index = other_root.borrow(self.token).size;
            self.tree.root = Some(other_root);
            return;
        }

        let opposite = side.opposite();

        //  No root.
        if self.index().is_none() {
            match side {
                //  Place at the back.
                Side::Left => self.move_to_back(),
                //  Place at the front.
                Side::Right => self.move_to_front(),
            }

            self.set_subtree(opposite, other_root);

            self.describe_self("splice_impl (end) (twilight)");
            return;
        }

        //  Otherwise, place at opposite-side-most child of side sub-tree.
        if let Some(_) = self.try_move_down(side) {
            while let Some(_) = self.try_move_down(opposite) {}

            self.set_subtree(opposite, other_root);
        } else {
            //  Unless there's no side child.
            self.set_subtree(side, other_root);
        }

        self.describe_self("splice_impl (end)");
    }

    //  Internal; splits the tree into two, taking all elements on the given side into the new tree.
    //
    //  Complexity: Time O(log² N), Space O(1).
    fn split_impl(&mut self, side: Side) -> TripodTree<'brand, T> {
        if self.node.is_none() {
            self.index = 0;
            return mem::replace(self.tree, TripodTree::new());
        }

        //  Special cases, taking a left-most or right-most sub-tree.
        {
            let node = self.node.as_ref().expect("Non-empty");

            match side {
                Side::Left if self.range().start == 0 => {
                    let result = TripodTree { root: Self::take_child(side, node, self.token) };
                    self.index = 0;

                    let current_tripod = self.node.take().expect("Non-empty");
                    self.rebalance_tree_single(current_tripod);

                    return result;
                },
                Side::Right if self.range().end == self.len() => {
                    let result = TripodTree { root: Self::take_child(side, node, self.token) };

                    let current_tripod = self.node.take().expect("Non-empty");
                    self.rebalance_tree_single(current_tripod);

                    return result;
                },
                _ => (),
            }
        }

        //  Computing which elements should go, and which shouldn't, is fairly complicated.
        //
        //  The one exception: when the current node is the root, then one side stays and one side goes!
        //
        //  So... we're going to have a simple plan:
        //
        //  1.  Make the current node root.
        //      a.  Keep its children balanced.
        //  2.  Strip off its `side` child, this is our tree.
        //  3.  Repeatedly rebalance until the entire tree is balanced.
        //  4.  Profit!

        self.describe_self("split_impl (begin)");

        //  1.  Make the current node root => O(log N), from O(log N) iterations each doing O(1) work.
        while let Some(parent_side) = self.node.as_ref().and_then(|node| node.borrow(self.token).is_child(self.token)) {
            self.move_up();

            let parent_tripod = self.node.take().expect("Non-empty");
            self.rotate_child_from(parent_side, parent_tripod);

            //  a.  Keep its children balanced.
            let parent = self.node.take().expect("Non-empty");

            self.rebalance_child(Side::Left, &parent);
            self.rebalance_child(Side::Right, &parent);

            self.node = Some(parent);

            self.describe_self("split_impl (post incremental rotation)");
        }

        self.describe_self("split_impl (pre split)");

        //  2.  Strip off its `side` child => O(1).
        let result = {
            let node = self.node.as_ref().expect("Non-empty");

            TripodTree { root: Self::take_child(side, node, self.token) }
        };

        if side == Side::Left {
            debug_assert_eq!(result.len(self.token), self.index);
            self.index = 0;
        }

        self.describe_self("split_impl (post split)");

        //  3.  Repeatedly rebalance, until it's balanced => O(log N) iterations each doing O(log N) work.
        let current_tripod = self.node.take().expect("Non-empty");
        self.rebalance_subtree_complete(current_tripod);

        result
    }

    //  Internal; sets the tree as the child of the current node. Fixes up indexes and rebalances.
    //
    //  Leaves the cursor pointing to the root.
    //
    //  Requirement: there must be not such child.
    //
    //  Complexity: Time O(log² N), Space O(1).
    fn set_subtree(&mut self, side: Side, other_root: QuarterNodePtr<'brand, T>) {
        debug_assert!(self.node.is_some());
        debug_assert!(side == Side::Right || self.peek_left().is_none());
        debug_assert!(side == Side::Left || self.peek_right().is_none());

        self.describe_self("set_subtree (begin)");

        let root_tripod = self.node.take().expect("Not empty");
        let other_tripod = self.deploy_tripod(&other_root);
        let other_size = other_tripod.borrow(self.token).size;

        let current = root_tripod.borrow_mut(self.token).replace_child(side, other_root).expect("Side child - pointing to self");
        other_tripod.borrow_mut(self.token).up.replace(current);

        self.retract_tripod(other_tripod);

        root_tripod.borrow_mut(self.token).size += other_size;

        if side == Side::Left {
            self.index += other_size;
        }

        self.rebalance_tree_complete(root_tripod);

        self.describe_self("set_child (end)");
    }

    //  Internal; rebalances the tree up to the root, adjusting the node size as it goes.
    //
    //  The cursor is left pointing to the root. The index is adjusted accordingly.
    //
    //  Complexity: Time O(log² N), Space O(1).
    fn rebalance_tree_complete(&mut self, root_tripod: QuarterNodePtr<'brand, T>) {
        self.describe_node("rebalance_tree_complete (begin)", &root_tripod);

        self.rebalance_subtree_complete(root_tripod);

        //  O(log N) iterations of O(log N) complexity.
        while let Some(_) = self.try_move_up() {
            self.describe_self("rebalance_tree_complete (loop)");

            let root_tripod = self.node.take().expect("Not empty");

            self.adjust_size(&root_tripod);
            self.rebalance_subtree_complete(root_tripod)
        }

        self.describe_self("rebalance_tree_complete (end)");
    }

    //  Internal; rebalances the tree up to the root, of at most 1 single step, adjusting the node size as it goes.
    //
    //  The cursor is left pointing to the root. The index is adjusted accordingly.
    //
    //  Complexity: Time O(log N), Space O(1).
    fn rebalance_tree_single(&mut self, root_tripod: QuarterNodePtr<'brand, T>) {
        self.describe_node("rebalance_tree_single (begin)", &root_tripod);

        self.rebalance_subtree_single(root_tripod);

        while let Some(_) = self.try_move_up() {
            self.describe_self("rebalance_tree_single (loop)");

            let root_tripod = self.node.take().expect("Not empty");

            self.adjust_size(&root_tripod);
            self.rebalance_subtree_single(root_tripod)
        }

        self.describe_self("rebalance_tree_single (end)");
    }

    //  Internal; rebalances the current sub-tree, if necessary.
    //
    //  The cursor is left pointing at the root of the sub-tree, whether it changed or not. The index is adjusted
    //  accordingly.
    //
    //  Complexity: Time O(log N), Space O(1).
    fn rebalance_subtree_complete(&mut self, mut root_tripod: QuarterNodePtr<'brand, T>) {
        self.describe_node("rebalance_subtree_complete (begin)", &root_tripod);

        let mut previous_index = self.index;

        loop {
            self.rebalance_subtree_single(root_tripod);

            if previous_index == self.index {
                break;
            }

            previous_index = self.index;

            root_tripod = self.node.take().expect("Non-empty");

            self.rebalance_child(Side::Left, &root_tripod);
            self.rebalance_child(Side::Right, &root_tripod);

            self.describe_node("rebalance_subtree_complete (loop)", &root_tripod);
        }

        self.describe_self("rebalance_subtree_complete (end)");
    }

    //  Internal; rebalances the current sub-tree by 1 single step, if necessary.
    //
    //  The cursor is left pointing at the root of the sub-tree, whether it changed or not. The index is adjusted
    //  accordingly.
    //
    //  Complexity: Time O(1), Space O(1).
    fn rebalance_subtree_single(&mut self, root_tripod: QuarterNodePtr<'brand, T>) {
        debug_assert!(self.node.is_none());

        let left_size = root_tripod.borrow(self.token).left_size(self.token);
        let right_size = root_tripod.borrow(self.token).right_size(self.token);

        if left_size > 2 * right_size + 1 {
            let root_tripod = self.prepare_rotation(Side::Left, root_tripod);
            self.rotate_child_from(Side::Left, root_tripod);
        } else if right_size > 2 * left_size + 1 {
            let root_tripod = self.prepare_rotation(Side::Right, root_tripod);
            self.rotate_child_from(Side::Right, root_tripod);
        } else {
            self.node = Some(root_tripod);
        }
    }

    //  Internal; rebalances the parent's child on the designated side.
    //
    //  Complexity: Time O(1), Space O(1).
    fn rebalance_child(&mut self, side: Side, parent: &GhostNode<'brand, T>) {
        if let Some(child) = parent.borrow_mut(self.token).take_child(side) {
            let child_tripod = child.borrow(self.token).deploy();
            let child_index = child_tripod.borrow(self.token).index(self.token);
            let parent_from_child = child_tripod.borrow_mut(self.token).up.take();

            let mut tree = TripodTree { root: Some(child) };

            let child_tripod = {
                let mut cursor = CursorMut { token: self.token, tree: &mut tree, node: None, index: child_index };
                cursor.rebalance_subtree_single(child_tripod);
                cursor.node.take().expect("Non-empty")
            };

            let child = tree.root.take().expect("Non-empty");

            child.borrow(self.token).retract(child_tripod);
            child.borrow_mut(self.token).up = parent_from_child;

            parent.borrow_mut(self.token).set_child(side, child);
        }
    }

    //  Internal; swaps the current root of the sub-tree with its child.
    //
    //  The cursor is left pointing at the former root, the index is adjusted accordingly.
    //
    //  Invoked with Side::Left:
    //
    //          Pa                  Pa
    //          |                   |
    //        Root                 Piv
    //         / \                 / \
    //        /   \               /   \
    //      Piv    X    =>     Root    X
    //      / \                / \
    //     Y   Z              Y   Z
    //
    //  Invoked with Side::Right:
    //
    //          Pa                  Pa
    //          |                   |
    //        Root                 Piv
    //         / \                 / \
    //        /   \               /   \
    //       X   Piv   =>        X   Root
    //           / \                 / \
    //          Y   Z               Y   Z
    //
    //  Legend:
    //  -   Pa: Parent, potentially tree.root.
    //  -   Root: the current root of the sub-tree.
    //  -   Piv: the pivot, or future root of the sub-tree post-rotation.
    //
    //  Complexity: Time O(1), Space O(1).
    fn swap_child_from(&mut self, side: Side, root_tripod: QuarterNodePtr<'brand, T>) {
        debug_assert!(self.node.is_none());

        self.describe_node("swap_child_from (begin)", &root_tripod);

        let opposite = side.opposite();

        //  Pick out pivot.
        let pivot = root_tripod.borrow_mut(self.token).take_child(side).expect("Selected child - otherwise we shouldn't attempt to swap");
        let pivot_tripod = self.deploy_tripod(&pivot);

        self.describe_node("swap_child_from (pivot)", &pivot_tripod);

        //  Swap opposite children, if any.
        {
            let opposite_root = root_tripod.borrow_mut(self.token).take_child(opposite);
            let opposite_pivot = pivot_tripod.borrow_mut(self.token).take_child(opposite);

            match (opposite_root, opposite_pivot) {
                (Some(opposite_root), Some(opposite_pivot)) => {
                    let root_from_opposite = opposite_root.borrow_mut(self.token).up.take();
                    let pivot_from_opposite = opposite_pivot.borrow_mut(self.token).up.take();

                    opposite_pivot.borrow_mut(self.token).up = root_from_opposite;
                    opposite_root.borrow_mut(self.token).up = pivot_from_opposite;

                    root_tripod.borrow_mut(self.token).set_child(opposite, opposite_pivot);
                    pivot_tripod.borrow_mut(self.token).set_child(opposite, opposite_root);
                },
                (None, Some(opposite_pivot)) => {
                    let root_from_self = root_tripod.borrow_mut(self.token).child_mut(opposite).take().expect("root.opposite == root");
                    let pivot_from_opposite = opposite_pivot.borrow_mut(self.token).up.replace(root_from_self).expect("pivot.opposite.up == pivot");

                    root_tripod.borrow_mut(self.token).set_child(opposite, opposite_pivot);
                    pivot_tripod.borrow_mut(self.token).set_child(opposite, pivot_from_opposite);
                },
                (Some(opposite_root), None) => {
                    let pivot_from_self = pivot_tripod.borrow_mut(self.token).child_mut(opposite).take().expect("pivot.opposite == pivot");
                    let root_from_opposite = opposite_root.borrow_mut(self.token).up.replace(pivot_from_self).expect("root.opposite.up == root");

                    pivot_tripod.borrow_mut(self.token).set_child(opposite, opposite_root);
                    root_tripod.borrow_mut(self.token).set_child(opposite, root_from_opposite);
                },
                (None, None) => (),
            }
        };

        //  Swap parent.
        let root_from_pivot = pivot_tripod.borrow_mut(self.token).up.take().expect("pivot.up == root");

        let root_from_parent = {
            let parent_root = root_tripod.borrow_mut(self.token).up.take();

            if let Some(parent_root) = parent_root {
                let parent_side = root_tripod.borrow(self.token).is_child_of(parent_root.borrow(self.token)).expect("Child!");

                let root_from_parent = parent_root.borrow_mut(self.token).replace_child(parent_side, pivot).expect("parent.child == root");
                pivot_tripod.borrow_mut(self.token).up = Some(parent_root);

                root_from_parent
            } else {
                //  root_tripod is root.
                self.tree.root.replace(pivot).expect("root")
            }
        };

        //  Swap selected child and parent, if any.
        {
            let child_pivot = pivot_tripod.borrow_mut(self.token).take_child(side);

            if let Some(child_pivot) = child_pivot {
                pivot_tripod.borrow_mut(self.token).set_child(side, root_from_parent);

                let pivot_from_child = child_pivot.borrow_mut(self.token).up.replace(root_from_pivot).expect("child.up == pivot");
                root_tripod.borrow_mut(self.token).set_child(side, pivot_from_child);
            } else {
                //  Pivot.side pointing to self.
                let pivot_from_self = pivot_tripod.borrow_mut(self.token).replace_child(side, root_from_parent);

                root_tripod.borrow_mut(self.token).up = pivot_from_self;
                root_tripod.borrow_mut(self.token).set_child(side, root_from_pivot);
            }
        }

        self.adjust_size(&root_tripod);
        self.adjust_size(&pivot_tripod);

        self.retract_tripod(pivot_tripod);

        let new_index = {
            let opposite_pivot_size = root_tripod.borrow(self.token).child_size(opposite, self.token);
            match side {
                Side::Left => self.index - 1 - opposite_pivot_size,
                Side::Right => self.index + 1 + opposite_pivot_size,
            }
        };

        self.switch_tripod(Some(root_tripod), new_index);

        self.describe_self("swap_child_from (end)");
    }

    //  Internal; rotates the current sub-tree so that the selected child becomes the root.
    //
    //  The cursor is left pointing at the new root of the sub-tree (pivot), the index is adjusted accordingly.
    //
    //  Invoked with Side::Left:
    //
    //          Pa                  Pa
    //          |                   |
    //        Root                  Piv
    //         / \                 / \
    //        /   \               /   \
    //      Piv   X     =>       Y     Root
    //      / \                        / \
    //     Y   Piv.OS            Piv.OS   X
    //
    //  Invoked with Side::Right:
    //
    //          Pa                  Pa
    //          |                   |
    //        Root                 Piv
    //         / \                 / \
    //        /   \               /   \
    //       X   Piv     =>    Root    Y
    //           / \           / \
    //     Piv.OS   Y         X   Piv.OS
    //
    //  Legend:
    //  -   Pa: Parent, potentially tree.root.
    //  -   Root: the current root of the sub-tree.
    //  -   Piv: the pivot, or future root of the sub-tree post-rotation.
    //  -   Piv.OS: the child of the pivot, on the opposite side.
    //
    //  Complexity: Time O(1), Space O(1).
    fn rotate_child_from(&mut self, side: Side, root_tripod: QuarterNodePtr<'brand, T>) {
        debug_assert!(self.node.is_none());

        self.describe_node("rotate_child_from (begin)", &root_tripod);

        let opposite = side.opposite();

        //  Pick out pivot.
        let pivot = root_tripod.borrow_mut(self.token).take_child(side).expect("Selected child - otherwise we shouldn't attempt to rotate");
        let pivot_tripod = self.deploy_tripod(&pivot);

        let root_from_pivot = pivot_tripod.borrow_mut(self.token).up.take().expect("Parent - root!");
        debug_assert!(root_tripod.borrow(self.token).is_aliased(Some(&root_from_pivot)), "root == pivot.up");

        //  Extract pivot pointer from opposite-child up.
        let pivot_from_opposite_child = {
            let opposite_child = pivot_tripod.borrow_mut(self.token).child_mut(opposite).take().expect("Either child or pivot-self");

            //  Aliased => actual self-points to pivot, which didn't have an opposite-side child.
            let (pivot, child) = if pivot_tripod.borrow(self.token).is_aliased(Some(&opposite_child)) {
                (opposite_child, root_from_pivot)
            } else {
                let pivot = opposite_child.borrow_mut(self.token).up.replace(root_from_pivot).expect("opposite_child.up == pivot");

                (pivot, opposite_child)
            };

            debug_assert!(pivot.borrow(self.token).is_aliased(Some(&pivot_tripod)), "pivot.opposite_child.up == pivot");

            root_tripod.borrow_mut(self.token).set_child(side, child);

            pivot
        };

        //  Switch pointer-to-root to pointer-to-pivot in parent.
        let root_from_parent = {
            let parent = root_tripod.borrow_mut(self.token).up.replace(pivot);

            if let Some(parent) = parent {
                let parent_side = root_tripod.borrow(self.token).is_child_of(parent.borrow(self.token)).expect("root.up == parent!");

                let result = parent.borrow_mut(self.token).replace_child(parent_side, pivot_from_opposite_child)
                    .expect("parent.parent_side_child == root");

                pivot_tripod.borrow_mut(self.token).up = Some(parent);

                result
            } else {
                self.tree.root.replace(pivot_from_opposite_child).expect("tree.root == root")
            }
        };

        debug_assert!(root_tripod.borrow(self.token).is_aliased(Some(&root_from_parent)), "root == pivot.up");

        pivot_tripod.borrow_mut(self.token).set_child(opposite, root_from_parent);

        self.adjust_size(&root_tripod);
        self.adjust_size(&pivot_tripod);

        let index = {
            //  Piv.OS size.
            let opposite_size = root_tripod.borrow(self.token).child_size(side, self.token);

            match side {
                Side::Left => self.index - 1 - opposite_size,
                Side::Right => self.index + 1 + opposite_size,
            }
        };

        self.retract_tripod(root_tripod);

        self.switch_tripod(Some(pivot_tripod), index);

        self.describe_self("rotate_child_from (end)");
    }

    //  Internal; prepare the side child for promotion to root.
    //
    //  The cursor is not pointing to any element, as the root_tripod is returned. The index is unmodified.
    //
    //  During the rotation, the pivot opposite side child is moved to be the side child of the root. If this child is
    //  deeper than its sibling, the result is not balanced:
    //
    //        Root                  Piv
    //         / \                 / \
    //        /   \               /   \
    //      Piv   X     =>       Y     Root
    //      / \                        / \
    //     Y   Piv.OS            Piv.OS   X
    //          \                    \
    //          A                    A
    //
    //  Hence, if necessary, a rotation must be performed to ensure that the pivot "side" child is the root of the
    //  deepest sub-tree prior to doing the main rotation.
    //
    //  Complexity: Time O(1), Space O(1).
    fn prepare_rotation(&mut self, side: Side, root_tripod: QuarterNodePtr<'brand, T>) -> QuarterNodePtr<'brand, T> {
        debug_assert!(self.node.is_none());

        self.describe_node("prepare_rotation (begin)", &root_tripod);

        let _original_index = self.index();
        let _original_address = &*root_tripod as *const _;

        let (pivot_selected, pivot_opposite) = {
            let pivot_node = root_tripod.borrow(self.token).child(side).expect("Pivot!");
            let selected = pivot_node.borrow(self.token).child_size(side, self.token);
            let opposite = pivot_node.borrow(self.token).child_size(side.opposite(), self.token);

            (selected, opposite)
        };

        if pivot_opposite >= 2 * pivot_selected {
            self.node = Some(root_tripod);

            //  Move to pivot.
            match side {
                Side::Left => self.move_left(),
                Side::Right => self.move_right(),
            }

            let pivot_tripod = self.node.take().expect("Pivot");

            self.rotate_child_from(side.opposite(), pivot_tripod);
            self.move_up();

            let root_tripod = self.node.take().expect("Root");

            debug_assert_eq!(_original_index, self.index());
            debug_assert_eq!(_original_address, &*root_tripod as *const _);

            self.describe_node("prepare_rotation (end) (modified)", &root_tripod);

            root_tripod
        } else {
            self.describe_node("prepare_rotation (end) (passthrough)", &root_tripod);

            root_tripod
        }
    }

    //  Internal; adjusts the size of the node by adding up the size of its children.
    //
    //  Complexity: Time O(1), Space O(1).
    fn adjust_size(&mut self, node: &GhostNode<'brand, T>) {
        let left_size = node.borrow(self.token).left_size(self.token);
        let right_size = node.borrow(self.token).right_size(self.token);

        node.borrow_mut(self.token).size = 1 + left_size + right_size;

        self.describe_node("adjust_size (adjusted)", node);
    }

    //  Internal; pops of the specified child, if any, adjusting size and pointers.
    //
    //  Complexity: Time O(1), Space O(1).
    fn take_child(side: Side, node: &GhostNode<'brand, T>, token: &mut GhostToken<'brand>) -> Option<QuarterNodePtr<'brand, T>> {
        let child = node.borrow_mut(token).take_child(side)?;

        let node_from_child = child.borrow_mut(token).up.take().expect("child.up == node");
        node.borrow_mut(token).set_child(side, node_from_child);

        let child_size = child.borrow(token).size;
        node.borrow_mut(token).size -= child_size;

        Some(child)
    }
}

//  Debugging code
#[allow(dead_code)]
impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    //  Internal; describe the node: sizes, parent and children, ...
    #[cfg(all(test, feature = "test-tree-debug"))]
    fn describe_node(&self, caller: &str, node: &GhostNode<'brand, T>) {
        let current_size = node.borrow(self.token).size;
        let left_size = node.borrow(self.token).left_size(self.token);
        let right_size = node.borrow(self.token).right_size(self.token);

        eprintln!(
            "{} - list: {}, index: {}, node: {:?} (size {}), up: {:?}, left: {:?} (size {}), right: {:?} (size {})",
            caller,
            self.len(),
            self.index,
            node as *const _, current_size,
            node.borrow(self.token).up.as_ref().map(|node| node as *const _),
            node.borrow(self.token).left().map(|node| node as *const _), left_size,
            node.borrow(self.token).right().map(|node| node as *const _), right_size
        );
    }

    //  Internal (dummy)
    #[cfg(not(all(test, feature = "test-tree-debug")))]
    fn describe_node(&self, _: &str, _: &GhostNode<'brand, T>) {}

    //  Internal; describe the cursor itself.
    #[cfg(all(test, feature = "test-tree-debug"))]
    fn describe_self(&self, caller: &str) {
        if let Some(node) = self.node.as_ref() {
            self.describe_node(caller, node);
        } else {
            eprintln!(
                "{} - list: {}, index: {}, current: None",
                caller,
                self.len(),
                self.index
            );
        };
    }

    #[cfg(not(all(test, feature = "test-tree-debug")))]
    fn describe_self(&self, _: &str) {}
}

impl<'a, 'brand, T> Drop for CursorMut<'a, 'brand, T> {
    fn drop(&mut self) {
        if let Some(tripod) = self.node.take() {
            super::retract(tripod, self.token);
        }
    }
}

#[cfg(test)]
mod tests {

use std::ops::Range;

use super::super::tests::*;
use super::*;

#[derive(Clone, Copy)]
struct Position<'a> {
    index: usize,
    start: usize,
    end: usize,
    current: &'a str,
    up: Option<&'a str>,
    left: Option<&'a str>,
    right: Option<&'a str>,
    prev: Option<&'a str>,
    next: Option<&'a str>,
}

impl<'a> Position<'a> {
    const fn new(
        index: usize,
        range: Range<usize>,
        current: &'a str,
        up: Option<&'a str>,
        left: Option<&'a str>,
        right: Option<&'a str>,
        prev: Option<&'a str>,
        next: Option<&'a str>
    )
        -> Self
    {
        let (start, end) = (range.start, range.end);

        Self { index, start, end, current, up, left, right, prev, next, }
    }

    const fn range(&self) -> Range<usize> { self.start..self.end }
}

#[track_caller]
fn assert_twilight(cursor: Cursor<'_, '_, String>) {
    assert_eq!(None, cursor.index());
    assert_eq!(0..0, cursor.range());
    assert_eq!(None, cursor.current());
}

#[track_caller]
fn assert_neighbours(parent: Option<&str>, left: Option<&str>, right: Option<&str>, cursor: Cursor<'_, '_, String>) {
    assert_eq!(parent, cursor.peek_up().map(String::as_str), "Parent");
    assert_eq!(left, cursor.peek_left().map(String::as_str), "Left Child");
    assert_eq!(right, cursor.peek_right().map(String::as_str), "Right Child");
}

#[track_caller]
fn assert_log_neighbours(prev: Option<&str>, next: Option<&str>, cursor: Cursor<'_, '_, String>) {
    assert_eq!(prev, cursor.peek_prev().map(String::as_str), "Prev");
    assert_eq!(next, cursor.peek_next().map(String::as_str), "Next");
}

#[track_caller]
fn assert_empty(cursor: Cursor<'_, '_, String>) {
    assert_twilight(cursor);
    assert_neighbours(None, None, None, cursor);
    assert_log_neighbours(None, None, cursor);
}

#[track_caller]
fn assert_current(at: usize, range: Range<usize>, element: &str, cursor: Cursor<'_, '_, String>) {
    assert_eq!(Some(at), cursor.index());
    assert_eq!(range, cursor.range());
    assert_eq!(Some(element), cursor.current().map(String::as_str), "Current");
}

#[track_caller]
fn assert_position(pos: Position<'_>, cursor: Cursor<'_, '_, String>) {
    assert_current(pos.index, pos.range(), pos.current, cursor);
    assert_neighbours(pos.up, pos.left, pos.right, cursor);
    assert_log_neighbours(pos.prev, pos.next, cursor);
}

#[track_caller]
fn assert_twilight_mut(cursor: &mut CursorMut<'_, '_, String>) {
    assert_eq!(None, cursor.index());
    assert_eq!(0..0, cursor.range());
    assert_eq!(None, cursor.current());
}

#[track_caller]
fn assert_neighbours_mut(parent: Option<&str>, left: Option<&str>, right: Option<&str>, cursor: &CursorMut<'_, '_, String>) {
    assert_eq!(parent, cursor.peek_up().map(|s| &**s), "Parent");
    assert_eq!(left, cursor.peek_left().map(|s| &**s), "Left Child");
    assert_eq!(right, cursor.peek_right().map(|s| &**s), "Right Child");
}

#[track_caller]
fn assert_log_neighbours_mut(prev: Option<&str>, next: Option<&str>, cursor: &CursorMut<'_, '_, String>) {
    assert_eq!(prev, cursor.peek_prev().map(|s| &**s), "Prev");
    assert_eq!(next, cursor.peek_next().map(|s| &**s), "Next");
}

#[track_caller]
fn assert_empty_mut(cursor: &mut CursorMut<'_, '_, String>) {
    assert_twilight_mut(cursor);
    assert_neighbours_mut(None, None, None, cursor);
    assert_log_neighbours_mut(None, None, cursor);
}

#[track_caller]
fn assert_current_mut(at: usize, range: Range<usize>, element: &str, cursor: &mut CursorMut<'_, '_, String>) {
    assert_eq!(Some(at), cursor.index());
    assert_eq!(range, cursor.range());
    assert_eq!(Some(element), cursor.current().map(|s| &**s), "Current");
}

#[track_caller]
fn assert_position_mut(pos: Position<'_>, cursor: &mut CursorMut<'_, '_, String>) {
    assert_current_mut(pos.index, pos.range(), pos.current, cursor);
    assert_neighbours_mut(pos.up, pos.left, pos.right, cursor);
    assert_log_neighbours_mut(pos.prev, pos.next, cursor);
}

//
//  Movement.
//

#[test]
fn cursor_empty() {
    with_tree(&[][..], |token, tree| {
        let mut cursor = tree.cursor(token);
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_up());
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_left());
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_right());
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_prev());
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_next());
        assert_empty(cursor);

        assert_eq!(None, cursor.try_move_to(0));
        assert_empty(cursor);

        cursor.move_up();
        assert_empty(cursor);

        cursor.move_left();
        assert_empty(cursor);

        cursor.move_right();
        assert_empty(cursor);

        cursor.move_prev();
        assert_empty(cursor);

        cursor.move_next();
        assert_empty(cursor);

        cursor.move_to(0);
        assert_empty(cursor);
    });
}

#[test]
fn cursor_mut_empty() {
    with_tree(&[][..], |token, tree| {
        let mut cursor = tree.cursor_mut(token);
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_up());
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_left());
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_right());
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_prev());
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_next());
        assert_empty_mut(&mut cursor);

        assert_eq!(None, cursor.try_move_to(0));
        assert_empty_mut(&mut cursor);

        cursor.move_up();
        assert_empty_mut(&mut cursor);

        cursor.move_left();
        assert_empty_mut(&mut cursor);

        cursor.move_right();
        assert_empty_mut(&mut cursor);

        cursor.move_prev();
        assert_empty_mut(&mut cursor);

        cursor.move_next();
        assert_empty_mut(&mut cursor);

        cursor.move_to(0);
        assert_empty_mut(&mut cursor);
    });
}

#[test]
fn cursor_brush_move_up_left_right() {
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor(token);

        assert_position(ROOT, cursor);

        cursor.move_up();
        assert_twilight(cursor);

        cursor.move_left();
        assert_position(ROOT, cursor);

        cursor.move_up();
        cursor.move_right();
        assert_position(ROOT, cursor);

        cursor.move_right();
        assert_position(RIGHT, cursor);

        cursor.move_up();
        cursor.move_left();
        assert_position(LEFT, cursor);

        cursor.move_right();
        assert_position(LR, cursor);

        cursor.move_right();
        assert_twilight(cursor);

        cursor.move_left();
        assert_position(ROOT, cursor);

        cursor.move_left();
        assert_position(LEFT, cursor);

        cursor.move_left();
        assert_twilight(cursor);
    });
}

#[test]
fn cursor_mut_brush_move_up_left_right() {
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        assert_position_mut(ROOT, &mut cursor);

        cursor.move_up();
        assert_twilight_mut(&mut cursor);

        cursor.move_left();
        assert_position_mut(ROOT, &mut cursor);

        cursor.move_up();
        cursor.move_right();
        assert_position_mut(ROOT, &mut cursor);

        cursor.move_right();
        assert_position_mut(RIGHT, &mut cursor);

        cursor.move_up();
        cursor.move_left();
        assert_position_mut(LEFT, &mut cursor);

        cursor.move_right();
        assert_position_mut(LR, &mut cursor);

        cursor.move_right();
        assert_twilight_mut(&mut cursor);

        cursor.move_left();
        assert_position_mut(ROOT, &mut cursor);

        cursor.move_left();
        assert_position_mut(LEFT, &mut cursor);

        cursor.move_left();
        assert_twilight_mut(&mut cursor);
    });
}

#[test]
fn cursor_brush_move_prev_next() {
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const RL: Position<'static> = Position::new(3, 3..4, "RL", Some("R"), None, None, Some("Root"), Some("R"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_front(token);

        for position in &[LEFT, LR, ROOT, RL, RIGHT] {
            assert_position(*position, cursor);

            cursor.move_next();
        }

        assert_twilight(cursor);

        for position in &[RIGHT, RL, ROOT, LR, LEFT] {
            cursor.move_prev();

            assert_position(*position, cursor);
        }

        cursor.move_prev();
        assert_twilight(cursor);

        cursor.move_next();
        assert_position(LEFT, cursor);

        cursor = tree.cursor_back(token);
        assert_position(RIGHT, cursor);
    });
}

#[test]
fn cursor_mut_brush_move_prev_next() {
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const RL: Position<'static> = Position::new(3, 3..4, "RL", Some("R"), None, None, Some("Root"), Some("R"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        {
            let mut cursor = tree.cursor_front_mut(token);

            for position in &[LEFT, LR, ROOT, RL, RIGHT] {
                assert_position_mut(*position, &mut cursor);

                cursor.move_next();
            }

            assert_twilight_mut(&mut cursor);

            for position in &[RIGHT, RL, ROOT, LR, LEFT] {
                cursor.move_prev();

                assert_position_mut(*position, &mut cursor);
            }

            cursor.move_prev();
            assert_twilight_mut(&mut cursor);

            cursor.move_next();
            assert_position_mut(LEFT, &mut cursor);
        }

        let mut cursor = tree.cursor_back_mut(token);
        assert_position_mut(RIGHT, &mut cursor);
    });
}

#[test]
fn cursor_brush_move_to() {
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const RL: Position<'static> = Position::new(3, 3..4, "RL", Some("R"), None, None, Some("Root"), Some("R"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);

    const POSITIONS: [Position<'static>; 5] = [LEFT, LR, ROOT, RL, RIGHT];

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor(token);

        for offset in 0..POSITIONS.len() {
            cursor.move_to(POSITIONS.len());

            assert_twilight(cursor);

            for base in &[1, 0, 2, 4, 3, 0, 2, 4, 1, 3, 2, 0, 3, 1, 4] {
                let index = (*base + offset) % POSITIONS.len();

                cursor.move_to(index);

                assert_position(POSITIONS[index], cursor);
            }
        }
    });
}

#[test]
fn cursor_mut_brush_move_to() {
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const RL: Position<'static> = Position::new(3, 3..4, "RL", Some("R"), None, None, Some("Root"), Some("R"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);

    const POSITIONS: [Position<'static>; 5] = [LEFT, LR, ROOT, RL, RIGHT];

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        for offset in 0..POSITIONS.len() {
            cursor.move_to(POSITIONS.len());

            assert_twilight_mut(&mut cursor);

            for base in &[1, 0, 2, 4, 3, 0, 2, 4, 1, 3, 2, 0, 3, 1, 4] {
                let index = (*base + offset) % POSITIONS.len();

                cursor.move_to(index);

                assert_position_mut(POSITIONS[index], &mut cursor);
            }
        }
    });
}

#[test]
fn cursor_mut_move_to_self() {
    const LEFT: Position<'static> = Position::new(0, 0..2, "L", Some("Root"), None, Some("LR"), None, Some("LR"));
    const LR: Position<'static> = Position::new(1, 1..2, "LR", Some("L"), None, None, Some("L"), Some("Root"));
    const ROOT: Position<'static> = Position::new(2, 0..5, "Root", None, Some("L"), Some("R"), Some("LR"), Some("RL"));
    const RL: Position<'static> = Position::new(3, 3..4, "RL", Some("R"), None, None, Some("Root"), Some("R"));
    const RIGHT: Position<'static> = Position::new(4, 3..5, "R", Some("Root"), Some("RL"), None, Some("RL"), None);

    const POSITIONS: [Position<'static>; 5] = [LEFT, LR, ROOT, RL, RIGHT];

    //  Move to self.
    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        for index in 0..POSITIONS.len() {
            cursor.move_to(index);
            assert_position_mut(POSITIONS[index], &mut cursor);

            cursor.move_to(index);
            assert_position_mut(POSITIONS[index], &mut cursor);
        }

        cursor.move_to(POSITIONS.len());
        assert_twilight_mut(&mut cursor);

        cursor.move_to(POSITIONS.len());
        assert_twilight_mut(&mut cursor);
    });
}

//
//  Editions
//

#[test]
fn cursor_mut_remove_current_twilight() {
    with_tree(&[], |token, tree| {
        let mut cursor = tree.cursor_mut(token);
        assert_twilight_mut(&mut cursor);

        let removed = cursor.remove_current();

        assert_twilight_mut(&mut cursor);
        assert_eq!(None, removed);
    });

    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_mut(token);
        cursor.move_up();
        assert_twilight_mut(&mut cursor);

        let removed = cursor.remove_current();

        assert_eq!(None, removed);
        assert_twilight_mut(&mut cursor);

        assert_tree(&["Root", "L", "R", "-", "LR", "RL"], cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_remove_current_root() {
    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        {
            const POS: Position<'static> = Position::new(2, 0..4, "R", None, Some("L"), Some("RL"), Some("LR"), Some("RL"));

            eprintln!("===== Remove Root =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("Root".to_string()), removed);
            assert_tree(&["R", "L", "RL", "-", "LR"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(2, 2..3, "RL", Some("L"), None, None, Some("L"), None);

            eprintln!("===== Remove R =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("R".to_string()), removed);
            assert_tree(&["L", "LR", "RL"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(1, 0..2, "RL", None, Some("LR"), None, Some("LR"), None);

            eprintln!("===== Remove L =====");

            cursor.move_up();

            let removed = cursor.remove_current();

            assert_eq!(Some("L".to_string()), removed);
            assert_tree(&["RL", "LR"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            eprintln!("===== Remove RL =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("RL".to_string()), removed);
            assert_tree(&["LR"], cursor.as_cursor());
            assert_twilight(cursor.as_cursor());
        }

        {
            eprintln!("===== Remove LR =====");

            cursor.move_left();

            let removed = cursor.remove_current();

            assert_eq!(Some("LR".to_string()), removed);
            assert_tree(&[], cursor.as_cursor());
            assert_twilight(cursor.as_cursor());
        }
    });
}

#[test]
fn cursor_mut_remove_current_front_to_back() {
    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_front_mut(token);

        {
            const POS: Position<'static> = Position::new(0, 0..1, "LR", Some("Root"), None, None, None, Some("Root"));

            eprintln!("===== Remove L =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("L".to_string()), removed);
            assert_tree(&["Root", "LR", "R", "-", "-", "RL"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(0, 0..1, "Root", Some("RL"), None, None, None, Some("RL"));

            eprintln!("===== Remove LR =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("LR".to_string()), removed);
            assert_tree(&["RL", "Root", "R"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(0, 0..2, "RL", None, None, Some("R"), None, Some("R"));

            eprintln!("===== Remove Root =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("Root".to_string()), removed);
            assert_tree(&["RL", "-", "R"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(0, 0..1, "R", None, None, None, None, None);

            eprintln!("===== Remove RL =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("RL".to_string()), removed);
            assert_tree(&["R"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            eprintln!("===== Remove R =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("R".to_string()), removed);
            assert_tree(&[], cursor.as_cursor());
            assert_twilight(cursor.as_cursor());
        }
    });
}

#[test]
fn cursor_mut_remove_current_back_to_front() {
    with_tree(&["Root", "L", "R", "", "LR", "RL"], |token, tree| {
        let mut cursor = tree.cursor_back_mut(token);

        {
            const POS: Position<'static> = Position::new(3, 3..4, "RL", Some("Root"), None, None, Some("Root"), None);

            eprintln!("===== Remove R =====");

            let removed = cursor.remove_current();
            cursor.move_to_back();

            assert_eq!(Some("R".to_string()), removed);
            assert_tree(&["Root", "L", "RL", "-", "LR"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(2, 2..3, "Root", Some("LR"), None, None, Some("LR"), None);

            eprintln!("===== Remove RL =====");

            let removed = cursor.remove_current();
            cursor.move_to_back();

            assert_eq!(Some("RL".to_string()), removed);
            assert_tree(&["LR", "L", "Root"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(1, 0..2, "LR", None, Some("L"), None, Some("L"), None);

            eprintln!("===== Remove Root =====");

            let removed = cursor.remove_current();
            cursor.move_to_back();

            assert_eq!(Some("Root".to_string()), removed);
            assert_tree(&["LR", "L"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            const POS: Position<'static> = Position::new(0, 0..1, "L", None, None, None, None, None);

            eprintln!("===== Remove LR =====");

            let removed = cursor.remove_current();
            cursor.move_to_back();

            assert_eq!(Some("LR".to_string()), removed);
            assert_tree(&["L"], cursor.as_cursor());
            assert_position(POS, cursor.as_cursor());
        }

        {
            eprintln!("===== Remove L =====");

            let removed = cursor.remove_current();

            assert_eq!(Some("L".to_string()), removed);
            assert_tree(&[], cursor.as_cursor());
            assert_twilight(cursor.as_cursor());
        }
    });
}

#[test]
fn cursor_mut_insert_after_from_twilight() {
    const TREES: &[&[&str]] = &[
        &["9"],
        &["9", "8"],
        &["8", "7", "9"],
        &["8", "7", "9", "6"],
        &["8", "6", "9", "5", "7"],
        &["6", "5", "8", "4", "-", "7", "9"],
        &["6", "4", "8", "3", "5", "7", "9"],
        &["6", "4", "8", "3", "5", "7", "9", "2"],
        &["6", "4", "8", "2", "5", "7", "9", "1", "3"],
        &["6", "2", "8", "1", "4", "7", "9", "0", "-", "3", "5"]
    ];

    with_tree(&[], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        for (i, tree) in TREES.iter().enumerate() {
            let element = TREES.len() - i - 1;

            eprintln!("===== Insert {} =====", element);

            cursor.insert_after(element.to_string());

            assert_tree(tree, cursor.as_cursor());
        }
    });
}

#[test]
fn cursor_mut_insert_before_from_twilight() {
    const TREES: &[&[&str]] = &[
        &["0"],
        &["0", "-", "1"],
        &["1", "0", "2"],
        &["1", "0", "2", "-", "-", "-", "3"],
        &["1", "0", "3", "-", "-", "2", "4"],
        &["3", "1", "4", "0", "2", "-", "5"],
        &["3", "1", "5", "0", "2", "4", "6"],
        &["3", "1", "5", "0", "2", "4", "6", "-", "-", "-", "-", "-", "-", "-", "7"],
        &["3", "1", "5", "0", "2", "4", "7", "-", "-", "-", "-", "-", "-", "6", "8"],
        &["3", "1", "7", "0", "2", "5", "8", "-", "-", "-", "-", "4", "6", "-", "9"]
    ];

    with_tree(&[], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        for (i, tree) in TREES.iter().enumerate() {
            eprintln!("===== Insert {} =====", i);

            cursor.insert_before(i.to_string());

            assert_tree(tree, cursor.as_cursor());
        }
    });
}

#[test]
fn cursor_mut_insert_as_leaf() {
    //  1 2 3 4 5 6 7 8 9 A B C D E F
    //                8
    //        4               C
    //    2       6       A       E
    //  1   3   5   7   9   B   D   F

    with_tree(&[], |token, tree| {
        let mut cursor = tree.cursor_mut(token);

        eprintln!("===== Insert 8 =====");

        cursor.insert_after("8".to_string());

        assert_tree(&["8"], cursor.as_cursor());

        eprintln!("===== Insert 4 & C =====");

        cursor.move_to_root();
        cursor.insert_before("4".to_string());
        cursor.insert_after("C".to_string());

        assert_tree(&["8", "4", "C"], cursor.as_cursor());

        eprintln!("===== Insert 2 & 6 =====");

        cursor.move_left();
        cursor.insert_before("2".to_string());
        cursor.insert_after("6".to_string());

        assert_tree(&["8", "4", "C", "2", "6"], cursor.as_cursor());

        eprintln!("===== Insert A & E =====");

        cursor.move_to_root();
        cursor.move_right();
        cursor.insert_before("A".to_string());
        cursor.insert_after("E".to_string());

        assert_tree(&["8", "4", "C", "2", "6", "A", "E"], cursor.as_cursor());

        eprintln!("===== Insert 1 & 3 =====");

        cursor.move_to_root();
        cursor.move_left();
        cursor.move_left();
        cursor.insert_before("1".to_string());
        cursor.insert_after("3".to_string());

        assert_tree(&["8", "4", "C", "2", "6", "A", "E", "1", "3"], cursor.as_cursor());

        eprintln!("===== Insert 5 & 7 =====");

        cursor.move_to_root();
        cursor.move_left();
        cursor.move_right();
        cursor.insert_before("5".to_string());
        cursor.insert_after("7".to_string());

        assert_tree(&["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7"], cursor.as_cursor());

        eprintln!("===== Insert 9 & B =====");

        cursor.move_to_root();
        cursor.move_right();
        cursor.move_left();
        cursor.insert_before("9".to_string());
        cursor.insert_after("B".to_string());

        assert_tree(&["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B"], cursor.as_cursor());

        eprintln!("===== Insert D & F =====");

        cursor.move_to_root();
        cursor.move_right();
        cursor.move_right();
        cursor.insert_before("D".to_string());
        cursor.insert_after("F".to_string());

        assert_tree(&["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"], cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_splice_empty() {
    const HEX: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];

    with_tree_duo(&[], &[], |token, tree, splice| {
        eprintln!("===== Splice After Empty in Empty =====");

        {
            let mut cursor = tree.cursor_mut(token);

            cursor.splice_after(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(&[], cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(&[], &[], |token, tree, splice| {
        eprintln!("===== Splice Before Empty in Empty =====");

        {
            let mut cursor = tree.cursor_mut(token);

            cursor.splice_before(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(&[], cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(&[], HEX, |token, tree, splice| {
        eprintln!("===== Splice After HEX in Empty =====");

        {
            let mut cursor = tree.cursor_mut(token);

            cursor.splice_after(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(HEX, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(&[], HEX, |token, tree, splice| {
        eprintln!("===== Splice Before HEX in Empty =====");

        {
            let mut cursor = tree.cursor_mut(token);

            cursor.splice_before(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(HEX, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });
}

#[test]
fn cursor_mut_splice_twilight() {
    const HEX: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];
    const FIRST_HALF_HEX: &[&str] = &["4", "2", "6", "1", "3", "5", "7"];
    const SECOND_HALF_HEX: &[&str] = &["C", "9", "E", "8", "A", "D", "F", "-", "-", "B"];

    with_tree_duo(HEX, &[], |token, tree, splice| {
        eprintln!("===== Splice After Empty in HEX =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            cursor.splice_after(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(HEX, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(HEX, &[], |token, tree, splice| {
        eprintln!("===== Splice Before Empty in HEX =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            cursor.splice_before(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(HEX, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(SECOND_HALF_HEX, FIRST_HALF_HEX, |token, tree, splice| {
        //                 9
        //         4               C
        //     2        6      A       E
        //   1   3   5   8   B   -   D   F
        //  - - - - - - 7 - - - - - - - - -
        const RESULT: &[&str] = &["9", "4", "C", "2", "6", "A", "E", "1", "3", "5", "8", "B", "-", "D", "F", "-", "-", "-", "-", "-", "-", "7"];

        eprintln!("===== Splice After First in Second =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            cursor.splice_after(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(RESULT, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });

    with_tree_duo(FIRST_HALF_HEX, SECOND_HALF_HEX, |token, tree, splice| {
        //                 9
        //         4               C
        //     2       6       A       E
        //   1   3   5   7   B   -   D   F
        //  - - - - - - - 8 - - - - - - - -
        const RESULT: &[&str] = &["9", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "B", "-", "D", "F", "-", "-", "-", "-", "-", "-", "-", "8"];

        eprintln!("===== Splice Before Second in First =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            cursor.splice_before(splice);

            assert_twilight(cursor.as_cursor());
            assert_tree(RESULT, cursor.as_cursor());
        }

        assert_tree(&[], splice.cursor(token));
    });
}

#[test]
fn cursor_mut_splice_after() {
    const ORIGINAL: &[&str] = &["D", "B", "F", "A", "C", "E", "G"];
    const SPLICE: &[&str] = &["4", "2", "6", "1", "3", "5", "7"];

    const RESULTS: &[&[&str]] = &[
        //                 4
        //         2               D
        //     A       3       B       F
        //   -   1   -   -   6   C   E   G
        //  - - - - - - - - 5 7 - - - - - -
        &["4", "2", "D", "A", "3", "B", "F", "-", "1", "-", "-", "6", "C", "E", "G", "-", "-", "-", "-", "-", "-", "-", "-", "5", "7"],
        //                 4
        //         B               D
        //     A       2       6       F
        //   -   -   1   3   5   C   E   G
        //  - - - - - - - - - - 7 - - - - -
        &["4", "B", "D", "A", "2", "6", "F", "-", "-", "1", "3", "5", "C", "E", "G", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "7"],
        //         4
        //     C       D
        //   B   2   6   F
        //  A - 1 3 5 7 E G
        &["4", "C", "D", "B", "2", "6", "F", "A", "-", "1", "3", "5", "7", "E", "G"],
        //         4
        //     D       E
        //   B   2   6   F
        //  A C 1 3 5 7 - G
        &["4", "D", "E", "B", "2", "6", "F", "A", "C", "1", "3", "5", "7", "-", "G"],
        //                 4
        //         D               F
        //     B       2       6       G
        //   A   C   E   3   5   7   -   -
        //  - - - - - 1 - - - - - - - - - -
        &["4", "D", "F", "B", "2", "6", "G", "A", "C", "E", "3", "5", "7", "-", "-", "-", "-", "-", "-", "-", "1"],
        //                 4
        //         D               6
        //     B       F       5       G
        //   A   C   E   2   -   -   7   -
        //  - - - - - - 1 3 - - - - - - - -
        &["4", "D", "6", "B", "F", "5", "G", "A", "C", "E", "2", "-", "-", "7", "-", "-", "-", "-", "-", "-", "-", "1", "3"],
        //         G
        //     D       4
        //   B   F   2   6
        //  A C E - 1 3 5 7
        &["G", "D", "4", "B", "F", "2", "6", "A", "C", "E", "-", "1", "3", "5", "7"],
    ];

    for index in 0..ORIGINAL.len() {
        eprintln!("===== Splice After {} =====", index);

        with_tree_duo(ORIGINAL, SPLICE, |token, tree, splice| {
            {
                let mut cursor = tree.cursor_mut(token);
                cursor.move_to(index);

                cursor.splice_after(splice);

                assert_eq!(Some(index), cursor.index());
                assert_tree(&RESULTS[index], cursor.as_cursor());
            }

            assert_tree(&[], splice.cursor(token));
        });
    }
}

#[test]
fn cursor_mut_splice_before() {
    const ORIGINAL: &[&str] = &["D", "B", "F", "A", "C", "E", "G"];
    const SPLICE: &[&str] = &["4", "2", "6", "1", "3", "5", "7"];

    const RESULTS: &[&[&str]] = &[
        //         A
        //     4       D
        //   2   6   B   F
        //  1 3 5 7 - C E G
        &["A", "4", "D", "2", "6", "B", "F", "1", "3", "5", "7", "-", "C", "E", "G"],
        //                 4
        //         2               D
        //     A       3       B       F
        //   -   1   -   -   6   C   E   G
        //  - - - - - - - - 5 7 - - - - - -
        &["4", "2", "D", "A", "3", "B", "F", "-", "1", "-", "-", "6", "C", "E", "G", "-", "-", "-", "-", "-", "-", "-", "-", "5", "7"],
        //                 4
        //         B               D
        //     A       2       6       F
        //   -   -   1   3   5   C   E   G
        //  - - - - - - - - - - 7 - - - - -
        &["4", "B", "D", "A", "2", "6", "F", "-", "-", "1", "3", "5", "C", "E", "G", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "7"],
        //         4
        //     C       D
        //   B   2   6   F
        //  A - 1 3 5 7 E G
        &["4", "C", "D", "B", "2", "6", "F", "A", "-", "1", "3", "5", "7", "E", "G"],
        //         4
        //     D       E
        //   B   2   6   F
        //  A C 1 3 5 7 - G
        &["4", "D", "E", "B", "2", "6", "F", "A", "C", "1", "3", "5", "7", "-", "G"],
        //                 4
        //         D               F
        //     B       2       6       G
        //   A   C   E   3   5   7   -   -
        //  - - - - - 1 - - - - - - - - - -
        &["4", "D", "F", "B", "2", "6", "G", "A", "C", "E", "3", "5", "7", "-", "-", "-", "-", "-", "-", "-", "1"],
        //                 4
        //         D               6
        //     B       F       5       G
        //   A   C   E   2   -   -   7   -
        //  - - - - - 1 3 - - - - - - - - -
        &["4", "D", "6", "B", "F", "5", "G", "A", "C", "E", "2", "-", "-", "7", "-", "-", "-", "-", "-", "-", "-", "1", "3"],
    ];

    for index in 0..ORIGINAL.len() {
        eprintln!("===== Splice Before {} =====", index);

        with_tree_duo(ORIGINAL, SPLICE, |token, tree, splice| {
            {
                let mut cursor = tree.cursor_mut(token);
                cursor.move_to(index);

                cursor.splice_before(splice);

                assert_eq!(Some(index + SPLICE.len()), cursor.index());
                assert_tree(&RESULTS[index], cursor.as_cursor());
            }

            assert_tree(&[], splice.cursor(token));
        });
    }
}

#[test]
fn cursor_mut_split_twilight() {
    const ORIGINAL: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];

    with_tree_duo(ORIGINAL, &[], |token, tree, split| {
        eprintln!("===== Split After =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            *split = cursor.split_after();

            assert_twilight(cursor.as_cursor());
            assert_tree(&[], cursor.as_cursor());
        }

        assert_tree(ORIGINAL, split.cursor(token));
    });

    with_tree_duo(ORIGINAL, &[], |token, tree, split| {
        eprintln!("===== Split Before =====");

        {
            let mut cursor = tree.cursor_mut(token);
            cursor.move_up();

            *split = cursor.split_before();

            assert_twilight(cursor.as_cursor());
            assert_tree(&[], cursor.as_cursor());
        }

        assert_tree(ORIGINAL, split.cursor(token));
    });
}

#[test]
fn cursor_mut_split_after() {
    const ORIGINAL: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];

    const SPLITS: &[(&[&str], &[&str])] = &[
        (&["1"], &["8", "4", "C", "2", "6", "A", "E", "-", "3", "5", "7", "9", "B", "D", "F"]),
        (&["2", "1"], &["8", "4", "C", "3", "6", "A", "E", "-", "-", "5", "7", "9", "B", "D", "F"]),
        (&["2", "1", "3"], &["8", "6", "C", "4", "7", "A", "E", "-", "5", "-", "-", "9", "B", "D", "F"]),
        (&["2", "1", "4", "-", "-", "3"], &["8", "6", "C", "5", "7", "A", "E", "-", "-", "-", "-", "9", "B", "D", "F"]),
        (&["4", "2", "5", "1", "3"], &["C", "8", "E", "6", "A", "D", "F", "-", "7", "9", "B"]),
        (&["4", "2", "6", "1", "3", "5"], &["C", "8", "E", "7", "A", "D", "F", "-", "-", "9", "B"]),
        (&["4", "2", "6", "1", "3", "5", "7"], &["C", "8", "E", "-", "A", "D", "F", "-", "-", "9", "B"]),
        (&["4", "2", "8", "1", "3", "6", "-", "-", "-", "-", "-", "5", "7"], &["C", "A", "E", "9", "B", "D", "F"]),
        (&["4", "2", "8", "1", "3", "6", "9", "-", "-", "-", "-", "5", "7"], &["C", "A", "E", "-", "B", "D", "F"]),
        (&["4", "2", "8", "1", "3", "6", "A", "-", "-", "-", "-", "5", "7", "9"], &["C", "B", "E", "-", "-", "D", "F"]),
        (&["8", "4", "A", "2", "6", "9", "B", "1", "3", "5", "7"], &["E", "C", "F", "-", "D"]),
        (&["8", "4", "A", "2", "6", "9", "C", "1", "3", "5", "7", "-", "-", "B"], &["E", "D", "F"]),
        (&["8", "4", "C", "2", "6", "A", "D", "1", "3", "5", "7", "9", "B"], &["E", "-", "F"]),
        (&["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D"], &["F"]),
        (ORIGINAL, &[]),
    ];

    for (index, (remainder, castaway)) in SPLITS.iter().enumerate() {
        eprintln!("===== Split After {} =====", index);

        with_tree_duo(ORIGINAL, &[], |token, tree, split| {
            {
                let mut cursor = tree.cursor_mut(token);
                cursor.move_to(index);

                *split = cursor.split_after();

                assert_eq!(Some(index), cursor.index());
                assert_tree(remainder, cursor.as_cursor());
            }

            assert_tree(castaway, split.cursor(token));
        });
    }
}

#[test]
fn cursor_mut_split_before() {
    const ORIGINAL: &[&str] = &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D", "F"];

    const SPLITS: &[(&[&str], &[&str])] = &[
        (ORIGINAL, &[]),
        (&["8", "4", "C", "2", "6", "A", "E", "-", "3", "5", "7", "9", "B", "D", "F"], &["1"]),
        (&["8", "4", "C", "3", "6", "A", "E", "-", "-", "5", "7", "9", "B", "D", "F"], &["2", "1"]),
        (&["8", "6", "C", "4", "7", "A", "E", "-", "5", "-", "-", "9", "B", "D", "F"], &["2", "1", "3"]),
        (&["8", "6", "C", "5", "7", "A", "E", "-", "-", "-", "-", "9", "B", "D", "F"], &["2", "1", "4", "-", "-", "3"]),
        (&["C", "8", "E", "6", "A", "D", "F", "-", "7", "9", "B"], &["4", "2", "5", "1", "3"]),
        (&["C", "8", "E", "7", "A", "D", "F", "-", "-", "9", "B"], &["4", "2", "6", "1", "3", "5"]),
        (&["C", "8", "E", "-", "A", "D", "F", "-", "-", "9", "B"], &["4", "2", "6", "1", "3", "5", "7"]),
        (&["C", "A", "E", "9", "B", "D", "F"], &["4", "2", "8", "1", "3", "6", "-", "-", "-", "-", "-", "5", "7"]),
        (&["C", "A", "E", "-", "B", "D", "F"], &["4", "2", "8", "1", "3", "6", "9", "-", "-", "-", "-", "5", "7"]),
        (&["C", "B", "E", "-", "-", "D", "F"], &["4", "2", "8", "1", "3", "6", "A", "-", "-", "-", "-", "5", "7", "9"]),
        (&["E", "C", "F", "-", "D"], &["8", "4", "A", "2", "6", "9", "B", "1", "3", "5", "7"]),
        (&["E", "D", "F"], &["8", "4", "A", "2", "6", "9", "C", "1", "3", "5", "7", "-", "-", "B"]),
        (&["E", "-", "F"], &["8", "4", "C", "2", "6", "A", "D", "1", "3", "5", "7", "9", "B"]),
        (&["F"], &["8", "4", "C", "2", "6", "A", "E", "1", "3", "5", "7", "9", "B", "D"]),
    ];

    for (index, (remainder, castaway)) in SPLITS.iter().enumerate() {
        eprintln!("===== Split Before {} =====", index);

        with_tree_duo(ORIGINAL, &[], |token, tree, split| {
            {
                let mut cursor = tree.cursor_mut(token);
                cursor.move_to(index);

                *split = cursor.split_before();

                assert_eq!(Some(0), cursor.index());
                assert_tree(remainder, cursor.as_cursor());
            }

            assert_tree(castaway, split.cursor(token));
        });
    }
}

} // mod tests
