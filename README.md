A proof of concept implementation of cyclic data structures in stable, safe, Rust.

This demonstrates the combined power of the [static-rc](https://github.com/matthieu-m/static-rc) crate and the
[ghost-cell](https://github.com/matthieu-m/ghost-cell) crate.


#   Motivation

##  Why the focus on safety?

A simple combination of 2 facts about data structures:

-   They are pervasive and often used to store user-controlled input.
-   They are extremely error-prone, juggling lifetime and aliasing concerns at the same time.

The combination of this two factors means that a single logical bug can result in Undefined Behavior, opening up the
door to a multitude of attacks.


##  How can you write safe cyclic data structures?

There are typically two obstacles, as mentioned: lifetime, and aliasing.

The state of the art recommendation today is one of:

-   A `Vec` with indices instead of pointers.
-   An arena to handle lifetime, and some form of cell to handle aliasing.
-   `Rc` + `RefCell`.


##  What's wrong with those approaches?

`Vec` based solutions will blow up the algorithmic complexity of splice/split operations. In a linked list, splicing in
another list, or splitting a part of the list, are both O(1) operations, but transferring N elements from one `Vec` to
another is at least an O(N) operation.

Arena based solution will allow implementing all operations with their expected algorithmic complexity, but this comes at
the cost of never being able to reclaim memory from the arena as long as a single data structure exists which references
the arena.

Finally `Rc` + `RefCell` suffer from increased memory consumption and runtime overhead:

-   `Rc` typically embeds 2 `usize` counters: the strong and weak count.
    -   An `Rc` implementation optimized for data structures could ditch the weak count.
-   `RefCell` typically embeds an `isize` counter: to count the number of readers and writers.


#   Does ghost-collections offer a better alternative then?

Maybe.


##  Lighter-weight building bricks

This crate aims at refining the `Rc` + `RefCell` solution by substituting both of them with `StaticRc` and `GhostCell`
respectively:

-   `GhostCell` is a compile-time cell, splitting the aliasing compile-time checks to the zero-sized `GhostToken`.
-   `StaticRc` is a compile-time reference counted pointer, so is _mostly_ free at run-time.
    -   One exception: joining 2 `StaticRc` requires checking that they both refer to the same allocation.

On the face of it, this seems fairly interesting:

-   No memory overhead.
-   No run-time overhead.


##  And a catch.

There's a catch, though.

`GhostCell` is a straightforward replacement, `StaticRc` is a _bit_ more complicated. Typical implementations based on
`Rc` will clone it whenever necessary -- but cloning a `StaticRc` is impossible.

If you have split your `StaticRc` in halves, that is, you have 2 instances of `StaticRc<T, 1, 2>`, then you only have
those two instances. You can split one, but it changes its type. This makes _temporarily_ holding onto one more
instance of a reference-counted pointer... impossible. There's no temporary instance.

To solve this problem, the nodes of the `TripodList` and `TripodTree` contain one extra instance of a pointer, compared
to the typical implementation. That is, a node from a `TripodList` contains 3 pointers, and one from a `TripodTree`
contains 4 pointers.

That's the same memory overhead as a special-purpose `Rc` with no weak count. And mostly the same run-time overhead too
as deploying the _tripod_ pointer is a memory write, just as cloning a `Rc`, and retracting the _tripod_ pointer is
another memory write, just as destroying a `Rc`. It may be slightly more efficient, and linear logic keeps one honest...

It _may_ be possible to avoid this overhead altogether. `LinkedList` avoids it... and uses the experimental
`GhostCursor` instead. It's not clear whether `GhostCursor` is _quite_ sufficient to implement all the functionality of
a list, though. And then there's the _experimental_ issue...


##  At least it's safe, no?

Mostly?

The core functionality of `GhostCell` and `StaticRc` are really strong contenders:

-   `GhostCell` (the paper) was developed by Ralf Jung and co, and proven safe. The implementation hopefully is also
    safe.
-   `StaticRc` is really basic reference-counting, just at compile-time.

The core functionality, though, is also _slightly_ insufficient. This forces this crate to use extra, experimental
functionality from its 2 core crates, and those are much less proven:

-   `static_rc::lift*` is at the core of this crate. None of the collections are too useful without it. Its core idea
    _looks_ sound (scary eh?), though even if it is, the implementation may not be...
-   `GhostCursor` is even more sketchy, safety-wise. If safe, it may allow writing the collections without an extra
    _tripod_ pointer... May.


#   Is ghost-collections really helpful then?

**Yes**.


##  GhostCell is practical.

At the very least, this crate is a proof-of-concept that `GhostCell` is _really_ usable.

To the best of our knowledge, this is the first crate making extensive use of `GhostCell`, and there were some questions
as to whether it was possible to express algorithms with `GhostCell`. Having implemented a complete linked list and
binary tree around `GhostCell` I can confirm that it is **practical** enough.

Replacing `RefCell` by `GhostCell` means avoiding both the memory and run-time overhead of `RefCell`. That's a
significant advantage.

There are some ergonomic downsides, though:

-   Using lifetime as a brand means that all the entire program needs to be wrapped within a closure.
-   Having to pass the extra `GhostToken` everywhere means that many traits -- such as `Debug` -- cannot be implemented
    on the collections.

Those were all foreseen, so no surprise there, but of course it's still annoying.


##  StaticRc is practical.

This crate also proves that `StaticRc` works, although it is perhaps not the best tool for cyclic data structures.


##  Test bed.

Finally, this crate provides a test bed for both of the above.

After putting them through their paces, I am happy to report that MIRI finds no issue when running the full test-suite.


#   That's all folks!

And thanks for reading.
