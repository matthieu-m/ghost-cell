`StaticRc` is a safe reference-counted pointer, similar to `Rc` or `Arc`, though performing its reference-counting at
compile-time rather than run-time, and therefore avoiding any run-time overhead.

#   Motivating Example

A number of collections, such as linked-lists, binary-trees, or B-Trees are most easily implemented with aliasing
pointers.

Traditionally, this requires either `unsafe` raw pointers, or using `Rc` or `Arc` depending on the scenario. A key
observation, however, is that in those collections the exact number of aliases is known at compile-time:

-   A doubly linked-list has 2 pointers to each node.
-   A binary-tree has 3 pointers to each node: one from the parent, and one from each child.
-   A B-Tree of cardinality N has N+1 pointers to each node.

In this type of scenario, `static-rc` offers the safety of `Rc` and `Arc`, with the performance of `unsafe` raw
pointers.


#   That's all folks!

And thanks for reading.
