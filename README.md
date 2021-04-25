An attempt at improving the ergonomics of the `GhostCell`.

#   Could it be more ergonomic?

The idea behind `GhostSea`:

-   Wrap an _un-branded_ (`'static`) version of the type.
-   When the user wishes to access the data:
    -   Create a `GhostToken` on the fly.
    -   _Brand_ the un-branded type to match, via a simple (if `unsafe`) projection trait.
    -   Call a user-supplied action with _newly-branded_ type and matching `GhostToken`.

This works to a degree: in the `examples/linked_list` folder one can see a `GhostLinkedList<'brand, T>` used as the
basis for a `LinkedList<T>`. A single of `unsafe` code to implement `GhostProject` and here you go.

There's a **catch**, though: references to the insides of `GhostLinkedList` (nodes, or elements) are prevented by the
borrow-checker from leaking through the interface of `LinkedList` -- because the borrow is bounded to the lifetime of
the token, which is ephemeral.


#   That's all folks!

And thanks for reading.
