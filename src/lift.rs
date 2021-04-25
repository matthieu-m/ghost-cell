use core::mem;

/// Lifts `root` into the slot provided by `fun`; returns the previous value of the slot, if any.
///
/// This function is useful, for example, to "tie the knot" when appending 2 linked-lists: it is easy to splice the
/// the head of the back linked-list at the back of the front linked-list, but then one has lost the head pointer
/// and can no longer splice the tail of the front linked-list to it.
///
/// #   Experimental
///
/// This function is highly experimental, see the ongoing discussion at
/// https://users.rust-lang.org/t/can-you-break-the-lift/58858.
pub fn lift<F, R>(root: R, fun: F) -> R
where
    F: for<'a> FnOnce(&'a R) -> &'a mut R,
{
    let slot = fun(&root) as *mut R;

    debug_assert_ne!(slot as *const _, &root as *const _);

    //  Safety:
    //  -   `root` is still alive, hence any reference linked to `root` is _also_ alive.
    //  -   `slot` is necessarily different from `root`, being mutable.
    mem::replace(unsafe { &mut *slot }, root)
}

/// Lifts `root` into the slot provided by `fun`; returns the previous value of the slot, if any.
///
/// #   Note
///
/// This function is similar to `lift`. The `extra` argument is required to work-around `for<'a>` not otherwise
/// appropriately constraining its range of lifetime.
pub fn lift_with<F, E, R>(root: R, extra: &E, fun: F) -> R
where
    F: for<'a> FnOnce(&'a R, &'a E) -> &'a mut R,
{
    let slot = fun(&root, extra) as *mut R;

    debug_assert_ne!(slot as *const _, &root as *const _);

    //  Safety:
    //  -   `root` is still alive, hence any reference linked to `root` is _also_ alive.
    //  -   `slot` is necessarily different from `root`, being mutable.
    mem::replace(unsafe { &mut *slot }, root)
}

/// Lifts `root` into the slot provided by `fun`; returns the previous value of the slot, if any.
///
/// #   Note
///
/// This function is similar to `lift`. The `extra` argument is required to work-around `for<'a>` not otherwise
/// appropriately constraining its range of lifetime.
pub fn lift_with_mut<F, E, R>(root: R, extra: &mut E, fun: F) -> R
where
    F: for<'a> FnOnce(&'a R, &'a mut E) -> &'a mut R,
{
    let slot = fun(&root, extra) as *mut R;

    debug_assert_ne!(slot as *const _, &root as *const _);

    //  Safety:
    //  -   `root` is still alive, hence any reference linked to `root` is _also_ alive.
    //  -   `slot` is necessarily different from `root`, being mutable.
    mem::replace(unsafe { &mut *slot }, root)
}
