use core::cell::Cell;
use ghost_cell::{GhostCell, GhostCursor, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let cell = GhostCell::new(1);
        let leak = Cell::new(None);
        let mut cursor = GhostCursor::new(&mut token, Some(&cell));

        let _ = cursor.move_mut(|cell_ref| {
            leak.set(Some(cell_ref));
            None
        });

        //  If `cell_ref` escaped, this would be a shared reference whose value can change -- this is unsound.
        let cell_ref: &i32 = leak.get().unwrap();
        assert_eq!(*cell_ref, 1);
        *cursor.borrow_mut().unwrap() = 42;
        assert_eq!(*cell_ref, 42);
    });
}
