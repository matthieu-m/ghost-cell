use ghost_cell::{GhostCell, GhostCursor, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let cell = GhostCell::new(1);
        let cursor = GhostCursor::new(&mut token, Some(&cell));

        assert_eq!(1, *cell.borrow(&token));
        assert_eq!(Some(&1), cursor.borrow());
    });
}
