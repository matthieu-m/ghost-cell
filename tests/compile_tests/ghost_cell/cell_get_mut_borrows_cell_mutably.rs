use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|token| {
        let mut cell = GhostCell::new(42);

        let r = cell.get_mut();
        assert_eq!(42, *cell.borrow(&token));

        *r = 33;
    });
}
