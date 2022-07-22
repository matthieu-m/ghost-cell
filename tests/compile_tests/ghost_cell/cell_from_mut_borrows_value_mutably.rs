use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|token| {
        let mut value = 42;

        let cell = GhostCell::from_mut(&mut value);

        assert_eq!(42, value);
        assert_eq!(42, *cell.borrow(&token));
    });
}
