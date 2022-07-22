use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|token| {
        let cell = GhostCell::new(42);

        let r = cell.borrow(&token);
        std::mem::drop(cell);

        *r
    });
}
