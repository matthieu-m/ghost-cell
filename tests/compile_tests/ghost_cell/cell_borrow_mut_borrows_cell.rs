use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let cell = GhostCell::new(42);

        let r = cell.borrow_mut(&mut token);
        std::mem::drop(cell);

        *r
    });
}
