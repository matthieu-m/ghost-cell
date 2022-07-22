use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let cell = GhostCell::new(42);
        *cell.borrow_mut(&mut token) = 33;
        cell
    });
}
