use ghost_cell::{GhostCell, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let one = GhostCell::new(1);
        let two = GhostCell::new(2);

        let r = one.borrow_mut(&mut token);
        assert_eq!(2, *two.borrow(&token));

        *r = 33;
    });
}
