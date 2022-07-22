use ghost_cell::{GhostCell, GhostCursor, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let (one, two) = (GhostCell::new(1), GhostCell::new(2));

        let cursor = GhostCursor::new(&mut token, Some(&one));
        if let Some(one) = cursor.into_inner() {
            assert_eq!(2, *two.borrow(&token));
            *one = 3;
        }
    });
}
