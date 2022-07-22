use ghost_cell::{GhostCell, GhostCursor, GhostToken};

fn main() {
    GhostToken::new(|mut token| {
        let (one, two) = (GhostCell::new(1), GhostCell::new(2));

        let cursor = GhostCursor::new(&mut token, Some(&one));
        let aliased_token = cursor.into_parts().0;
        *two.borrow_mut(&mut token) = 4;
        assert_eq!(1, *one.borrow(aliased_token));
    });
}
