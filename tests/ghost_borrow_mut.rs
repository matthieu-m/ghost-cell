#![cfg(feature = "experimental-multiple-mutable-borrows")]

use ghost_cell::{GhostCell, GhostToken};
use ghost_cell::ghost_borrow_mut::GhostBorrowMut;

#[test]
fn multiple_borrows_tuple() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);

        let (reference1, reference2, reference3, reference4): (&mut i32, &mut i32, &mut i32, &mut i32)
            = (&cell1, &cell2, &cell3, &cell4).borrow_mut(&mut token).unwrap();
        *reference1 = 33;
        *reference2 = 34;
        *reference3 = 35;
        *reference4 = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*cell1.borrow(&token), *cell2.borrow(&token), *cell3.borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
#[should_panic]
fn multiple_borrows_tuple_aliased() {
    GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let _: (&mut i32, &mut i32, &mut i32, &mut i32)
            = (&cell1, &cell2, &cell3, &cell2).borrow_mut(&mut token).unwrap();
    });
}

#[test]
fn multiple_borrows_tuple_ref() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let tuple = (cell1, cell2, cell3, cell4);

        let reference: &mut (i32, i32, i32, i32)
            = tuple.borrow_mut(&mut token).unwrap();
        reference.0 = 33;
        reference.1 = 34;
        reference.2 = 35;
        reference.3 = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*tuple.0.borrow(&token), *tuple.1.borrow(&token), *tuple.2.borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
fn multiple_borrows_array_ref() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let array = [cell1, cell2, cell3, cell4];

        let reference: &mut [i32; 4]
            = array.borrow_mut(&mut token).unwrap();
        reference[0] = 33;
        reference[1] = 34;
        reference[2] = 35;
        reference[3] = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*array[0].borrow(&token), *array[1].borrow(&token), *array[2].borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
fn check_distinct() {
    // small array
    GhostToken::new(|mut token| {
        let cells = [
            GhostCell::new(1),
            GhostCell::new(2),
            GhostCell::new(3),
            GhostCell::new(4),
            GhostCell::new(5),
            GhostCell::new(6),
        ];

        // no aliasing
        let tuple1 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5]);
        assert!(tuple1.borrow_mut(&mut token).is_ok());

        // aliasing at start/end
        let tuple2 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[0]);
        assert!(tuple2.borrow_mut(&mut token).is_err());
    });

    // big array
    GhostToken::new(|mut token| {
        let cells = [
            GhostCell::new(1),
            GhostCell::new(2),
            GhostCell::new(3),
            GhostCell::new(4),
            GhostCell::new(5),
            GhostCell::new(6),
            GhostCell::new(7),
            GhostCell::new(8),
            GhostCell::new(9),
            GhostCell::new(10),
            GhostCell::new(11),
            GhostCell::new(12),
        ];

        // no aliasing
        let tuple1 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple1.borrow_mut(&mut token).is_ok());

        // aliasing at start/end
        let tuple2 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[0]);
        assert!(tuple2.borrow_mut(&mut token).is_err());

        // aliasing at the start
        let tuple3 = (&cells[0], &cells[0], &cells[1], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple3.borrow_mut(&mut token).is_err());

        // aliasing at the end
        let tuple4 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[10]);
        assert!(tuple4.borrow_mut(&mut token).is_err());

        // aliasing in the middle
        let tuple5 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[5], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple5.borrow_mut(&mut token).is_err());
    });
}
