use ghost_cell::{GhostCell, GhostToken};
use ghost_cell::ghost_borrow::GhostBorrow;

#[test]
fn multiple_borrows_tuple() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);

        let (reference1, reference2, reference3, reference4): (&i32, &i32, &i32, &i32)
            = (&cell1, &cell2, &cell3, &cell4).borrow(&token);

        (*reference1, *reference2, *reference3, *reference4)
    });
    assert_eq!((42, 47, 7, 9), value);
}

#[test]
fn multiple_borrows_tuple_ref() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let tuple = (cell1, cell2, cell3, cell4);

        let reference: &(i32, i32, i32, i32) = tuple.borrow(&token);

        (reference.0, reference.1, reference.2, reference.3)
    });
    assert_eq!((42, 47, 7, 9), value);
}

#[test]
fn multiple_borrows_array_ref() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let array = [cell1, cell2, cell3, cell4];

        let reference: &[i32; 4] = array.borrow(&token);

        (reference[0], reference[1], reference[2], reference[3])
    });
    assert_eq!((42, 47, 7, 9), value);
}

#[test]
fn multiple_borrows_tuple_unsized() {
    let value = GhostToken::new(|token| {
        let mut data1 = 42;
        let mut data2 = [47];
        let mut data3 = 7;
        let mut data4 = [9];

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn ToString);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn ToString);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut [i32]);

        let (reference1, reference2, reference3, reference4) = (cell1, cell2, cell3, cell4).borrow(&token);

        (reference1.to_string(), reference2[0], reference3.to_string(), reference4[0])
    });
    assert_eq!(("42".to_owned(), 47, "7".to_owned(), 9), value);
}

#[test]
fn multiple_borrows_array_unsized_slice() {
    let value = GhostToken::new(|token| {
        let mut data1 = [42];
        let mut data2 = [47];
        let mut data3 = [7];
        let mut data4 = [9];

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut [i32]);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut [i32]);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut [i32]);
        let array = [cell1, cell2, cell3, cell4];

        let reference: [&[i32]; 4] = array.borrow(&token);

        reference.map(|slice| slice[0])
    });
    assert_eq!([42, 47, 7, 9], value);
}

#[test]
fn multiple_borrows_array_unsized_dyn_trait() {
    let value = GhostToken::new(|token| {
        let mut data1 = 42;
        let mut data2 = 47;
        let mut data3 = 7;
        let mut data4 = 9;

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn ToString);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut dyn ToString);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn ToString);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut dyn ToString);
        let array = [cell1, cell2, cell3, cell4];

        let reference: [&dyn ToString; 4] = array.borrow(&token);

        reference.map(ToString::to_string)
    });
    assert_eq!(["42".to_owned(), "47".to_owned(), "7".to_owned(), "9".to_owned()], value);
}
