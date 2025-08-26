type Col 'a = tuple[4]
type Row 'a = tuple[4]
type Slice 'a = tuple[4]
type Keys 'a = tuple[4]

fn 'a. col_reverse(cols : Col 'a) Col 'a = 
    # Col(
        range[](cols)[3],
        range[](cols)[2],
        range[](cols)[1],
        range[](cols)[0]
    )
fn 'a. transpose(cols : Col Row 'a) Row Col 'a = 
    # Row(
        # Col(
            range(range(cols)[0])[0],
            range(range(cols)[0])[1],
            range(range(cols)[0])[2],
            range(range(cols)[0])[3]
        ),
        # Col(
            range(range(cols)[1])[0],
            range(range(cols)[1])[1],
            range(range(cols)[1])[2],
            range(range(cols)[1])[3]
        ),
        # Col(
            range(range(cols)[2])[0],
            range(range(cols)[2])[1],
            range(range(cols)[2])[2],
            range(range(cols)[2])[3]
        ),
        # Col(
            range(range(cols)[3])[0],
            range(range(cols)[3])[1],
            range(range(cols)[3])[2],
            range(range(cols)[3])[3]           
        )
    )
    

fn 'a. rev_rotate_0(cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.['a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range[](rows))[0] in
    # reindex[Col | Row](range(rows))
    
fn 'a. rev_rotate_1(cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.['a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range[](rows))[1] in
    # reindex[Col | Row](range(rows))
    
fn 'a. rev_rotate_2(cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.['a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range(rows))[2] in
    # reindex[Col | Row](range(rows))
    
fn 'a. rev_rotate_3(cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.['a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range[](rows))[3] in
    # reindex[Col | Row](range(rows))
    
fn 'a. permbits(state : Col Row Slice 'a) Col Row Slice 'a = 
    let permbits = # Slice(
        rev_rotate_1,
        rev_rotate_2,
        rev_rotate_3,
        rev_rotate_0
    ) in
    let state = # reindex[Col Row | Slice](range(state)) in
    # reindex[Slice | Col Row](
        let+ f = range[Slice](permbits) and slice = range[Slice](state) in 
        f.['a](slice)
    )

fn 'a. subcells(
    slice : Slice 'a, 
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for  : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a
) Slice 'a = 
    let s0 = range[](slice)[0] in
    let s1 = range[](slice)[1] in
    let s2 = range[](slice)[2] in
    let s3 = range[](slice)[3] in
    let s1 = fxor.(s1, fand.(s0, s2)) in
    let s0 = fxor.(s0, fand.(s1, s3)) in
    let s2 = fxor.(s2, for.(s0, s1)) in
    let s3 = fxor.(s3, s2) in
    let s1 = fxor.(s1, s3) in
    let s3 = fnot.(s3) in
    let s2 = fxor.(s2, fand.(s0, s1)) in
    # Slice(s3, s1, s2, s0)
    
// fn 'a. subcells(
//     state : Col Row Slice 'a,
//     fnot : fn('a) -> 'a,
//     fand : fn('a, 'a) -> 'a,
//     for : fn('a, 'a) -> 'a,
//     fxor : fn('a, 'a) -> 'a
// ) Col Row Slice 'a =
//     # let+ slice = range[Col Row](state) in subcells(slice, fnot, fand, for, fxor)
//     

// fn 'a. add_round_key(
//     state : Col Row Slice 'a, 
//     key : Col Row Slice 'a, 
//     fxor: fn('a, 'a) -> 'a
// ) Col Row Slice 'a =
//     # let+ state = range[Col Row Slice](state) and key = range[Col Row Slice](key) in
//         fxor.(state, key)
    
fn 'a. round(
    state : Col Row Slice 'a, 
    key : Col Row Slice 'a,
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a
) Col Row Slice 'a = 
    let state = subcells.(state, fnot, fand, for, fxor) in
    let state = permbits.(state) in
    add_round_key.(state, fxor)
