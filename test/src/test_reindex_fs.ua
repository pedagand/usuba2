type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Keys = tuple[28]

fn double_not(d: Double bool) Double bool = 
    # let+ b = range[Double](d) in ! b 

fn double_and(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs & rhs
    
fn double_or(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs | rhs
    
fn double_xor(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs ^ rhs
    
fn col_reverse ['a]  (cols : Col 'a) Col 'a = 
    # Col(
        range(cols)[3],
        range(cols)[2],
        range(cols)[1],
        range(cols)[0]
    )
    
fn col_reverse_row_double(cols : Col Row Double bool) Col Row Double bool = 
    # Col(
        range(cols)[3],
        range(cols)[2],
        range(cols)[1],
        range(cols)[0]
    )

fn transpose ['a] (cols : Col Row 'a) Row Col 'a = 
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
    
fn transpose_double(cols : Col Row Double bool) Row Col Double bool = 
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

fn rev_rotate_0_double(cols : Col Row Double bool) Col Row Double bool = 
    let cols = col_reverse_row_double.(cols) in
    let rows = transpose_double.(cols) in
    let rows = circ(range(rows))[0] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_1_double(cols : Col Row Double bool) Col Row Double bool = 
    let cols = col_reverse_row_double.(cols) in
    let rows = transpose_double.(cols) in
    let rows = circ(range[](rows))[1] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_2_double(cols : Col Row Double bool) Col Row Double bool = 
    let cols = col_reverse_row_double.(cols) in
    let rows = transpose_double.(cols) in
    let rows = circ(range(rows))[2] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_3_double(cols : Col Row Double bool) Col Row Double bool = 
    let cols = col_reverse_row_double.(cols) in
    let rows = transpose_double.(cols) in
    let rows = circ(range(rows))[3] in
    # reindex[Row | Col](range(rows))
    
fn permbits_bitslice_double(state : Slice Col Row Double bool) 
    Slice Col Row Double bool =
        let permbits = # Slice(
            rev_rotate_1_double,
            rev_rotate_2_double,
            rev_rotate_3_double,
            rev_rotate_0_double
        ) in
        # let+ f = range[Slice](permbits) and slice = range[Slice](Slice) in 
            f(slice)
    
    
// To monomorph.
fn subcells ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for  : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    slice : Slice 'a
) Slice 'a = 
    let s0 = range(slice)[0] in
    let s1 = range(slice)[1] in
    let s2 = range(slice)[2] in
    let s3 = range(slice)[3] in
    let s1 = fxor.(s1, fand.(s0, s2)) in
    let s0 = fxor.(s0, fand.(s1, s3)) in
    let s2 = fxor.(s2, for.(s0, s1)) in
    let s3 = fxor.(s3, s2) in
    let s1 = fxor.(s1, s3) in
    let s3 = fnot.(s3) in
    let s2 = fxor.(s2, fand.(s0, s1)) in
    # Slice(s3, s1, s2, s0)
    
fn subcells_bitslice_double (
    state : Slice Col Row Double bool
) Slice Col Row Double bool = 
    subcells.[Col Row Double bool](
            lift[Col Row](double_not), 
            lift[Col Row](double_and), 
            lift[Col Row](double_or),
            lift[Col Row](double_xor), 
            state
    )
    
fn add_round_key_bitslice_double(
    state : Slice Col Row Double bool,
    key : Slice Col Row Double bool
) Slice Col Row Double bool = 
    double_xor.(state, key)
    
fn round_bitslice_double (
    state : Slice Col Row Double bool,
    key : Slice Col Row Double bool
) Slice Col Row Double bool = 
    let state = subcells_bitslice_double.(state) in
    let state = permbits_bitslice_double.(state) in
    add_round_key_bitslice_double.(state, key)
    
    
fn gift_double (
    state : Col Row Slice Double bool, 
    keys : Keys Col Row Slice Double bool
) Col Row Slice Double bool = 
    fold[28](round_bitslice_double)(state, range(keys))
