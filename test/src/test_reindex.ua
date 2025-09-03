type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Keys = tuple[28]

fn col_reverse ['a]  (cols : Col 'a) Col 'a = 
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

fn rev_rotate_0['a](cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range(rows))[0] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_1 ['a](cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range[](rows))[1] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_2 ['a] (cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range(rows))[2] in
    # reindex[Row | Col](range(rows))
    
fn rev_rotate_3 ['a] (cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(range(rows))[3] in
    # reindex[Row | Col](range(rows))
    
fn permbits ['a] (state : Col Row Slice 'a) Col Row Slice 'a = 
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
    
    
fn subcells_reindexed ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    let state = # reindex[Slice | Col Row](range(state)) in
    # reindex[Col Row | Slice](
        range(# let+ slice = range[Col Row](state) in 
            subcells.['a](fnot, fand, for, fxor, slice)
        )
    )
    
fn subcells ['a] ( 
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Col Row Slice 'a
) Col Row Slice 'a =
    # let+ slice = range[Col Row](state) in 
        subcells.['a](fnot, fand, for, fxor, slice)
        

    

fn add_round_key ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Col Row Slice 'a,
    key : Col Row Slice 'a
) Col Row Slice 'a =
    # let+ state = range[Col Row Slice](state) and key = range[Col Row Slice](key) in
        fxor.(state, key)
    
fn round ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Col Row Slice 'a,
    key : Col Row Slice 'a
) Col Row Slice 'a = 
    let state = subcells.['a](fnot, fand, for, fxor, state) in
    let state = permbits.['a](state) in
    add_round_key.['a](fxor, state, key)
    
fn gift ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Col Row Slice 'a, 
    keys : Keys Col Row Slice 'a
) Col Row Slice 'a = 
    fold[28](round.['a](fnot, fand, for, fxor))(state, range(keys))
    
fn fnot(b: bool) bool = ! b
fn fand(lhs: bool, rhs: bool) bool = lhs & rhs
fn for(lhs: bool, rhs: bool) bool = lhs | rhs
fn fxor(lhs: bool, rhs : bool) bool = lhs ^ rhs
    
fn double_not(d: Double bool) Double bool = 
    # let+ b = range[Double](d) in ! b 

fn double_and(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs & rhs
    
fn double_or(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs | rhs
    
fn double_xor(lhs: Double bool, rhs: Double bool) Double bool = 
    # let+ lhs = range[Double](lhs) and rhs = range[Double](rhs) in lhs ^ rhs
    
fn gift32(
    state : Col Row Slice Double bool,
    keys : Keys Col Row Slice Double bool
) Col Row Slice Double bool =
    gift.[Double bool](
        double_not, double_and, double_or, double_xor, state, keys
    )

fn gift16(
    state : Col Row Slice bool,
    keys : Keys Col Row Slice bool
) Col Row Slice bool =
gift.[bool](
    fnot, fand, for, fxor, state, keys
) 
