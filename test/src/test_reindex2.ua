type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Keys = tuple[28]

fn col_reverse ['a]  (cols : Col 'a) Col 'a = 
    Col [
        cols[3],
        cols[2],
        cols[1],
        cols[0]
    ]

fn transpose ['a] (cols : Col Row 'a) Row Col 'a = 
    Row[
        Col[
            cols[0][0],
            cols[0][1],
            cols[0][2],
            cols[0][3]
        ],
        Col[
            cols[1][0],
            cols[1][1],
            cols[1][2],
            cols[1][3]
        ],
        Col[
            cols[2][0],
            cols[2][1],
            cols[2][2],
            cols[2][3]
        ],
        Col[
            cols[3][0],
            cols[3][1],
            cols[3][2],
            cols[3][3] 
        ]
    ] 

fn rev_rotate_0['a](cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(rows)[0] in
    reindex[Row | Col](rows)
    
fn rev_rotate_1 ['a](cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(rows)[1] in
    reindex[Row | Col](rows)
    
fn rev_rotate_2 ['a] (cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(rows)[2] in
    reindex[Row | Col](rows)
    
fn rev_rotate_3 ['a] (cols : Col Row 'a) Col Row 'a = 
    let cols = col_reverse.[Row 'a](cols) in
    let rows = transpose.['a](cols) in
    let rows = circ(rows)[3] in
    reindex[Row | Col](rows)
    
fn permbits ['a] (state : Col Row Slice 'a) Col Row Slice 'a = 
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let state = reindex[Col Row | Slice](state) in
    reindex[Slice | Col Row](
        ( let+ f = permbits and slice = state in 
            f.['a](slice) : Slice Col Row 'a )
    )
    
    
// wrap reindex
fn permbits_0 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    reindex[Col Row | Slice](
        (let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
        let state = reindex[Col Row | Slice]((state : Col Row Slice 'a)) in
        reindex[Slice | Col Row](
            ( let+ f = permbits and slice = state in 
            f.['a](slice) : Slice Col Row 'a )
        ) : Col Row Slice 'a)
    )
    
// Un-nested let
fn permbits_1 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let state = reindex[Col Row | Slice]((state : Col Row Slice 'a)) in
    reindex[Col Row | Slice](
        (
            reindex[Slice | Col Row](
                ( let+ f = permbits and slice = state in 
                    f.['a](slice) : Slice Col Row 'a 
                )
        ) : Col Row Slice 'a)
    )
    
// Inline term
fn permbits_2 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let state : Slice Col Row 'a = reindex[Col Row | Slice](
        (reindex[Slice | Col Row]((state : Slice Col Row 'a)) : Col Row Slice 'a)
    ) in
    reindex[Col Row | Slice](
        (
            reindex[Slice | Col Row](
                ( let+ f = permbits and slice = state in 
                    f.['a](slice) : Slice Col Row 'a 
                )
        ) : Col Row Slice 'a)
    )
    
// simplify inline term 2
fn permbits_2 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let state : Slice Col Row 'a = state in
    reindex[Col Row | Slice](
        reindex[Slice | Col Row](
            ( let+ f = permbits and slice = state in 
                f.['a](slice) : Slice Col Row 'a 
            )
        )
    )
    
    
// Maybe we can inline only if we manage to simplify the expression ?
// Should we try to inline the perbits ?
// simplify inline term 3
fn permbits_2 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    reindex[Col Row | Slice](
        (
            reindex[Slice | Col Row](
                ( let+ f = permbits and slice = state in 
                    f.['a](slice) : Slice Col Row 'a 
                )
        ) : Col Row Slice 'a)
    )
    
// Simplify reindex
fn permbits_bitslice ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let+ f = permbits and slice = state in 
        f.['a](slice)
        
fn subcells ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for  : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    slice : Slice 'a
) Slice 'a = 
    let s0 = slice[0] in
    let s1 = slice[1] in
    let s2 = slice[2] in
    let s3 = slice[3] in
    let s1 = fxor.(s1, fand.(s0, s2)) in
    let s0 = fxor.(s0, fand.(s1, s3)) in
    let s2 = fxor.(s2, for.(s0, s1)) in
    let s3 = fxor.(s3, s2) in
    let s1 = fxor.(s1, s3) in
    let s3 = fnot.(s3) in
    let s2 = fxor.(s2, fand.(s0, s1)) in
    Slice [s3, s1, s2, s0]
    
    
fn subcells ['a] ( 
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Col Row Slice 'a
) Col Row Slice 'a =
    let+ row = state in 
        let+ slice = row in
            subcells.['a](fnot, fand, for, fxor, slice)
    
fn subcells_reindexed ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    reindex[Col Row | Slice](
        (let+ row = state in 
            let+ slice = row in
                subcells.['a](fnot, fand, for, fxor, slice) : Col Row Slice 'a)
    )
    
// inline
fn subcells_1 ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    reindex[Col Row | Slice](
        (let+ row = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in 
            let+ slice = row in
                subcells.['a](fnot, fand, for, fxor, slice) : Col Row Slice 'a)
    )
    

// ? range [X.. ] reindex[Y | X..] + lift
fn subcells_2 ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    reindex[Col Row | Slice](
        reindex[Slice | Col Row](
            subcells.[Col Row 'a](lift[Col Row](fnot), lift[Col Row](fand), 
                lift[Col Row](for), lift[Col Row](fxor), state)
        )
    )
 
// simplify reindex
fn subcells_bitslice ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    subcells.[Col Row 'a](lift[Col Row](fnot), lift[Col Row](fand), 
        lift[Col Row](for), lift[Col Row](fxor), state)

fn add_round_key ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Col Row Slice 'a,
    key : Col Row Slice 'a
) Col Row Slice 'a =
    let+ row_state = state and row_key = key in
        let+ slice_state = row_state and slice_key = row_key in
            let+ a_state = slice_state and a_key = slice_key in
                fxor.(a_state, a_key)
        
fn add_round_key_reindexed['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a = 
    let key = reindex[Slice | Col Row]((key : Slice Col Row 'a)) in
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    reindex[Col Row | Slice](
        (let+ row_state = state and row_key = key in
            let+ slice_state = row_state and slice_key = row_key in
                let+ a_state = slice_state and a_key = slice_key in
                    fxor.(a_state, a_key) : 
            Col Row Slice 'a
        )
    )
        
// inline    
fn add_round_key_1 ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a =
    reindex[Col Row | Slice](
        (let+ row_state = reindex[Slice | Col Row](state) 
            and row_key = reindex[Slice | Col Row](key) 
        in
            let+ slice_state = row_state and slice_key = row_key in
                let+ a_state = slice_state and a_key = slice_key in
                    fxor.(a_state, a_key) : 
            Col Row Slice 'a
        )
    ) 
    
// ? range [X.. ] reindex[Y | X..] + lift
fn add_round_key_2 ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a =
    reindex[Col Row | Slice](
        reindex[Slice | Col Row](
            (
                let f = lift[Slice Col Row](fxor) in
                f.(state, key) : Slice Col Row 'a)
        )
    )

// simplify reindex
fn add_round_key_bitslice ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a =
    let f = lift[Slice Col Row](fxor) in
    f.(state, key)
    
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
    
fn round_bitslice ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a = 
    let state = subcells_bitslice.['a](fnot, fand, for, fxor, state) in
    let state = permbits_bitslice.['a](state) in
    add_round_key_bitslice.['a](fxor, state, key)
    
fn gift ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Col Row Slice 'a, 
    keys : Keys Col Row Slice 'a
) Col Row Slice 'a = 
    fold[28](round.['a](fnot, fand, for, fxor))(state, keys)
    
fn fnot(b: bool) bool = ! b
fn fand(lhs: bool, rhs: bool) bool = lhs & rhs
fn for(lhs: bool, rhs: bool) bool = lhs | rhs
fn fxor(lhs: bool, rhs : bool) bool = lhs ^ rhs
    
fn double_not(d: Double bool) Double bool = 
    let+ b = d in ! b 

fn double_and(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs = lhs and rhs = rhs in lhs & rhs
    
fn double_or(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs = lhs and rhs = rhs in lhs | rhs
    
fn double_xor(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs = lhs and rhs = rhs in lhs ^ rhs
    
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
