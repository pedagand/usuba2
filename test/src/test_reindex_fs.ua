type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Key4 = tuple[4]
type C7 = tuple[7]
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
    
fn inv_transpose ['a] (cols : Row Col 'a) Col Row  'a = 
    Col[
        Row[
            cols[0][0],
            cols[0][1],
            cols[0][2],
            cols[0][3]
        ],
        Row[
            cols[1][0],
            cols[1][1],
            cols[1][2],
            cols[1][3]
        ],
        Row[
            cols[2][0],
            cols[2][1],
            cols[2][2],
            cols[2][3]
        ],
        Row[
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
        ( let+ f : Slice _ = permbits and slice = state in 
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
            ( let+ f : Slice _ = permbits and slice = state in 
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
                ( let+ f : Slice _ = permbits and slice = state in 
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
                ( let+ f : Slice _ = permbits and slice = state in 
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
            ( let+ f : Slice _ = permbits and slice = state in 
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
        reindex[Slice | Col Row](
            ( let+ f : Slice _ = permbits and slice = state in 
                f.['a](slice) : Slice Col Row 'a 
            )
        )
    )
    
    
fn inv_rev_rotate_1 ['a](slice : Col Row 'a) Col Row 'a = 
    let rows = reindex[Col | Row](slice) in
    // Why 3, I should think about it.
    let rows = circ(rows)[3] in
    let cols = inv_transpose.['a](rows) in
    col_reverse.[Row 'a](cols)
    
// Simplify reindex
fn permbits_bitslice ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let+ f : Slice _ = permbits and slice = state in 
        f.['a](slice)
        
fn map_rev_rotate_1 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let+ slice : Slice _ = state in
        rev_rotate_1.['a](slice)
        
fn map_in_rev_rotate_1 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let+ slice : Slice _ = state in
        inv_rev_rotate_1.['a](slice)

// permbits fixslice mode_0        
fn permbits_fixslice_mod_0_ ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = permbits_bitslice.['a](state) in
    let+ slice : Slice _ = state in 
        inv_rev_rotate_1.['a](slice)
        
// Inline permbits_mod_n-1
fn permbits_fixslice_mod_0_1 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let state : Slice Col Row 'a =     
        let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
        let+ f : Slice _ = permbits and slice = state in 
            f.['a](slice) 
    in
    let+ slice : Slice _ = state in 
        inv_rev_rotate_1.['a](slice)
        
        
// unested-let
fn permbits_fixslice_mod_0_2 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in
    let state : Slice Col Row 'a =     
        let+ f : Slice _ = permbits and slice = state in 
            f.['a](slice) 
    in
    let+ slice : Slice _ = state in 
        inv_rev_rotate_1.['a](slice)
        
// inline inv_rev_rotate_1
fn permbits_fixslice_mod_0_3 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & rev_rotate_1,
        & rev_rotate_2,
        & rev_rotate_3,
        & rev_rotate_0
    ] in   
    let+ f : Slice _ = permbits and slice = state in 
        inv_rev_rotate_1.['a](f.['a](slice))
        
fn  fix_rev_rotate_1 ['a](slice : Col Row 'a) Col Row 'a = 
    inv_rev_rotate_1.['a](rev_rotate_1.['a](slice))
    
fn  fix_rev_rotate_2 ['a](slice : Col Row 'a) Col Row 'a = 
    inv_rev_rotate_1.['a](rev_rotate_2.['a](slice))
    
fn  fix_rev_rotate_3 ['a](slice : Col Row 'a) Col Row 'a = 
    inv_rev_rotate_1.['a](rev_rotate_3.['a](slice))
    
fn  fix_rev_rotate_0 ['a](slice : Col Row 'a) Col Row 'a = 
    inv_rev_rotate_1.['a](rev_rotate_0.['a](slice))

// inline inv_rev_rotate_1 2
// - Creation of the composition of inv_rev_rotate_1 with rev_rotate_{0...3}
// Simplify the composition by compution the composition of permutation
fn permbits_fixslice_mod_0_4 ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
        & fix_rev_rotate_1,
        & fix_rev_rotate_2,
        & fix_rev_rotate_3,
        & fix_rev_rotate_0
    ] in   
    let+ f : Slice _ = permbits and slice = state in 
        f.['a](slice)
    
// permbits fixslice mode_1    
fn permbits_fixslice_mod_1_ ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let state : Slice Col Row 'a = 
        let+ slice : Slice _ = state in 
            rev_rotate_1.['a](slice)
    in
    let state = permbits_fixslice_mod_0_4.['a](state) in
    let+ slice : Slice _ = state in 
        inv_rev_rotate_1.['a](slice)
    
// permbits fixslice mode_2    
fn permbits_fixslice_mod_2_ ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let state : Slice Col Row 'a = let+ slice : Slice _ = state in rev_rotate_1.['a](slice) in
    let state = permbits_fixslice_mod_1_.['a](state) in
    let+ slice : Slice _ = state in inv_rev_rotate_1.['a](slice)
    
// permbits fixslice mode_3    
fn permbits_fixslice_mod_3_ ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let state : Slice Col Row 'a = let+ slice : Slice _ = state in rev_rotate_1.['a](slice) in
    let state = permbits_fixslice_mod_2_.['a](state) in
    let+ slice : Slice _ = state in inv_rev_rotate_1.['a](slice)

// permbits_fixslice_mod_{3...26}_
    
fn permbits_fixslice_mod_27_ ['a](state : Slice Col Row 'a) Slice Col Row 'a = 
    let state : Slice Col Row 'a = let+ slice : Slice _ = state in rev_rotate_1.['a](slice) in
    // permbits_fixslice_mod_27_ should be 27_ be to please the typechecker
    let state = permbits_fixslice_mod_2_.['a](state) in
    let+ slice : Slice _ = state in inv_rev_rotate_1.['a](slice)
    
// after the last round
// apply `fix_delay` 28 times
    
/// SUBCELLS
fn subcells_ ['a](
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
    let+ slice : Col Row _ = state in 
        subcells_.['a](fnot, fand, for, fxor, slice)
    
fn subcells_reindexed ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a
) Slice Col Row 'a = 
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    reindex[Col Row | Slice](
        (let+ slice : Col Row _ = state in 
            subcells_.['a](fnot, fand, for, fxor, slice) : Col Row Slice 'a)
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
        (let+ slice : Col Row _ = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
            subcells_.['a](fnot, fand, for, fxor, slice) : Col Row Slice 'a)
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
            subcells_.[Col Row 'a](lift[Col Row](fnot), lift[Col Row](fand), 
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
    subcells_.[Col Row 'a](lift[Col Row](fnot), lift[Col Row](fand), 
        lift[Col Row](for), lift[Col Row](fxor), state)

fn add_round_key ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Col Row Slice 'a,
    key : Col Row Slice 'a
) Col Row Slice 'a =
    let+ a_state : Col Row Slice _ = state and a_key = key in
        fxor.(a_state, a_key)
        
fn add_round_key_reindexed['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a = 
    let key = reindex[Slice | Col Row]((key : Slice Col Row 'a)) in
    let state = reindex[Slice | Col Row]((state : Slice Col Row 'a)) in
    reindex[Col Row | Slice](
        (let+ a_state : Col Row Slice _ = state and a_key = key in
            fxor.(a_state, a_key) : Col Row Slice 'a
        )
    )
        
// inline    
fn add_round_key_1 ['a](
    fxor: fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a =
    reindex[Col Row | Slice](
        (let+ a_state : Col Row Slice _ = reindex[Slice | Col Row](state) 
            and a_key = reindex[Slice | Col Row](key) 
        in
            fxor.(a_state, a_key) : Col Row Slice 'a
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
    
fn gift_bitslice ['a] (
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a, 
    keys : Keys Slice Col Row 'a
) Slice Col Row 'a = 
    fold[28](round_bitslice.['a](fnot, fand, for, fxor))(state, keys)
    
fn fnot(b: bool) bool = ! b
fn fand(lhs: bool, rhs: bool) bool = lhs & rhs
fn for(lhs: bool, rhs: bool) bool = lhs | rhs
fn fxor(lhs: bool, rhs : bool) bool = lhs ^ rhs
    
fn double_not(d: Double bool) Double bool = 
    let+ b : Double _ = d in ! b 

fn double_and(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs : Double _ = lhs and rhs = rhs in lhs & rhs
    
fn double_or(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs : Double _ = lhs and rhs = rhs in lhs | rhs
    
fn double_xor(lhs: Double bool, rhs: Double bool) Double bool = 
    let+ lhs : Double _ = lhs and rhs = rhs in lhs ^ rhs
    
fn giftb_32(
    state : Slice Col Row Double bool,
    keys : Keys Slice Col Row Double bool
) Slice Col Row Double bool =
    gift_bitslice.[Double bool](
        double_not, double_and, double_or, double_xor, state, keys
    )
    

fn permbits_mod_0 ['a](state: Slice Col Row 'a) 
    Slice Col Row 'a =
    Slice [
        circ(state[0])[0],
        circ(state[1])[1],
        circ(state[2])[2],
        circ(state[3])[3]
    ]
    
    
fn permbits_mod_1 ['a](state : Slice Col Row 'a) 
    Slice Col Row 'a = 
        Slice [
            let+ row : Col _ = state[0] in circ(row)[0],
            let+ row : Col _ = state[1] in circ(row)[1],
            let+ row : Col _ = state[2] in circ(row)[2],
            let+ row : Col _ = state[3] in circ(row)[3]
        ]

    
fn permbits_mod_2 ['a](state: Slice Col Row 'a) 
    Slice Col Row 'a =
    Slice [
        circ(state[0])[3],
        circ(state[1])[2],
        circ(state[2])[1],
        circ(state[3])[0]
    ]

fn permbits_mod_3 ['a](state : Slice Col Row 'a) 
    Slice Col Row 'a = 
    Slice [
        let+ row : Col _ = state[0] in circ(row)[3],
        let+ row : Col _ = state[1] in circ(row)[2],
        let+ row : Col _ = state[2] in circ(row)[1],
        let+ row : Col _ = state[3] in circ(row)[0]
    ]

fn round_fix_ ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    permbits : fn ['a](Slice Col Row 'a) -> Slice Col Row 'a, 
    state : Slice Col Row 'a,
    key : Slice Col Row 'a
) Slice Col Row 'a = 
    let state = subcells_bitslice.['a](fnot, fand, for, fxor, state) in
    let state = permbits.['a](state) in
    add_round_key_bitslice.['a](fxor, state, key)

fn round_fixslice ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a, 
    keys : Key4 Slice Col Row 'a
) Slice Col Row 'a = 
        let state = round_fix_.['a](fnot, fand, for, fxor, permbits_mod_0, state, keys[0]) in
        let state = round_fix_.['a](fnot, fand, for, fxor, permbits_mod_1, state, keys[1]) in
        let state = round_fix_.['a](fnot, fand, for, fxor, permbits_mod_2, state, keys[2]) in
        round_fix_.['a](fnot, fand, for, fxor, permbits_mod_3, state, keys[3])
        
fn gift_fixslice ['a](
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
    fxor : fn('a, 'a) -> 'a,
    state : Slice Col Row 'a,
    keys : C7 Key4 Slice Col Row 'a
) Slice Col Row 'a = 
    fold[7](round_fixslice.['a](fnot, fand, for, fxor))(state, keys)

fn giftf_32(
    state : Slice Col Row Double bool,
    keys : C7 Key4 Slice Col Row Double bool
) Slice Col Row Double bool =
    gift_fixslice.[Double bool](
        double_not, double_and, double_or, double_xor, state, keys
    )
