type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Keys = tuple[28]

// ****************************************************************
// Subcells

fn subcells_ ['a]
             <fnot : fn('a) -> 'a,
              fand : fn('a, 'a) -> 'a,
              for  : fn('a, 'a) -> 'a,
              fxor : fn('a, 'a) -> 'a>
             (slice : Slice 'a)
              Slice 'a =
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

// Spec: subcells_bitslice = reindex[ | ] . subcells . reindex [ | ]
// Alt spec: subcells . reindex [ | ] = reindex[ | ] . subcells_bitslice
fn subcells_bitslice0 ['a]
                      <fnot : fn('a) -> 'a,
                       fand : fn('a, 'a) -> 'a,
                       for : fn('a, 'a) -> 'a,
                       fxor : fn('a, 'a) -> 'a>
                      (state : Slice Col Row 'a)
                      Slice Col Row 'a =
    let state = reindex[Slice | Col Row](state) in
    let res = (let+ slice  : Col Row _ = state in
               subcells_.['a]<fnot, fand, for, fxor>(slice) : Col Row Slice 'a) in
    reindex[Col Row | Slice](res)

// Apply (Let-Beta) at `let state = ... in ...`
fn subcells_bitslice1 ['a]
                      <fnot : fn('a) -> 'a,
                       fand : fn('a, 'a) -> 'a,
                       for : fn('a, 'a) -> 'a,
                       fxor : fn('a, 'a) -> 'a>
                      (state : Slice Col Row 'a)
                      Slice Col Row 'a =
    let res = (let+ slice  : Col Row _ = reindex[Slice | Col Row](state) in
               subcells_.['a]<fnot, fand, for, fxor>(slice) : Col Row Slice 'a) in
    reindex[Col Row | Slice](res)

// Apply (Let-Beta) at `let res = ... in ...`
fn subcells_bitslice2 ['a]
                      <fnot : fn('a) -> 'a,
                       fand : fn('a, 'a) -> 'a,
                       for : fn('a, 'a) -> 'a,
                       fxor : fn('a, 'a) -> 'a>
                      (state : Slice Col Row 'a)
                      Slice Col Row 'a =
    reindex[Col Row | Slice](
        (let+ slice  : Col Row _ = reindex[Slice | Col Row](state) in
         subcells_.['a]<fnot, fand, for, fxor>(slice) : Col Row Slice 'a))

// Apply (Reindex-Map) at `let+ slice : ... = ... in ...`
fn subcells_bitslice3 ['a]
                      <fnot : fn('a) -> 'a,
                       fand : fn('a, 'a) -> 'a,
                       for : fn('a, 'a) -> 'a,
                       fxor : fn('a, 'a) -> 'a>
                      (state : Slice Col Row 'a)
                      Slice Col Row 'a =
    reindex[Col Row | Slice](
      reindex[Slice | Col Row](
         subcells_.[Col Row 'a]
                   <lift[Col Row](fnot),
                    lift[Col Row](fand),
                    lift[Col Row](for),
                    lift[Col Row](fxor)>(state)))

// Apply (Reindex-Id) at `reindex[...] (reindex [...] (...))`
fn subcells_bitslice ['a]
                     <fnot : fn('a) -> 'a,
                      fand : fn('a, 'a) -> 'a,
                      for : fn('a, 'a) -> 'a,
                      fxor : fn('a, 'a) -> 'a>
                     (state : Slice Col Row 'a)
                     Slice Col Row 'a =
    subcells_.[Col Row 'a]
              <lift[Col Row](fnot),
               lift[Col Row](fand),
               lift[Col Row](for),
               lift[Col Row](fxor)>(state)

// ****************************************************************
// Permbits

fn col_reverse ['a]  (cols : Col 'a) Col 'a =
    Col [
        cols[3],
        cols[2],
        cols[1],
        cols[0]
    ]

fn transpose ['a] (cols : Col Row 'a) Row Col 'a =
 // = reindex[Col | Row](cols)
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

// Spec: permbits_bitslice = reindex[ | ] . permbits . reindex [ | ]
// Alt spec: permbits . reindex[ | ] = reindex [ | ] . permbits_bitslice
fn permbits_bitslice0 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row](state) in
    let res =
        (let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
        let state = reindex[Col Row | Slice](state) in
        let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
        reindex[Slice | Col Row](res) : Col Row Slice 'a)
    in
    reindex[Col Row | Slice](res)

// Apply (Let-Float) to `let res = let permbits = _ in _ in _`
fn permbits_bitslice1 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row](state) in
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let res =
       (let state = reindex[Col Row | Slice](state) in
        let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
        reindex[Slice | Col Row](res) : Col Row Slice 'a)
    in
    reindex[Col Row | Slice](res)

// Apply (Let-Float) to `let res = let state = _ in _ in _`
fn permbits_bitslice2 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row](state) in
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let state = reindex[Col Row | Slice](state) in
    let res =
       (let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
        reindex[Slice | Col Row](res) : Col Row Slice 'a)
    in
    reindex[Col Row | Slice](res)

// Apply (Let-Float) to `let res = let res = _ in _ in _`
fn permbits_bitslice2 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = reindex[Slice | Col Row](state) in
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let state = reindex[Col Row | Slice](state) in
    let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    let res = reindex[Slice | Col Row](res) in
    reindex[Col Row | Slice](res)

// Apply (Let-Beta) at first occurrence of `let state = _ in _ `
fn permbits_bitslice3 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let state = reindex[Col Row | Slice](reindex[Slice | Col Row](state)) in
    let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    let res = reindex[Slice | Col Row](res) in
    reindex[Col Row | Slice](res)

// Apply (Reindex-Id)
fn permbits_bitslice4 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let state = state in
    let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    let res = reindex[Slice | Col Row](res) in
    reindex[Col Row | Slice](res)

// Apply (Let-Beta) at `let state = ... in ...`
fn permbits_bitslice5 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    let res = reindex[Slice | Col Row](res) in
    reindex[Col Row | Slice](res)

// Apply (Let-Beta) at second occurrence of `let res = _ in _ `
fn permbits_bitslice6 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let res =
            (let+ f : Slice _ = permbits
             and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    reindex[Col Row | Slice](reindex[Slice | Col Row](res))

// Apply (Reindex-Id)
fn permbits_bitslice7 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let res =
            (let+ f : Slice _ = permbits and slice = state in
             f.['a](slice) : Slice Col Row 'a) in
    res

// Apply (Let-Beta) at `let res = _ in _ `
fn permbits_bitslice8 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let permbits : Slice fn ['a](Col Row 'a) -> Col Row 'a = Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] in
    let+ f : Slice _ = permbits and slice = state in
    f.['a](slice)

// Apply (Let-Beta) at `let permbits = _ in _ `
fn permbits_bitslice9 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let+ f : Slice _ = (Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] : Slice fn ['a](Col Row 'a) -> Col Row 'a )
    and slice = state in
    f.['a](slice)

// Apply (Let+-Lookup) at `let+ f = _ and slice = _ in _ `
fn permbits_bitslice10 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    Slice[
      (Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] : Slice fn ['a](Col Row 'a) -> Col Row 'a)[0].['a](state[0]),
      (Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] : Slice fn ['a](Col Row 'a) -> Col Row 'a)[1].['a](state[1]),
      (Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] : Slice fn ['a](Col Row 'a) -> Col Row 'a)[2].['a](state[2]),
      (Slice[
            & rev_rotate_1,
            & rev_rotate_2,
            & rev_rotate_3,
            & rev_rotate_0
        ] : Slice fn ['a](Col Row 'a) -> Col Row 'a)[3].['a](state[3])]

// Apply (Lookup-Constr) at all `(Slice[...])[k]`
fn permbits_bitslice ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    Slice[
      rev_rotate_1.['a](state[0]),
      rev_rotate_2.['a](state[1]),
      rev_rotate_3.['a](state[2]),
      rev_rotate_0.['a](state[3])]

// ****************************************************************
// Add round key

// Spec: add_round_key_bitslice(_,_) = reindex[ | ] . add_round_key(reindex [ | ](_), reindex [ | ](_))
// Alt spec: add_round_key(reindex [ | ](_), reindex [ | ](_)) = reindex [ | ] . add_round_key_bitslice(_,_)
fn add_round_key_bitslice0 ['a]
                           <fxor: fn('a, 'a) -> 'a>
                           (state : Slice Col Row 'a,
                            key : Slice Col Row 'a)
                            Slice Col Row 'a =
    let key = reindex[Slice | Col Row](key) in
    let state = reindex[Slice | Col Row](state) in
    let res = (let+ a_state : Col Row Slice _ = state
               and a_key = key in
               fxor.(a_state, a_key) : Col Row Slice 'a) in
    reindex[Col Row | Slice](res)

// (Let-Beta) at `let res = ... in ...`
fn add_round_key_bitslice1 ['a]
                           <fxor: fn('a, 'a) -> 'a>
                           (state : Slice Col Row 'a,
                            key : Slice Col Row 'a)
                            Slice Col Row 'a =
    let key = reindex[Slice | Col Row](key) in
    let state = reindex[Slice | Col Row](state) in
    reindex[Col Row | Slice]((let+ a_state : Col Row Slice _ = state
                               and a_key = key in
                               fxor.(a_state, a_key) : Col Row Slice 'a))

// (Let-Beta) at `let key = ... in ...` and `let state = ... in ...`
fn add_round_key_bitslice2 ['a]
                           <fxor: fn('a, 'a) -> 'a>
                           (state : Slice Col Row 'a,
                            key : Slice Col Row 'a)
                            Slice Col Row 'a =
    reindex[Col Row | Slice](
        (let+ a_state : Col Row Slice _ = reindex[Slice | Col Row](state)
         and a_key = reindex[Slice | Col Row](key) in
         fxor.(a_state, a_key) :  Col Row Slice 'a))

// (Reindex-Let+) at `reindex[...](let+ a_state = ... and a_key = ... in ...)`
fn add_round_key_bitslice3 ['a]
                           <fxor: fn('a, 'a) -> 'a>
                           (state : Slice Col Row 'a,
                            key : Slice Col Row 'a)
                            Slice Col Row 'a =
     reindex[Col Row | Slice](
         reindex[Slice | Col Row](
             (lift[Slice Col Row](fxor).(state, key) : Slice Col Row 'a)))

// (Reindex-Id)
fn add_round_key_bitslice ['a]
                           <fxor: fn('a, 'a) -> 'a>
                           (state : Slice Col Row 'a,
                            key : Slice Col Row 'a)
                            Slice Col Row 'a =
  lift[Slice Col Row](fxor).(state, key)

// ****************************************************************
// Round

// Spec: round_bitslice = reindex[ | ] . round . reindex [ | ]
// fn round_bitslice0 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let state = reindex[Slice | Col Row](state) in
//         let key = reindex[Slice | Col Row](key) in
//         let state = subcells.['a]<fnot, fand, for, fxor>(state) in
//         let state = permbits.['a](state) in
//         let res = add_round_key.['a]<fxor>(state, key) in
//         reindex[Col Row | Slice](res)

// By (Let-Beta) on `let state = ... in ...`
// fn round_bitslice1 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let key = reindex[Slice | Col Row](key) in
//         let state = subcells.['a]<fnot, fand, for, fxor>(reindex[Slice | Col Row](state)) in
//         let state = permbits.['a](state) in
//         let res = add_round_key.['a]<fxor>(state, key) in
//         reindex[Col Row | Slice](res)

// By Alt Spec of `subcells`
// fn round_bitslice2 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let key = reindex[Slice | Col Row](key) in
//         let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
//         let state = reindex[Slice | Col Row](state) in
//         let state = permbits.['a](state) in
//         let res = add_round_key.['a]<fxor>(state, key) in
//         reindex[Col Row | Slice](res)

// By (Let-Beta) on `let state = .. in ..`
// fn round_bitslice3 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let key = reindex[Slice | Col Row](key) in
//         let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
//         let state = permbits.['a](reindex[Slice | Col Row](state)) in
//         let res = add_round_key.['a]<fxor>(state, key) in
//         reindex[Col Row | Slice](res)

// By Alt Spec of `permbits`
// fn round_bitslice4 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let key = reindex[Slice | Col Row](key) in
//         let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
//         let state = permbits_bitslice.['a](state) in
//         let state = reindex[Slice | Col Row](state) in
//         let res = add_round_key.['a]<fxor>(state, key) in
//         reindex[Col Row | Slice](res)

// By (Let-Beta) on `let key = ... in ...` and `let state = ... in ...`
// fn round_bitslice5 ['a]
//                   <fnot : fn('a) -> 'a,
//                    fand : fn('a, 'a) -> 'a,
//                    for : fn('a, 'a) -> 'a,
//                    fxor : fn('a, 'a) -> 'a>
//                   (state : Slice Col Row 'a,
//                    key : Slice Col Row 'a)
//                    Slice Col Row 'a =
//         let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
//         let state = permbits_bitslice.['a](state) in
//         let res = add_round_key.['a]<fxor>(reindex[Slice | Col Row](state), reindex[Slice | Col Row](key)) in
//         reindex[Col Row | Slice](res)

// By Alt Spec of `add_round_key`
fn round_bitslice6 ['a]
                  <fnot : fn('a) -> 'a,
                   fand : fn('a, 'a) -> 'a,
                   for : fn('a, 'a) -> 'a,
                   fxor : fn('a, 'a) -> 'a>
                  (state : Slice Col Row 'a,
                   key : Slice Col Row 'a)
                   Slice Col Row 'a =
        let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
        let state = permbits_bitslice.['a](state) in
        let res = add_round_key_bitslice.['a]<fxor>(state, key) in
        let res = reindex[Slice | Col Row](res) in
        reindex[Col Row | Slice](res)


// By (Reindex-Id)
fn round_bitslice ['a]
                  <fnot : fn('a) -> 'a,
                   fand : fn('a, 'a) -> 'a,
                   for : fn('a, 'a) -> 'a,
                   fxor : fn('a, 'a) -> 'a>
                  (state : Slice Col Row 'a,
                   key : Slice Col Row 'a)
                   Slice Col Row 'a =
        let state = subcells_bitslice.['a]<fnot, fand, for, fxor>(state) in
        let state = permbits_bitslice.['a](state) in
        add_round_key_bitslice.['a]<fxor>(state, key)


// ****************************************************************
// Primitive

// Spec of `gift_bitslice` gift_bitslice = reindex[ | ] . gift . reindex [ | ]
// fn gift_bitslice0 ['a]
//                  <fnot : fn('a) -> 'a,
//                   fand : fn('a, 'a) -> 'a,
//                   for : fn('a, 'a) -> 'a,
//                   fxor : fn('a, 'a) -> 'a>
//                  (state : Slice Col Row 'a,
//                   keys : Keys Slice Col Row 'a)
//                   Slice Col Row 'a =
//     let state = reindex[Slice | Col Row](state) in
//     let keys = (let+ keys : Keys _ = keys in reindex[Slice | Col Row](keys) : Keys Col Row Slice 'a) in
//     let state = fold[28](round.['a]<fnot, fand, for, fxor>)(state, keys) in
//     reindex[Col Row | Slice](state)

// (Fold-reindex)
// XXX: invalid syntax
// fn gift_bitslice1 ['a]
//                  <fnot : fn('a) -> 'a,
//                   fand : fn('a, 'a) -> 'a,
//                   for : fn('a, 'a) -> 'a,
//                   fxor : fn('a, 'a) -> 'a>
//                  (state : Slice Col Row 'a,
//                   keys : Keys Slice Col Row 'a)
//                   Slice Col Row 'a =
//     fold[28](
//         let state = reindex[Slice | Col Row](state) in
//         let keys = reindex[Slice | Col Row](keys) in
//         let res = round.['a]<fnot, fand, for, fxor>(state, keys) in
//         reindex[Col Row | Slice](res))(state, keys)

// Spec of `round_bitslice`
fn gift_bitslice ['a]
                 <fnot : fn('a) -> 'a,
                  fand : fn('a, 'a) -> 'a,
                  for : fn('a, 'a) -> 'a,
                  fxor : fn('a, 'a) -> 'a>
                 (state : Slice Col Row 'a,
                  keys : Keys Slice Col Row 'a)
                  Slice Col Row 'a =
    fold[28](round_bitslice.['a]<fnot, fand, for, fxor>)(state, keys)


// ****************************************************************
// Concretizations

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

fn subcells32_bitslice (
    state : Slice Col Row Double bool
) Slice Col Row Double bool =
  subcells_bitslice.[Double bool]<double_not, double_and, double_or, double_xor>(state)

fn round32_bitslice(
    state : Slice Col Row Double bool,
    key : Slice Col Row Double bool
) Slice Col Row Double bool =
   round_bitslice.[Double bool]<double_not, double_and, double_or, double_xor>(state, key)

fn gift16_bitslice(
    state : Slice Col Row bool,
    keys : Keys Slice Col Row bool
) Slice Col Row bool =
    gift_bitslice.[bool]<&fnot, &fand, &for, &fxor>(state, keys)

fn gift32_bitslice(
    state : Slice Col Row Double bool,
    keys : Keys Slice Col Row Double bool
) Slice Col Row Double bool =
    gift_bitslice.[Double bool]
        <double_not, double_and, double_or, double_xor>(state, keys)

fn transpose32_inv (state: Col Row Slice Double bool)
   Slice Col Row Double bool =
   Slice[let+ s : Col Row _ = state in s[0],
         let+ s : Col Row _ = state in s[1],
         let+ s : Col Row _ = state in s[2],
         let+ s : Col Row _ = state in s[3]]

fn transpose32 (s: Slice Col Row Double bool)
   Col Row Slice Double bool =
  reindex[ Slice | Col Row ](s)

 // =
 //   Col[ Row[ Slice[s[0][0][0],
 //                   s[1][0][0],
 //                   s[2][0][0],
 //                   s[3][0][0]],
 //             Slice[s[0][0][1],
 //                   s[1][0][1],
 //                   s[2][0][1],
 //                   s[3][0][1]],
 //             Slice[s[0][0][2],
 //                   s[1][0][2],
 //                   s[2][0][2],
 //                   s[3][0][2]],
 //             Slice[s[0][0][3],
 //                   s[1][0][3],
 //                   s[2][0][3],
 //                   s[3][0][3]]],
 //        Row[ Slice[s[0][1][0],
 //                   s[1][1][0],
 //                   s[2][1][0],
 //                   s[3][1][0]],
 //             Slice[s[0][1][1],
 //                   s[1][1][1],
 //                   s[2][1][1],
 //                   s[3][1][1]],
 //             Slice[s[0][1][2],
 //                   s[1][1][2],
 //                   s[2][1][2],
 //                   s[3][1][2]],
 //             Slice[s[0][1][3],
 //                   s[1][1][3],
 //                   s[2][1][3],
 //                   s[3][1][3]]],
 //        Row[ Slice[s[0][2][0],
 //                   s[1][2][0],
 //                   s[2][2][0],
 //                   s[3][2][0]],
 //             Slice[s[0][2][1],
 //                   s[1][2][1],
 //                   s[2][2][1],
 //                   s[3][2][1]],
 //             Slice[s[0][2][2],
 //                   s[1][2][2],
 //                   s[2][2][2],
 //                   s[3][2][2]],
 //             Slice[s[0][2][3],
 //                   s[1][2][3],
 //                   s[2][2][3],
 //                   s[3][2][3]]],
 //        Row[ Slice[s[0][3][0],
 //                   s[1][3][0],
 //                   s[2][3][0],
 //                   s[3][3][0]],
 //             Slice[s[0][3][1],
 //                   s[1][3][1],
 //                   s[2][3][1],
 //                   s[3][3][1]],
 //             Slice[s[0][3][2],
 //                   s[1][3][2],
 //                   s[2][3][2],
 //                   s[3][3][2]],
 //             Slice[s[0][3][3],
 //                   s[1][3][3],
 //                   s[2][3][3],
 //                   s[3][3][3]]]]

