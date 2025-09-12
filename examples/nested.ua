type Double = tuple[2]
type Col = tuple[4]
type Row = tuple[4]
type Slice = tuple[4]
type Keys = tuple[28]

fn test(b : bool) bool = 
    let ab = 
        let a = true in
        let b = false in
        a ^ b
    in
    b & ab

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


fn permbits_0 ['a](state : Slice Col Row 'a) Slice Col Row 'a =
    let state = # reindex[Slice | Col Row](range(state)) in
    # reindex[Col Row | Slice](
        range(
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
        )
    )

fn lu_permbits_0(8)(16) [a(12)](state(23) : Slice(4) Col(2) Row(3) a(12)) Slice(4) Col(2) Row(3) a(12) = 
    let state(24) = # reindex[Slice(4) | Col(2) Row(3)](range[](state(23))) in 
    let permbits(25) = # Slice(4) (rev_rotate_1(5), rev_rotate_2(6), rev_rotate_3(7), rev_rotate_0(4)) in 
    let state(26) = # reindex[Col(2) Row(3) | Slice(4)](range[](state(24))) in 
    # reindex[Col(2) Row(3) | Slice(4)](
        range[](# reindex[Slice(4) | Col(2) Row(3)](
            let+ f(27) = range[Slice(4)](permbits(25)) and slice(28) = range[Slice(4)](state(26)) in 
                f(27).[a(12)](slice(28))))
    )
