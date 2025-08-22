type Col = tuple[4] 'a
type Row = tuple[4] 'a
type Slice = tuple[4] 'a

fn 'a. subcells(
    slice : Slice 'a, 
    fnot : fn('a) -> 'a,
    fand : fn('a, 'a) -> 'a,
    for : fn('a, 'a) -> 'a,
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


fn 'a. round(
    state : Col Row Slice 'a, 
    key : Col Row Slice 'a
) Col Row Slice 'a = 
    state
