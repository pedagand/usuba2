open Ast

module Ty = struct
  let bool = TyBool
  let v v = TyVar v
  let app name ty = TyApp { name; ty }

  let fn tyvars parameters return_type =
    TyFun { tyvars; parameters; return_type }
end

module LTerm = struct
  let range ty term = LRange { ty; term }
  let cstr ty terms = LConstructor { ty; terms }
  let circ term = LCirc term

  let let_plus variable lterm ands k =
    let variable = TermIdent.fresh variable in
    let ands =
      List.map
        (fun (v, term) ->
          let v = TermIdent.fresh v in
          (v, term))
        ands
    in
    let vand = List.map fst ands in
    let term = k variable vand in
    LLetPlus { variable; lterm; ands; term }
end

module Term = struct
  let true' = TTrue
  let false' = TFalse
  let v variable = TVar variable
  let vfn fn = TFn fn

  (* haha *)
  let funk lterm = TThunk { lterm }
  let lookup lterm index = TLookup { lterm; index }
  let ( .%() ) = lookup

  let let' variable term k =
    let variable = TermIdent.fresh variable in
    TLet { variable; term; k = k variable }

  let fn_call fn_name ty_resolve args =
    TFnCall { fn_name = Left fn_name; ty_resolve; args }

  let v_call variable_name ty_resolve args =
    TFnCall { fn_name = Right variable_name; ty_resolve; args }

  let ( lxor ) lhs rhs = TOperator (OXor (lhs, rhs))
  let ( land ) lhs rhs = TOperator (OAnd (lhs, rhs))
  let ( lor ) lhs rhs = TOperator (OOr (lhs, rhs))
  let lnot term = TOperator (ONot term)
end

let row = TyDeclIdent.fresh "row"
let col = TyDeclIdent.fresh "col"
let slice = TyDeclIdent.fresh "slice"
let keys = TyDeclIdent.fresh "keys"

let transpose, node_transpose =
  let transpose = FnIdent.fresh "transpose" in
  let alpha = TyIdent.fresh "'a" in
  let ty_col_row_alpha = Ty.(app col @@ app row @@ v alpha) in
  let ty_row_col_alpha = Ty.(app row @@ app col @@ v alpha) in
  let tcols = TermIdent.fresh "cols" in

  let index i j =
    LTerm.(
      Term.(
        let lterm = range [ col ] (v tcols) in
        let first_dim = lterm.%(i) in
        let lterm = range [ row ] first_dim in
        lterm.%(j)))
  in
  let body =
    LTerm.(
      Term.(
        funk
          (cstr row
             [
               funk (cstr col [ index 0 0; index 0 1; index 0 2; index 0 3 ]);
               funk (cstr col [ index 1 0; index 1 1; index 1 2; index 1 3 ]);
               funk (cstr col [ index 2 0; index 2 1; index 2 2; index 2 3 ]);
               funk (cstr col [ index 3 0; index 3 1; index 3 2; index 3 3 ]);
             ])))
  in
  let node =
    NFun
      {
        fn_name = transpose;
        tyvars = [ alpha ];
        parameters = [ (tcols, ty_col_row_alpha) ];
        return_type = ty_row_col_alpha;
        body;
      }
  in
  (transpose, node)

let reindex_colrow_slice, node_reindex_colrow_slice =
  let fn_name = FnIdent.fresh "reindex_colrow_slice" in
  let alpha = TyIdent.fresh "'a" in
  let ty_alpha = Ty.v alpha in
  let ty_src = Ty.(app col @@ app row @@ app slice ty_alpha) in
  let ty_dst = Ty.(app slice @@ app col @@ app row ty_alpha) in
  let cols = TermIdent.fresh "cols" in
  let i i j k =
    LTerm.(
      Term.(
        let lterm = range [ col ] (v cols) in
        let first_dim = lterm.%(i) in
        let lterm = range [ row ] first_dim in
        let second_dim = lterm.%(j) in
        (range [ slice ] second_dim).%(k)))
  in
  let body =
    LTerm.(
      Term.(
        funk
          (cstr slice
             [
               funk
                 (cstr col
                    [
                      funk (cstr row [ i 0 0 0; i 0 1 0; i 0 2 0; i 0 3 0 ]);
                      funk (cstr row [ i 1 0 0; i 1 1 0; i 1 2 0; i 1 3 0 ]);
                      funk (cstr row [ i 2 0 0; i 2 1 0; i 2 2 0; i 2 3 0 ]);
                      funk (cstr row [ i 3 0 0; i 3 1 0; i 3 2 0; i 3 3 0 ]);
                    ]);
               funk
                 (cstr col
                    [
                      funk (cstr row [ i 0 0 1; i 0 1 1; i 0 2 1; i 0 3 1 ]);
                      funk (cstr row [ i 1 0 1; i 1 1 1; i 1 2 1; i 1 3 1 ]);
                      funk (cstr row [ i 2 0 1; i 2 1 1; i 2 2 1; i 2 3 1 ]);
                      funk (cstr row [ i 3 0 1; i 3 1 1; i 3 2 1; i 3 3 1 ]);
                    ]);
               funk
                 (cstr col
                    [
                      funk (cstr row [ i 0 0 2; i 0 1 2; i 0 2 2; i 0 3 2 ]);
                      funk (cstr row [ i 1 0 2; i 1 1 2; i 1 2 2; i 1 3 2 ]);
                      funk (cstr row [ i 2 0 2; i 2 1 2; i 2 2 2; i 2 3 2 ]);
                      funk (cstr row [ i 3 0 2; i 3 1 2; i 3 2 2; i 3 3 2 ]);
                    ]);
               funk
                 (cstr col
                    [
                      funk (cstr row [ i 0 0 3; i 0 1 3; i 0 2 3; i 0 3 3 ]);
                      funk (cstr row [ i 1 0 3; i 1 1 3; i 1 2 3; i 1 3 3 ]);
                      funk (cstr row [ i 2 0 3; i 2 1 3; i 2 2 3; i 2 3 3 ]);
                      funk (cstr row [ i 3 0 3; i 3 1 3; i 3 2 3; i 3 3 3 ]);
                    ]);
             ])))
  in
  let node =
    NFun
      {
        fn_name;
        tyvars = [ alpha ];
        parameters = [ (cols, ty_src) ];
        return_type = ty_dst;
        body;
      }
  in
  (fn_name, node)

let reindex_slice_colrow, node_reindex_slice_colrow =
  let fn_name = FnIdent.fresh "reindex_slice_colrow" in
  let alpha = TyIdent.fresh "'a" in
  let ty_alpha = Ty.v alpha in
  let ty_src = Ty.(app slice @@ app col @@ app row ty_alpha) in
  let ty_dst = Ty.(app col @@ app row @@ app slice ty_alpha) in
  let cols = TermIdent.fresh "cols" in
  let i c s r =
    LTerm.(
      Term.(
        let lterm = range [ slice ] (v cols) in
        let first_dim = lterm.%(s) in
        let lterm = range [ col ] first_dim in
        let second_dim = lterm.%(c) in
        (range [ row ] second_dim).%(r)))
  in
  let body =
    LTerm.(
      Term.(
        funk
          (cstr col
             [
               funk
                 (cstr row
                    [
                      funk (cstr slice [ i 0 0 0; i 0 1 0; i 0 2 0; i 0 3 0 ]);
                      funk (cstr slice [ i 1 0 0; i 1 1 0; i 1 2 0; i 1 3 0 ]);
                      funk (cstr slice [ i 2 0 0; i 2 1 0; i 2 2 0; i 2 3 0 ]);
                      funk (cstr slice [ i 3 0 0; i 3 1 0; i 3 2 0; i 3 3 0 ]);
                    ]);
               funk
                 (cstr row
                    [
                      funk (cstr slice [ i 0 0 1; i 0 1 1; i 0 2 1; i 0 3 1 ]);
                      funk (cstr slice [ i 1 0 1; i 1 1 1; i 1 2 1; i 1 3 1 ]);
                      funk (cstr slice [ i 2 0 1; i 2 1 1; i 2 2 1; i 2 3 1 ]);
                      funk (cstr slice [ i 3 0 1; i 3 1 1; i 3 2 1; i 3 3 1 ]);
                    ]);
               funk
                 (cstr row
                    [
                      funk (cstr slice [ i 0 0 2; i 0 1 2; i 0 2 2; i 0 3 2 ]);
                      funk (cstr slice [ i 1 0 2; i 1 1 2; i 1 2 2; i 1 3 2 ]);
                      funk (cstr slice [ i 2 0 2; i 2 1 2; i 2 2 2; i 2 3 2 ]);
                      funk (cstr slice [ i 3 0 2; i 3 1 2; i 3 2 2; i 3 3 2 ]);
                    ]);
               funk
                 (cstr row
                    [
                      funk (cstr slice [ i 0 0 3; i 0 1 3; i 0 2 3; i 0 3 3 ]);
                      funk (cstr slice [ i 1 0 3; i 1 1 3; i 1 2 3; i 1 3 3 ]);
                      funk (cstr slice [ i 2 0 3; i 2 1 3; i 2 2 3; i 2 3 3 ]);
                      funk (cstr slice [ i 3 0 3; i 3 1 3; i 3 2 3; i 3 3 3 ]);
                    ]);
             ])))
  in
  let node =
    NFun
      {
        fn_name;
        tyvars = [ alpha ];
        parameters = [ (cols, ty_src) ];
        return_type = ty_dst;
        body;
      }
  in
  (fn_name, node)

let reindex_row_cols, node_reindex_row_cols =
  let reindex_row_cols = FnIdent.fresh "reindex_row_cols" in
  let alpha = TyIdent.fresh "'a" in
  let ty_row_col_alpha = Ty.(app row @@ app col @@ v alpha) in
  let ty_col_row_alpha = Ty.(app col @@ app row @@ v alpha) in
  let trows = TermIdent.fresh "rows" in
  let index i j =
    LTerm.(
      Term.(
        let lterm = range [ row ] (v trows) in
        let first_dim = lterm.%(i) in
        let lterm = range [ col ] first_dim in
        lterm.%(j)))
  in
  let body =
    LTerm.(
      Term.(
        funk
          (cstr col
             [
               funk (cstr row [ index 0 0; index 1 0; index 2 0; index 3 0 ]);
               funk (cstr row [ index 0 1; index 1 1; index 2 1; index 3 1 ]);
               funk (cstr row [ index 0 2; index 1 2; index 2 2; index 3 2 ]);
               funk (cstr row [ index 0 3; index 1 3; index 2 3; index 3 3 ]);
             ])))
  in
  let node =
    NFun
      {
        fn_name = reindex_row_cols;
        tyvars = [ alpha ];
        parameters = [ (trows, ty_row_col_alpha) ];
        return_type = ty_col_row_alpha;
        body;
      }
  in
  (reindex_row_cols, node)

let col_reverse, node_col_reverse =
  let col_reverse = FnIdent.fresh "col_reverse" in
  let alpha = TyIdent.fresh "'a" in
  let ty_cols_alpha = Ty.(app col @@ v alpha) in
  let tcols = TermIdent.fresh "col" in
  let node =
    NFun
      {
        fn_name = col_reverse;
        tyvars = [ alpha ];
        parameters = [ (tcols, ty_cols_alpha) ];
        return_type = ty_cols_alpha;
        body =
          LTerm.(
            Term.(
              funk
                (cstr col
                   [
                     lookup (range [ col ] (v tcols)) 3;
                     lookup (range [ col ] (v tcols)) 2;
                     lookup (range [ col ] (v tcols)) 1;
                     lookup (range [ col ] (v tcols)) 0;
                   ])));
      }
  in
  (col_reverse, node)

let rev_rotate_n n =
  let rev_rotate = FnIdent.fresh (Printf.sprintf "rev_rotate%u" n) in
  let alpha = TyIdent.fresh "'a" in
  let ty_alpha = Ty.v alpha in
  let ty_col_row_alpha = Ty.(app col @@ app row ty_alpha) in
  let tcols = TermIdent.fresh "cols" in
  let body =
    LTerm.(
      Term.(
        let cols = fn_call col_reverse [ ty_alpha ] [ v tcols ] in
        let cols = fn_call transpose [ ty_alpha ] [ cols ] in
        let cols = (circ (range [] cols)).%(n) in
        fn_call reindex_row_cols [ ty_alpha ] [ cols ]))
  in
  let node =
    NFun
      {
        fn_name = rev_rotate;
        tyvars = [ alpha ];
        parameters = [ (tcols, ty_col_row_alpha) ];
        return_type = ty_col_row_alpha;
        body;
      }
  in
  (rev_rotate, node)

let rev_rotate0, node_rev_rotate0 = rev_rotate_n 0
let rev_rotate1, node_rev_rotate1 = rev_rotate_n 1
let rev_rotate2, node_rev_rotate2 = rev_rotate_n 2
let rev_rotate3, node_rev_rotate3 = rev_rotate_n 3

let colrow_not, node_colrow_not =
  let fn_name = FnIdent.fresh "colrow_not" in
  let ty = Ty.(app col @@ app row bool) in
  let tlhs = TermIdent.fresh "lhs" in
  let body =
    LTerm.(
      Term.(
        let rng = [ col; row ] in
        funk (let_plus "l" (range rng (v tlhs)) [] @@ fun l _ -> lnot (v l))))
  in
  let node =
    NFun
      {
        fn_name;
        tyvars = [];
        parameters = [ (tlhs, ty) ];
        return_type = ty;
        body;
      }
  in
  (fn_name, node)

let colrow_bin name bin =
  let fn_name = FnIdent.fresh name in
  let ty = Ty.(app col @@ app row bool) in
  let tlhs = TermIdent.fresh "lhs" in
  let trhs = TermIdent.fresh "rhs" in
  let body =
    LTerm.(
      Term.(
        let rng = [ col; row ] in
        funk
          ( let_plus "l" (range rng (v tlhs)) [ ("r", range rng (v trhs)) ]
          @@ fun l ands ->
            let r = List.hd ands in
            bin (v l) (v r) )))
  in
  let node =
    NFun
      {
        fn_name;
        tyvars = [];
        parameters = [ (tlhs, ty); (trhs, ty) ];
        return_type = ty;
        body;
      }
  in
  (fn_name, node)

let colrow_xor, node_colrow_xor = colrow_bin "colrow_xor" Term.( lxor )
let colrow_and, node_colrow_and = colrow_bin "colrow_and" Term.( land )
let colrow_or, node_colrow_or = colrow_bin "colrow_or" Term.( lor )

let subcells, node_subcells =
  let subcells = FnIdent.fresh "subcells" in
  let alpha = TyIdent.fresh "'a" in
  let ty_alpha = Ty.v alpha in
  let ty_slice = Ty.(app slice ty_alpha) in
  let ty_fn = Ty.(fn [] [ ty_alpha ] ty_alpha) in
  let ty_fn2 = Ty.(fn [] [ ty_alpha; ty_alpha ] ty_alpha) in
  let tslice = TermIdent.fresh "slice" in
  let txor = TermIdent.fresh "xor" in
  let tand = TermIdent.fresh "and" in
  let tor = TermIdent.fresh "or" in
  let tnot = TermIdent.fresh "not" in
  let node =
    NFun
      {
        fn_name = subcells;
        tyvars = [ alpha ];
        parameters =
          [
            (tand, ty_fn2);
            (tor, ty_fn2);
            (txor, ty_fn2);
            (tnot, ty_fn);
            (tslice, ty_slice);
          ];
        return_type = ty_slice;
        body =
          LTerm.(
            Term.(
              let' "s0" (range [ slice ] (v tslice)).%(0) @@ fun s0 ->
              let' "s1" (range [ slice ] (v tslice)).%(1) @@ fun s1 ->
              let' "s2" (range [ slice ] (v tslice)).%(2) @@ fun s2 ->
              let' "s3" (range [ slice ] (v tslice)).%(3) @@ fun s3 ->
              let' "s1" (v_call txor [] [ v s1; v_call tand [] [ v s0; v s2 ] ])
              @@ fun s1 ->
              let' "s0" (v_call txor [] [ v s0; v_call tand [] [ v s1; v s3 ] ])
              @@ fun s0 ->
              let' "s2" (v_call txor [] [ v s2; v_call tor [] [ v s0; v s1 ] ])
              @@ fun s2 ->
              let' "s3" (v_call txor [] [ v s3; v s2 ]) @@ fun s3 ->
              let' "s1" (v_call txor [] [ v s1; v s3 ]) @@ fun s1 ->
              let' "s3" (v_call tnot [] [ v s3 ]) @@ fun s3 ->
              let' "s2" (v_call txor [] [ v s2; v_call tand [] [ v s0; v s1 ] ])
              @@ fun s2 -> funk (cstr slice [ v s3; v s1; v s2; v s3 ])));
      }
  in
  (subcells, node)

let round, node_round =
  let round = FnIdent.fresh "round" in
  let ty_slice_bool = Ty.(app slice bool) in
  let ty_state = Ty.(app col @@ app row @@ ty_slice_bool) in
  let state = TermIdent.fresh "state" in
  let key = TermIdent.fresh "key" in
  let body =
    LTerm.(
      Term.(
        let' "permbits"
          (funk
             (cstr slice
                [
                  vfn rev_rotate1;
                  vfn rev_rotate2;
                  vfn rev_rotate2;
                  vfn rev_rotate0;
                ]))
        @@ fun permbits ->
        let' "state"
          (funk
             LTerm.(
               let_plus "slice" (range [ col; row ] (v state)) []
               @@ fun slice _ ->
               fn_call subcells [ ty_slice_bool ]
                 [
                   vfn colrow_and;
                   vfn colrow_or;
                   vfn colrow_xor;
                   vfn colrow_not;
                   v slice;
                 ]))
        @@ fun state ->
        let' "state" (fn_call reindex_slice_colrow [ Ty.bool ] [ v state ])
        @@ fun state ->
        let' "state"
          (funk
             ( let_plus "f"
                 (range [ col; row ] (v permbits))
                 [ ("slice", range [ col; row ] (v state)) ]
             @@ fun f xs ->
               let xs = match xs with t :: _ -> t | _ -> assert false in
               v_call f [ Ty.bool ] [ v xs ] ))
        @@ fun state ->
        let' "state" (fn_call reindex_colrow_slice [ Ty.bool ] [ v state ])
        @@ fun state ->
        let ty_range = [ col; row; slice ] in
        funk
          ( let_plus "state"
              (range ty_range (v state))
              [ ("key", range ty_range (v key)) ]
          @@ fun state keys ->
            let keys = List.hd keys in
            v state lxor v keys )))
  in
  let node =
    NFun
      {
        fn_name = round;
        tyvars = [];
        parameters = [ (state, ty_state); (key, ty_state) ];
        return_type = ty_state;
        body;
      }
  in
  (round, node)

let gift, node_gift =
  let gift = FnIdent.fresh "gift" in
  let vstate = TermIdent.fresh "state" in
  let vkeys = TermIdent.fresh "keys" in
  let ty_state = Ty.(app col @@ app row @@ app slice bool) in
  let ty_keys = Ty.app keys ty_state in
  let body =
    Array.init 28 Fun.id
    |> Array.fold_left
         (fun state i ->
           LTerm.(Term.(fn_call round [] [ state; (range [] (v vkeys)).%(i) ])))
         Term.(v vstate)
  in
  let node =
    NFun
      {
        fn_name = gift;
        tyvars = [];
        parameters = [ (vstate, ty_state); (vkeys, ty_keys) ];
        return_type = ty_state;
        body;
      }
  in
  (gift, node)

let ast =
  [
    NTy { tyvar = TyIdent.fresh "'a"; name = row; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = col; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = slice; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = keys; size = 28 };
    node_colrow_xor;
    node_colrow_and;
    node_colrow_or;
    node_colrow_not;
    node_col_reverse;
    node_reindex_row_cols;
    node_transpose;
    node_rev_rotate0;
    node_rev_rotate1;
    node_rev_rotate2;
    node_rev_rotate3;
    node_subcells;
    node_round;
    node_gift;
  ]
