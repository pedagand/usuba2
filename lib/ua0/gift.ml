open Ast

module Ty = struct
  let bool = TyBool
  let v v = TyVar v
  let app name ty = TyApp { name; ty }
  let tuple size ty = TyTuple { size; ty }

  let fn tyvars parameters return_type =
    TyFun { tyvars; parameters; return_type }
end

module LTerm = struct
  let range ty term = LRange { ty; term }
  let cstr ty terms = LConstructor { ty; terms }

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

  (* haha *)
  let funk lterm = TThunk { lterm }
  let lookup lterm index = TLookup { lterm; index }
  let ( .%() ) = lookup

  let let' variable term k =
    let variable = TermIdent.fresh variable in
    TLet { variable; term; k = k variable }

  let fn_call fn_name ty_resolve args =
    TFnCall { fn_name = Left fn_name; ty_resolve; args }
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

let subcells, node_subcells =
  let subcells = FnIdent.fresh "subcell" in
  let alpha = TyIdent.fresh "'a" in
  let ty_slice = Ty.(app slice @@ v alpha) in
  let tslice = TermIdent.fresh "slice" in
  let node =
    NFun
      {
        fn_name = subcells;
        tyvars = [ alpha ];
        parameters = [ (tslice, ty_slice) ];
        return_type = ty_slice;
        body =
          LTerm.(
            Term.(
              let' "s0" (range [ slice ] (v tslice)).%(0) @@ fun _s0 ->
              let' "s1" (range [ slice ] (v tslice)).%(1) @@ fun _s1 ->
              let' "s2" (range [ slice ] (v tslice)).%(2) @@ fun _s2 ->
              let' "s3" (range [ slice ] (v tslice)).%(3) @@ fun _s3 ->
              failwith ""));
      }
  in
  (subcells, node)

let round, node_round =
  let round = FnIdent.fresh "gift" in
  let ty_slice_bool = Ty.(app slice bool) in
  let ty_state = Ty.(app col @@ app row @@ ty_slice_bool) in
  let state = TermIdent.fresh "state" in
  let key = TermIdent.fresh "key" in
  let node =
    NFun
      {
        fn_name = round;
        tyvars = [];
        parameters = [ (state, ty_state); (key, ty_state) ];
        return_type = ty_state;
        body =
          Term.(
            let' "state"
              (funk
                 LTerm.(
                   let_plus "slice" (range [ col; row ] (v state)) []
                   @@ fun slice _ ->
                   fn_call subcells [ ty_slice_bool ] [ v slice ]))
            @@ fun _state -> failwith "");
      }
  in
  (round, node)

let ast =
  [
    NTy { tyvar = TyIdent.fresh "'a"; name = row; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = col; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = slice; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = keys; size = 28 };
    node_col_reverse;
    node_transpose;
    node_subcells;
    node_round;
  ]
