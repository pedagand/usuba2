open Ast

module Ty = struct
  let bool = TyBool
  let eapp name = TyApp { name; ty_args = None }
  let app name ty_args = TyApp { name; ty_args = Some ty_args }
  let tuple size ty = TyTuple { size; ty }

  let fn ty_vars parameters return_type =
    TyFun { ty_vars; parameters; return_type }

  let v name = TyVarApp { name; ty_args = None }
  let varapp name ty_args = TyVarApp { name; ty_args = Some ty_args }
end

module Expression = struct
  let true' = ETrue
  let false' = EFalse

  let e_indexing expression slice index =
    EIndexing { expression; indexing = { name = slice; index } }

  let indexing s slice index = e_indexing (EVar s) slice index
  let builin_call builtin ty_args args = EBuiltinCall { builtin; ty_args; args }

  let fn_call fn_name ty_args args =
    EFunctionCall { fn_name = Left fn_name; ty_args; args }

  let term_call fn_name ty_args args =
    EFunctionCall { fn_name = Right fn_name; ty_args; args }

  let ( land ) lhs rhs = EOp (BAnd (lhs, rhs))
  let ( lor ) lhs rhs = EOp (BOr (lhs, rhs))
  let ( lxor ) lhs rhs = EOp (BXor (lhs, rhs))

  let ( |> ) e ty_args fn_name =
    EFunctionCall { fn_name = Either.left fn_name; ty_args; args = [ e ] }

  let let_plus variable ty_arg ty_ret expression ands k =
    let variable = TermIdent.fresh variable in
    let ands =
      List.map
        (fun (variable, expression) ->
          let variable = TermIdent.fresh variable in
          (variable, expression))
        ands
    in
    let statements, expression' = k variable (List.map fst ands) in
    SLetPLus
      {
        variable;
        ty_arg;
        ty_ret;
        expression;
        ands;
        body = { statements; expression = expression' };
      }

  let lnot expr = EOp (Unot expr)
  let v s = EVar s
  let fv s = EFunVar (s, None)
  let fv_t s tys = EFunVar (s, Some tys)
  let vars idents = List.map v idents
end

module Statement = struct
  let decl variable expression k =
    let variable = TermIdent.fresh variable in
    let statements, finale = k variable in
    (StDeclaration { variable; expression } :: statements, finale)

  let cstr variable ty expressions k =
    let variable = TermIdent.fresh variable in
    let statements, finale = k variable in
    (StConstructor { variable; ty; expressions } :: statements, finale)

  let log message variables k =
    let statements, finale = k () in
    (StLog { message; variables } :: statements, finale)
end

let app = FnIdent.fresh "app"
let map2 = FnIdent.fresh "map2"
let map = FnIdent.fresh "map"
let row = TyDeclIdent.fresh "row"
let col = TyDeclIdent.fresh "col"
let keys = TyDeclIdent.fresh "keys"
let slice = TyDeclIdent.fresh "slice"
let state = TyDeclIdent.fresh "state"
let subcells = FnIdent.fresh "subcells"
let add_round_key = FnIdent.fresh "add_round_key"
let transpose = FnIdent.fresh "transpose"
let reindex_cols_row = FnIdent.fresh "reindex_cols_row"
let reindex_rowcol_slice = FnIdent.fresh "reindex_rowcol_slice"
let reindex_slice_rowcol = FnIdent.fresh "reindex_slice_rowcol"
let col_reverse = FnIdent.fresh "col_reverse"
let rev_rotate_0 = FnIdent.fresh "rev_rotate_0"
let rev_rotate_1 = FnIdent.fresh "rev_rotate_1"
let rev_rotate_2 = FnIdent.fresh "rev_rotate_2"
let rev_rotate_3 = FnIdent.fresh "rev_rotate_3"
let permbits = FnIdent.fresh "permbits"
let row_ror_0 = FnIdent.fresh "row_ror_0"
let row_ror_1 = FnIdent.fresh "row_ror_1"
let row_ror_2 = FnIdent.fresh "row_ror_2"
let row_ror_3 = FnIdent.fresh "row_ror_3"
let fxor = FnIdent.fresh "fxor"
let round = FnIdent.fresh "round"
let fngift = FnIdent.fresh "gift"

let gift =
  [
    (let alpha = TyIdent.fresh "'a" in
     KnTypedecl
       {
         ty_vars = [ alpha ];
         ty_name = row;
         definition = TyTuple { size = 4; ty = Ty.v alpha };
       });
    (let alpha = TyIdent.fresh "'a" in
     KnTypedecl
       {
         ty_vars = [ alpha ];
         ty_name = col;
         definition = Ty.(tuple 4 (v alpha));
       });
    (let alpha = TyIdent.fresh "'a" in
     KnTypedecl
       {
         ty_vars = [ alpha ];
         ty_name = slice;
         definition = TyTuple { size = 4; ty = Ty.v alpha };
       });
    KnTypedecl
      {
        ty_vars = [];
        ty_name = state;
        definition = Ty.(app col (app row (app slice bool)));
      };
    KnTypedecl
      { ty_vars = []; ty_name = keys; definition = Ty.(tuple 28 @@ eapp state) };
    (let alpha = TyIdent.fresh "'a" in
     let beta = TyIdent.fresh "'b" in
     let ctrl = TyIdent.fresh "#t" in
     let ty_alpha = Ty.(v alpha) in
     let ty_beta = Ty.(v beta) in
     let ty_fn = Ty.(fn [] [ ty_alpha ] ty_beta) in
     let ty_ctrl_fn = Ty.(varapp ctrl ty_fn) in
     let ty_ctrl_alpha = Ty.(varapp ctrl ty_alpha) in
     let ty_ctrl_beta = Ty.(varapp ctrl ty_beta) in
     let fs = TermIdent.fresh "fs" in
     let xs = TermIdent.fresh "xs" in
     let expression =
       Expression.let_plus "f"
         Ty.(v ctrl)
         ty_beta
         Expression.(v fs)
         Expression.[ ("x", v xs) ]
       @@ fun f ands ->
       let x = match ands with [] -> assert false | x :: _ -> x in
       ([], Expression.(term_call f [] [ v x ]))
     in
     KnFundecl
       {
         fn_name = app;
         ty_vars =
           [ (ctrl, KArrow (KType, KType)); (alpha, KType); (beta, KType) ];
         parameters = [ (fs, ty_ctrl_fn); (xs, ty_ctrl_alpha) ];
         return_type = ty_ctrl_beta;
         body = { statements = []; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let beta = TyIdent.fresh "'b" in
     let ctrl = TyIdent.fresh "#t" in
     let ty_alpha = Ty.(v alpha) in
     let ty_beta = Ty.(v beta) in
     let ty_ctrl_alpha = Ty.(varapp ctrl ty_alpha) in
     let ty_ctrl_beta = Ty.(varapp ctrl ty_beta) in
     let ty_fn = Ty.(fn [] [ ty_alpha ] ty_beta) in
     let f = TermIdent.fresh "f" in
     let xs = TermIdent.fresh "xs" in
     let expression =
       Expression.let_plus "x" Ty.(v ctrl) ty_beta Expression.(v xs) []
       @@ fun x _ -> ([], Expression.term_call f [] Expression.[ v x ])
     in
     KnFundecl
       {
         fn_name = map;
         ty_vars =
           [ (ctrl, KArrow (KType, KType)); (alpha, KType); (beta, KType) ];
         parameters = [ (f, ty_fn); (xs, ty_ctrl_alpha) ];
         return_type = ty_ctrl_beta;
         body = { statements = []; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let beta = TyIdent.fresh "'b" in
     let charly = TyIdent.fresh "'c" in
     let ctrl = TyIdent.fresh "#t" in
     let ty_alpha = Ty.(v alpha) in
     let ty_beta = Ty.(v beta) in
     let ty_charly = Ty.(v charly) in
     let ty_ctrl_alpha = Ty.(varapp ctrl ty_alpha) in
     let ty_ctrl_beta = Ty.(varapp ctrl ty_beta) in
     let ty_ctrl_charly = Ty.(varapp ctrl ty_charly) in
     let ty_fn = Ty.(fn [] [ ty_alpha; ty_beta ] ty_charly) in
     let f = TermIdent.fresh "f" in
     let xs = TermIdent.fresh "xs" in
     let ys = TermIdent.fresh "ys" in
     let expression =
       Expression.let_plus "x"
         Ty.(v ctrl)
         ty_charly
         Expression.(v xs)
         Expression.[ ("y", v ys) ]
       @@ fun x ands ->
       let y = match ands with [] -> assert false | t :: _ -> t in
       ([], Expression.term_call f [] Expression.[ v x; v y ])
     in
     KnFundecl
       {
         fn_name = map2;
         ty_vars =
           [
             (ctrl, KArrow (KType, KType));
             (alpha, KType);
             (beta, KType);
             (charly, KType);
           ];
         parameters = [ (f, ty_fn); (xs, ty_ctrl_alpha); (ys, ty_ctrl_beta) ];
         return_type = ty_ctrl_charly;
         body = { statements = []; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let lhs = TermIdent.fresh "lhs" in
     let rhs = TermIdent.fresh "rhs" in
     KnFundecl
       {
         fn_name = fxor;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (lhs, ty_alpha); (rhs, ty_alpha) ];
         return_type = ty_alpha;
         body = { statements = []; expression = Expression.(v lhs lxor v rhs) };
       });
    (let s = TermIdent.fresh "s" in
     let alpha = TyIdent.fresh "'a" in
     let ty_slice = Ty.(app slice (v alpha)) in
     let statements, expression =
       Statement.decl "s0" (Expression.indexing s slice 0) @@ fun s0 ->
       Statement.decl "s1" (Expression.indexing s slice 1) @@ fun s1 ->
       Statement.decl "s2" (Expression.indexing s slice 2) @@ fun s2 ->
       Statement.decl "s3" (Expression.indexing s slice 3) @@ fun s3 ->
       Statement.decl "s1" Expression.(v s1 lxor (v s0 land v s2)) @@ fun s1 ->
       Statement.decl "s0" Expression.(v s0 lxor (v s1 land v s3)) @@ fun s0 ->
       Statement.decl "s2" Expression.(v s2 lxor (v s0 lor v s1)) @@ fun s2 ->
       Statement.decl "s3" Expression.(v s3 lxor v s2) @@ fun s3 ->
       Statement.decl "s1" Expression.(v s1 lxor v s3) @@ fun s1 ->
       Statement.decl "s3" Expression.(lnot (v s3)) @@ fun s3 ->
       Statement.decl "s2" Expression.(v s2 lxor (v s0 land v s1)) @@ fun s2 ->
       Statement.cstr "s" ty_slice Expression.[ v s3; v s1; v s2; v s0 ]
       @@ fun s -> ([], Expression.v s)
     in
     KnFundecl
       {
         fn_name = subcells;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (s, ty_slice) ];
         return_type = ty_slice;
         body = { statements; expression };
       });
    (let s = TermIdent.fresh "s" in
     let key = TermIdent.fresh "key" in
     let alpha = TyIdent.fresh "'a" in
     (* let ty_alpha = Ty.(v alpha) in *)
     let ty_slice = Ty.(app slice (v alpha)) in
     let statements, expression = ([], Expression.(v s lxor v key)) in
     KnFundecl
       {
         fn_name = add_round_key;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (s, ty_slice); (key, ty_slice) ];
         return_type = ty_slice;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_col_alpha = Ty.(app col ty_alpha) in
     let ty_cols_rows = Ty.(app col (app row ty_alpha)) in
     let ty_rows_cols = Ty.(app row ty_col_alpha) in
     let state = TermIdent.fresh "s" in
     let index icol irow =
       Expression.(e_indexing (indexing state col icol) row irow)
     in
     let statements, expression =
       Statement.cstr "c0" ty_col_alpha
         [ index 0 0; index 0 1; index 0 2; index 0 3 ]
       @@ fun c0 ->
       Statement.cstr "c1" ty_col_alpha
         [ index 1 0; index 1 1; index 1 2; index 1 3 ]
       @@ fun c1 ->
       Statement.cstr "c2" ty_col_alpha
         [ index 2 0; index 2 1; index 2 2; index 2 3 ]
       @@ fun c2 ->
       Statement.cstr "c3" ty_col_alpha
         [ index 3 0; index 3 1; index 3 2; index 3 3 ]
       @@ fun c3 ->
       Statement.cstr "r" ty_rows_cols Expression.(vars [ c0; c1; c2; c3 ])
       @@ fun r -> ([], Expression.v r)
     in
     KnFundecl
       {
         fn_name = transpose;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (state, ty_cols_rows) ];
         return_type = ty_rows_cols;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_row_alpha = Ty.(app row ty_alpha) in
     let ty_row_cols = Ty.(app row (app col ty_alpha)) in
     let ty_col_rows = Ty.(app col ty_row_alpha) in
     let state = TermIdent.fresh "s" in
     let index icol irow =
       Expression.(e_indexing (indexing state row irow) col icol)
     in
     let statements, expression =
       Statement.cstr "r0" ty_row_alpha
         [ index 0 0; index 0 1; index 0 2; index 0 3 ]
       @@ fun r0 ->
       Statement.cstr "r1" ty_row_alpha
         [ index 1 0; index 1 1; index 1 2; index 1 3 ]
       @@ fun r1 ->
       Statement.cstr "r2" ty_row_alpha
         [ index 2 0; index 2 1; index 2 2; index 2 3 ]
       @@ fun r2 ->
       Statement.cstr "r3" ty_row_alpha
         [ index 3 0; index 3 1; index 3 2; index 3 3 ]
       @@ fun r3 ->
       Statement.cstr "c" ty_col_rows Expression.(vars [ r0; r1; r2; r3 ])
       @@ fun c -> ([], Expression.v c)
     in
     KnFundecl
       {
         fn_name = reindex_cols_row;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (state, ty_row_cols) ];
         return_type = ty_col_rows;
         body = { statements; expression };
       });
    (let colsrow = TermIdent.fresh "colsrow" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_slice = Ty.app slice ty_alpha in
     let ty_row_alpha = Ty.(app row @@ ty_alpha) in
     let ty_col_row = Ty.(app col @@ app row ty_alpha) in
     let ty_col_row_slice_a = Ty.(app col @@ app row @@ ty_slice) in
     let ty_slice_col_row_a = Ty.(app slice @@ app col @@ app row ty_alpha) in
     let index irow icol islice =
       Expression.(
         e_indexing
           (e_indexing (indexing colsrow col icol) row irow)
           slice islice)
     in
     let statements, expression =
       Statement.decl "b0" (index 0 0 0) @@ fun b0 ->
       Statement.decl "b1" (index 0 0 1) @@ fun b1 ->
       Statement.decl "b2" (index 0 0 2) @@ fun b2 ->
       Statement.decl "b3" (index 0 0 3) @@ fun b3 ->
       Statement.decl "b4" (index 0 1 0) @@ fun b4 ->
       Statement.decl "b5" (index 0 1 1) @@ fun b5 ->
       Statement.decl "b6" (index 0 1 2) @@ fun b6 ->
       Statement.decl "b7" (index 0 1 3) @@ fun b7 ->
       Statement.decl "b8" (index 0 2 0) @@ fun b8 ->
       Statement.decl "b9" (index 0 2 1) @@ fun b9 ->
       Statement.decl "b10" (index 0 2 2) @@ fun b10 ->
       Statement.decl "b11" (index 0 2 3) @@ fun b11 ->
       Statement.decl "b12" (index 0 3 0) @@ fun b12 ->
       Statement.decl "b13" (index 0 3 1) @@ fun b13 ->
       Statement.decl "b14" (index 0 3 2) @@ fun b14 ->
       Statement.decl "b15" (index 0 3 3) @@ fun b15 ->
       Statement.decl "b16" (index 1 0 0) @@ fun b16 ->
       Statement.decl "b17" (index 1 0 1) @@ fun b17 ->
       Statement.decl "b18" (index 1 0 2) @@ fun b18 ->
       Statement.decl "b19" (index 1 0 3) @@ fun b19 ->
       Statement.decl "b20" (index 1 1 0) @@ fun b20 ->
       Statement.decl "b21" (index 1 1 1) @@ fun b21 ->
       Statement.decl "b22" (index 1 1 2) @@ fun b22 ->
       Statement.decl "b23" (index 1 1 3) @@ fun b23 ->
       Statement.decl "b24" (index 1 2 0) @@ fun b24 ->
       Statement.decl "b25" (index 1 2 1) @@ fun b25 ->
       Statement.decl "b26" (index 1 2 2) @@ fun b26 ->
       Statement.decl "b27" (index 1 2 3) @@ fun b27 ->
       Statement.decl "b28" (index 1 3 0) @@ fun b28 ->
       Statement.decl "b29" (index 1 3 1) @@ fun b29 ->
       Statement.decl "b30" (index 1 3 2) @@ fun b30 ->
       Statement.decl "b31" (index 1 3 3) @@ fun b31 ->
       Statement.decl "b32" (index 2 0 0) @@ fun b32 ->
       Statement.decl "b33" (index 2 0 1) @@ fun b33 ->
       Statement.decl "b34" (index 2 0 2) @@ fun b34 ->
       Statement.decl "b35" (index 2 0 3) @@ fun b35 ->
       Statement.decl "b36" (index 2 1 0) @@ fun b36 ->
       Statement.decl "b37" (index 2 1 1) @@ fun b37 ->
       Statement.decl "b38" (index 2 1 2) @@ fun b38 ->
       Statement.decl "b39" (index 2 1 3) @@ fun b39 ->
       Statement.decl "b40" (index 2 2 0) @@ fun b40 ->
       Statement.decl "b41" (index 2 2 1) @@ fun b41 ->
       Statement.decl "b42" (index 2 2 2) @@ fun b42 ->
       Statement.decl "b43" (index 2 2 3) @@ fun b43 ->
       Statement.decl "b44" (index 2 3 0) @@ fun b44 ->
       Statement.decl "b45" (index 2 3 1) @@ fun b45 ->
       Statement.decl "b46" (index 2 3 2) @@ fun b46 ->
       Statement.decl "b47" (index 2 3 3) @@ fun b47 ->
       Statement.decl "b48" (index 3 0 0) @@ fun b48 ->
       Statement.decl "b49" (index 3 0 1) @@ fun b49 ->
       Statement.decl "b50" (index 3 0 2) @@ fun b50 ->
       Statement.decl "b51" (index 3 0 3) @@ fun b51 ->
       Statement.decl "b52" (index 3 1 0) @@ fun b52 ->
       Statement.decl "b53" (index 3 1 1) @@ fun b53 ->
       Statement.decl "b54" (index 3 1 2) @@ fun b54 ->
       Statement.decl "b55" (index 3 1 3) @@ fun b55 ->
       Statement.decl "b56" (index 3 2 0) @@ fun b56 ->
       Statement.decl "b57" (index 3 2 1) @@ fun b57 ->
       Statement.decl "b58" (index 3 2 2) @@ fun b58 ->
       Statement.decl "b59" (index 3 2 3) @@ fun b59 ->
       Statement.decl "b60" (index 3 3 0) @@ fun b60 ->
       Statement.decl "b61" (index 3 3 1) @@ fun b61 ->
       Statement.decl "b62" (index 3 3 2) @@ fun b62 ->
       Statement.decl "b63" (index 3 3 3) @@ fun b63 ->
       Statement.cstr "c0" ty_row_alpha Expression.[ v b0; v b16; v b32; v b48 ]
       @@ fun c0 ->
       Statement.cstr "c1" ty_row_alpha Expression.[ v b4; v b20; v b36; v b52 ]
       @@ fun c1 ->
       Statement.cstr "c2" ty_row_alpha Expression.[ v b8; v b24; v b40; v b56 ]
       @@ fun c2 ->
       Statement.cstr "c3" ty_row_alpha
         Expression.[ v b12; v b28; v b44; v b60 ]
       @@ fun c3 ->
       Statement.cstr "c4" ty_row_alpha Expression.[ v b1; v b17; v b33; v b49 ]
       @@ fun c4 ->
       Statement.cstr "c5" ty_row_alpha Expression.[ v b5; v b21; v b37; v b53 ]
       @@ fun c5 ->
       Statement.cstr "c6" ty_row_alpha Expression.[ v b9; v b25; v b41; v b57 ]
       @@ fun c6 ->
       Statement.cstr "c7" ty_row_alpha
         Expression.[ v b13; v b29; v b45; v b61 ]
       @@ fun c7 ->
       Statement.cstr "c8" ty_row_alpha Expression.[ v b2; v b18; v b34; v b50 ]
       @@ fun c8 ->
       Statement.cstr "c9" ty_row_alpha Expression.[ v b6; v b22; v b38; v b54 ]
       @@ fun c9 ->
       Statement.cstr "c10" ty_row_alpha
         Expression.[ v b10; v b26; v b42; v b58 ]
       @@ fun c10 ->
       Statement.cstr "c11" ty_row_alpha
         Expression.[ v b14; v b30; v b46; v b62 ]
       @@ fun c11 ->
       Statement.cstr "c12" ty_row_alpha
         Expression.[ v b3; v b19; v b35; v b51 ]
       @@ fun c12 ->
       Statement.cstr "c13" ty_row_alpha
         Expression.[ v b7; v b23; v b39; v b55 ]
       @@ fun c13 ->
       Statement.cstr "c14" ty_row_alpha
         Expression.[ v b11; v b27; v b43; v b59 ]
       @@ fun c14 ->
       Statement.cstr "c15" ty_row_alpha
         Expression.[ v b15; v b31; v b47; v b63 ]
       @@ fun c15 ->
       Statement.cstr "s0" ty_col_row Expression.[ v c0; v c1; v c2; v c3 ]
       @@ fun s0 ->
       Statement.cstr "s1" ty_col_row Expression.[ v c4; v c5; v c6; v c7 ]
       @@ fun s1 ->
       Statement.cstr "s2" ty_col_row Expression.[ v c8; v c9; v c10; v c11 ]
       @@ fun s2 ->
       Statement.cstr "s3" ty_col_row Expression.[ v c12; v c13; v c14; v c15 ]
       @@ fun s3 ->
       Statement.cstr "slice" ty_slice_col_row_a
         Expression.[ v s0; v s1; v s2; v s3 ]
       @@ fun slice -> ([], Expression.v slice)
     in

     KnFundecl
       {
         fn_name = reindex_rowcol_slice;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (colsrow, ty_col_row_slice_a) ];
         return_type = ty_slice_col_row_a;
         body = { statements; expression };
       });
    (let slice' = TermIdent.fresh "slice" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_slice_alpha = Ty.(app slice ty_alpha) in
     let ty_row_slice_alpha = Ty.(app row ty_slice_alpha) in
     let ty_col_row_slice_a = Ty.(app col @@ app row @@ app slice ty_alpha) in
     let ty_slice_col_row_a = Ty.(app slice @@ app col @@ app row ty_alpha) in
     let index irow icol islice =
       Expression.(
         e_indexing
           (e_indexing (indexing slice' slice islice) col icol)
           row irow)
     in
     let statements, expression =
       Statement.decl "b0" (index 0 0 0) @@ fun b0 ->
       Statement.decl "b1" (index 0 0 1) @@ fun b1 ->
       Statement.decl "b2" (index 0 0 2) @@ fun b2 ->
       Statement.decl "b3" (index 0 0 3) @@ fun b3 ->
       Statement.decl "b4" (index 0 1 0) @@ fun b4 ->
       Statement.decl "b5" (index 0 1 1) @@ fun b5 ->
       Statement.decl "b6" (index 0 1 2) @@ fun b6 ->
       Statement.decl "b7" (index 0 1 3) @@ fun b7 ->
       Statement.decl "b8" (index 0 2 0) @@ fun b8 ->
       Statement.decl "b9" (index 0 2 1) @@ fun b9 ->
       Statement.decl "b10" (index 0 2 2) @@ fun b10 ->
       Statement.decl "b11" (index 0 2 3) @@ fun b11 ->
       Statement.decl "b12" (index 0 3 0) @@ fun b12 ->
       Statement.decl "b13" (index 0 3 1) @@ fun b13 ->
       Statement.decl "b14" (index 0 3 2) @@ fun b14 ->
       Statement.decl "b15" (index 0 3 3) @@ fun b15 ->
       Statement.decl "b16" (index 1 0 0) @@ fun b16 ->
       Statement.decl "b17" (index 1 0 1) @@ fun b17 ->
       Statement.decl "b18" (index 1 0 2) @@ fun b18 ->
       Statement.decl "b19" (index 1 0 3) @@ fun b19 ->
       Statement.decl "b20" (index 1 1 0) @@ fun b20 ->
       Statement.decl "b21" (index 1 1 1) @@ fun b21 ->
       Statement.decl "b22" (index 1 1 2) @@ fun b22 ->
       Statement.decl "b23" (index 1 1 3) @@ fun b23 ->
       Statement.decl "b24" (index 1 2 0) @@ fun b24 ->
       Statement.decl "b25" (index 1 2 1) @@ fun b25 ->
       Statement.decl "b26" (index 1 2 2) @@ fun b26 ->
       Statement.decl "b27" (index 1 2 3) @@ fun b27 ->
       Statement.decl "b28" (index 1 3 0) @@ fun b28 ->
       Statement.decl "b29" (index 1 3 1) @@ fun b29 ->
       Statement.decl "b30" (index 1 3 2) @@ fun b30 ->
       Statement.decl "b31" (index 1 3 3) @@ fun b31 ->
       Statement.decl "b32" (index 2 0 0) @@ fun b32 ->
       Statement.decl "b33" (index 2 0 1) @@ fun b33 ->
       Statement.decl "b34" (index 2 0 2) @@ fun b34 ->
       Statement.decl "b35" (index 2 0 3) @@ fun b35 ->
       Statement.decl "b36" (index 2 1 0) @@ fun b36 ->
       Statement.decl "b37" (index 2 1 1) @@ fun b37 ->
       Statement.decl "b38" (index 2 1 2) @@ fun b38 ->
       Statement.decl "b39" (index 2 1 3) @@ fun b39 ->
       Statement.decl "b40" (index 2 2 0) @@ fun b40 ->
       Statement.decl "b41" (index 2 2 1) @@ fun b41 ->
       Statement.decl "b42" (index 2 2 2) @@ fun b42 ->
       Statement.decl "b43" (index 2 2 3) @@ fun b43 ->
       Statement.decl "b44" (index 2 3 0) @@ fun b44 ->
       Statement.decl "b45" (index 2 3 1) @@ fun b45 ->
       Statement.decl "b46" (index 2 3 2) @@ fun b46 ->
       Statement.decl "b47" (index 2 3 3) @@ fun b47 ->
       Statement.decl "b48" (index 3 0 0) @@ fun b48 ->
       Statement.decl "b49" (index 3 0 1) @@ fun b49 ->
       Statement.decl "b50" (index 3 0 2) @@ fun b50 ->
       Statement.decl "b51" (index 3 0 3) @@ fun b51 ->
       Statement.decl "b52" (index 3 1 0) @@ fun b52 ->
       Statement.decl "b53" (index 3 1 1) @@ fun b53 ->
       Statement.decl "b54" (index 3 1 2) @@ fun b54 ->
       Statement.decl "b55" (index 3 1 3) @@ fun b55 ->
       Statement.decl "b56" (index 3 2 0) @@ fun b56 ->
       Statement.decl "b57" (index 3 2 1) @@ fun b57 ->
       Statement.decl "b58" (index 3 2 2) @@ fun b58 ->
       Statement.decl "b59" (index 3 2 3) @@ fun b59 ->
       Statement.decl "b60" (index 3 3 0) @@ fun b60 ->
       Statement.decl "b61" (index 3 3 1) @@ fun b61 ->
       Statement.decl "b62" (index 3 3 2) @@ fun b62 ->
       Statement.decl "b63" (index 3 3 3) @@ fun b63 ->
       Statement.cstr "s0" ty_slice_alpha Expression.[ v b0; v b1; v b2; v b3 ]
       @@ fun s0 ->
       Statement.cstr "s1" ty_slice_alpha Expression.[ v b4; v b5; v b6; v b7 ]
       @@ fun s1 ->
       Statement.cstr "s2" ty_slice_alpha
         Expression.[ v b8; v b9; v b10; v b11 ]
       @@ fun s2 ->
       Statement.cstr "s3" ty_slice_alpha
         Expression.[ v b12; v b13; v b14; v b15 ]
       @@ fun s3 ->
       Statement.cstr "s4" ty_slice_alpha
         Expression.[ v b16; v b17; v b18; v b19 ]
       @@ fun s4 ->
       Statement.cstr "s5" ty_slice_alpha
         Expression.[ v b20; v b21; v b22; v b23 ]
       @@ fun s5 ->
       Statement.cstr "s6" ty_slice_alpha
         Expression.[ v b24; v b25; v b26; v b27 ]
       @@ fun s6 ->
       Statement.cstr "s7" ty_slice_alpha
         Expression.[ v b28; v b29; v b30; v b31 ]
       @@ fun s7 ->
       Statement.cstr "s8" ty_slice_alpha
         Expression.[ v b32; v b33; v b34; v b35 ]
       @@ fun s8 ->
       Statement.cstr "s9" ty_slice_alpha
         Expression.[ v b36; v b37; v b38; v b39 ]
       @@ fun s9 ->
       Statement.cstr "s10" ty_slice_alpha
         Expression.[ v b40; v b41; v b42; v b43 ]
       @@ fun s10 ->
       Statement.cstr "s11" ty_slice_alpha
         Expression.[ v b44; v b45; v b46; v b47 ]
       @@ fun s11 ->
       Statement.cstr "s12" ty_slice_alpha
         Expression.[ v b48; v b49; v b50; v b51 ]
       @@ fun s12 ->
       Statement.cstr "s13" ty_slice_alpha
         Expression.[ v b52; v b53; v b54; v b55 ]
       @@ fun s13 ->
       Statement.cstr "s14" ty_slice_alpha
         Expression.[ v b56; v b57; v b58; v b59 ]
       @@ fun s14 ->
       Statement.cstr "s15" ty_slice_alpha
         Expression.[ v b60; v b61; v b62; v b63 ]
       @@ fun s15 ->
       Statement.cstr "c0" ty_row_slice_alpha
         Expression.[ v s0; v s4; v s8; v s12 ]
       @@ fun c0 ->
       Statement.cstr "c1" ty_row_slice_alpha
         Expression.[ v s1; v s5; v s9; v s13 ]
       @@ fun c1 ->
       Statement.cstr "c2" ty_row_slice_alpha
         Expression.[ v s2; v s6; v s10; v s14 ]
       @@ fun c2 ->
       Statement.cstr "c3" ty_row_slice_alpha
         Expression.[ v s3; v s7; v s11; v s15 ]
       @@ fun c3 ->
       Statement.cstr "cs" ty_col_row_slice_a
         Expression.[ v c0; v c1; v c2; v c3 ]
       @@ fun cs -> ([], Expression.v cs)
     in

     KnFundecl
       {
         fn_name = reindex_slice_rowcol;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (slice', ty_slice_col_row_a) ];
         return_type = ty_col_row_slice_a;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row ty_alpha) in
     let statements, expression = ([], Expression.v rows) in
     KnFundecl
       {
         fn_name = row_ror_0;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row ty_alpha) in
     let statements, expression =
       ([], Expression.(e_indexing (builin_call BCirc [] [ v rows ]) row 1))
     in
     KnFundecl
       {
         fn_name = row_ror_1;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row ty_alpha) in
     let statements, expression =
       ([], Expression.(e_indexing (builin_call BCirc [] [ v rows ]) row 2))
     in
     KnFundecl
       {
         fn_name = row_ror_2;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row ty_alpha) in
     let statements, expression =
       ([], Expression.(e_indexing (builin_call BCirc [] [ v rows ]) row 3))
     in
     KnFundecl
       {
         fn_name = row_ror_3;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col (app row ty_alpha)) in
     let cols = TermIdent.fresh "cols" in

     let statements, expression =
       let cols = Expression.v cols in
       let cols = Expression.fn_call col_reverse [ ty_alpha ] [ cols ] in
       let cols = Expression.fn_call transpose [ ty_alpha ] [ cols ] in
       let cols = Expression.builin_call BCirc [] [ cols ] in
       let cols = Expression.e_indexing cols row 1 in
       let cols = Expression.fn_call reindex_cols_row [ ty_alpha ] [ cols ] in
       ([], cols)
     in
     KnFundecl
       {
         fn_name = rev_rotate_0;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col (app row ty_alpha)) in
     let cols = TermIdent.fresh "cols" in

     let statements, expression =
       let cols = Expression.v cols in
       let cols = Expression.fn_call col_reverse [ ty_alpha ] [ cols ] in
       let cols = Expression.fn_call transpose [ ty_alpha ] [ cols ] in
       let cols = Expression.builin_call BCirc [] [ cols ] in
       let cols = Expression.e_indexing cols row 2 in
       let cols = Expression.fn_call reindex_cols_row [ ty_alpha ] [ cols ] in
       ([], cols)
     in
     KnFundecl
       {
         fn_name = rev_rotate_1;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col (app row ty_alpha)) in
     let cols = TermIdent.fresh "cols" in

     let statements, expression =
       let cols = Expression.v cols in
       let cols = Expression.fn_call col_reverse [ ty_alpha ] [ cols ] in
       let cols = Expression.fn_call transpose [ ty_alpha ] [ cols ] in
       let cols = Expression.builin_call BCirc [] [ cols ] in
       let cols = Expression.e_indexing cols row 3 in
       let cols = Expression.fn_call reindex_cols_row [ ty_alpha ] [ cols ] in
       ([], cols)
     in
     KnFundecl
       {
         fn_name = rev_rotate_2;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col @@ app row ty_alpha) in
     let cols = TermIdent.fresh "cols" in
     (*     let ( _|> ) e fn_ident = Expression.( |> ) e [ ty_alpha ] fn_ident in*)
     let statements, expression =
       let cols = Expression.v cols in
       let cols = Expression.fn_call col_reverse [ ty_alpha ] [ cols ] in
       let cols = Expression.fn_call transpose [ ty_alpha ] [ cols ] in
       let cols = Expression.builin_call BCirc [] [ cols ] in
       let cols = Expression.e_indexing cols row 0 in
       let cols = Expression.fn_call reindex_cols_row [ ty_alpha ] [ cols ] in
       ([], cols)
     in
     KnFundecl
       {
         fn_name = rev_rotate_3;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let cols = TermIdent.fresh "cols" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_col_alpha = Ty.(app col ty_alpha) in
     let index index = Expression.indexing cols col index in
     let statements, expression =
       Statement.cstr "cols" ty_col_alpha [ index 3; index 2; index 1; index 0 ]
       @@ fun cols -> ([], Expression.v cols)
     in
     KnFundecl
       {
         fn_name = col_reverse;
         ty_vars = [ (alpha, KType) ];
         parameters = [ (cols, ty_col_alpha) ];
         return_type = ty_col_alpha;
         body = { statements; expression };
       });
    (let state' = TermIdent.fresh "state" in
     let key = TermIdent.fresh "key" in
     (*     let ty_alpha = Ty.(v alpha) in*)
     let ty_state = Ty.(eapp state) in
     let ty_cols_rows = Ty.(app col @@ app row bool) in
     let ty_fn_row_cols__row_cols = Ty.(fn [] [ ty_cols_rows ] ty_cols_rows) in
     let _ty_cols_rows_bool = Ty.(app col @@ app row bool) in
     let ty_cols_rows_partial = Ty.(app col @@ eapp row) in
     let ty_slice = Ty.(app slice ty_fn_row_cols__row_cols) in
     let statements, expression =
       Statement.cstr "permbits" ty_slice
         Expression.
           [
             fv_t rev_rotate_0 [ Ty.bool ];
             fv_t rev_rotate_1 [ Ty.bool ];
             fv_t rev_rotate_2 [ Ty.bool ];
             fv_t rev_rotate_3 [ Ty.bool ];
           ]
       @@ fun permbits ->
       Statement.decl "state"
         Expression.(
           let_plus "slice" ty_cols_rows_partial
             Ty.(app slice bool)
             Expression.(v state')
             []
           @@ fun expr _ ->
           ([], fn_call subcells [ Ty.(app slice bool) ] [ v expr ]))
       @@ fun state ->
       Statement.log "after subcells" [ state ] @@ fun () ->
       Statement.decl "state"
         Expression.(
           fn_call reindex_rowcol_slice Ty.[ bool ] Expression.[ v state ])
       @@ fun state ->
       Statement.decl "state"
         Expression.(
           fn_call app
             Ty.[ ty_cols_rows_partial; bool; bool ]
             [ v permbits; v state ])
       @@ fun state ->
       Statement.decl "state"
         Expression.(
           fn_call reindex_slice_rowcol Ty.[ bool ] Expression.[ v state ])
       @@ fun state ->
       Statement.log "after permbits" [ state ] @@ fun () ->
       Statement.decl "state" Expression.(v state lxor v key) @@ fun state ->
       Statement.log "after add_round_key" [ state ] @@ fun () ->
       ([], Expression.v state)
     in
     KnFundecl
       {
         fn_name = round;
         ty_vars = [];
         parameters = [ (state', ty_state); (key, ty_state) ];
         return_type = ty_state;
         body = { statements; expression };
       });
    (let vstate = TermIdent.fresh "state" in
     let vkeys = TermIdent.fresh "keys" in
     let ty_state = Ty.(eapp state) in
     let ty_keys = Ty.(eapp keys) in
     let expression =
       List.init 28 Fun.id
       |> List.fold_left
            (fun acc i ->
              Expression.(fn_call round [] [ acc; indexing vkeys keys i ]))
            (Expression.v vstate)
     in
     KnFundecl
       {
         fn_name = fngift;
         ty_vars = [];
         parameters = [ (vstate, ty_state); (vkeys, ty_keys) ];
         return_type = ty_state;
         body = { statements = []; expression };
       });
  ]
