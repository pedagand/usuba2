module Ident () = struct
  type t = { id : int; pretty : string }

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let compare lhs rhs = Int.compare lhs.id rhs.id
  let pp format { id = _; pretty } = Format.fprintf format "%s" pretty
end

module TyIdent = Ident ()
module TyDeclIdent = Ident ()
module TermIdent = Ident ()
module FnIdent = Ident ()

let circ = FnIdent.fresh "@circ"
let anti_circ = FnIdent.fresh "@anti_circ"
let map2 = FnIdent.fresh "@map2"
let pure = FnIdent.fresh "@pure"
let app = FnIdent.fresh "@app"
(* type 'a = 'a Util.Position.loc *)

(* type tykind = KType | KArrow of { parameters : tykind list; return : tykind } *)

type kind = KindTy of kind list

type ty =
  | TyApp of { name : TyDeclIdent.t; ty_args : ty list }
  | TyVarApp of { name : TyIdent.t; ty_args : ty list }
  | TyTuple of { size : int; ty : ty }
  | TyFun of (ty list * ty)
  | TyBool

type indexing = { name : TyDeclIdent.t; index : int }

type 'a op =
  | Unot of 'a
  | Uneg of 'a
  | BAnd of ('a * 'a)
  | BOr of ('a * 'a)
  | BXor of ('a * 'a)

type expression =
  | ETrue
  | EFalse
  | EVar of TermIdent.t
  | EFunVar of FnIdent.t
  | EIndexing of { expression : expression; indexing : indexing }
  | EOp of { op : expression op }
  | EFunctionCall of {
      fn_name : (FnIdent.t, TermIdent.t) Either.t;
      ty_args : ty list;
      args : expression list;
    }

type statement =
  | StDeclaration of { variable : TermIdent.t; expression : expression }
  | StConstructor of {
      variable : TermIdent.t;
      ty : ty;
      expressions : expression list;
    }
  | SLetPLus of {
      variable : TermIdent.t;
      expression : expression;
      ands : (TermIdent.t * expression) list;
    }

type body = { statements : statement list; expression : expression }

type kasumi_type_decl = {
  ty_vars : TyIdent.t list;
  ty_name : TyDeclIdent.t;
  definition : ty;
}

type kasumi_function_decl = {
  fn_name : FnIdent.t;
  parameters : (TermIdent.t * ty) list;
  return_type : ty;
  body : body;
}

type kasumi_node =
  | KnTypedecl of kasumi_type_decl
  | KnFundecl of kasumi_function_decl

type ksm_module = kasumi_node list

module Pp = struct
  let rec pp_ty format = function
    | TyBool -> Format.fprintf format "bool"
    | TyApp { name; ty_args } ->
        Format.fprintf format "%a%a" pp_ty_args ty_args TyDeclIdent.pp name
    | TyFun (params, ret) ->
        Format.fprintf format "(%a) -> %a" pp_tys params pp_ty ret
    | TyVarApp { name; ty_args } ->
        Format.fprintf format "%a%a" pp_ty_args ty_args TyIdent.pp name
    | TyTuple { size; ty } -> Format.fprintf format "%a tuple<%u>" pp_ty ty size

  and pp_tys format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_char format ',')
      pp_ty format

  and pp_ty_args format ty_args =
    match ty_args with
    | [] -> ()
    | (TyFun _ as ty) :: [] -> Format.fprintf format "(%a) " pp_ty ty
    | ty :: [] -> Format.fprintf format "%a " pp_ty ty
    | _ :: _ as ty_args -> Format.fprintf format "(%a) " pp_tys ty_args

  let pp_op fmt format = function
    | Unot expression -> Format.fprintf format "! %a" fmt expression
    | Uneg expression -> Format.fprintf format "- %a" fmt expression
    | BAnd (lhs, rhs) -> Format.fprintf format "%a and (%a)" fmt lhs fmt rhs
    | BOr (lhs, rhs) -> Format.fprintf format "%a or (%a)" fmt lhs fmt rhs
    | BXor (lhs, rhs) -> Format.fprintf format "%a xor (%a)" fmt lhs fmt rhs

  let pp_indexing format indexing =
    let { name; index } = indexing in
    Format.fprintf format "%a(%u)" TyDeclIdent.pp name index

  let rec pp_expression format = function
    | ETrue -> Format.fprintf format "1"
    | EFalse -> Format.fprintf format "0"
    | EVar id -> Format.fprintf format "%a" TermIdent.pp id
    | EFunVar id -> Format.fprintf format "%a" FnIdent.pp id
    | EIndexing { expression; indexing } ->
        Format.fprintf format "%a[%a]" pp_expression expression pp_indexing
          indexing
    | EOp { op } -> pp_op pp_expression format op
    | EFunctionCall { fn_name; ty_args; args } ->
        let pp_ty_args format ty_args =
          match ty_args with
          | [] -> ()
          | _ :: _ as ty_args ->
              let pp_list =
                Format.pp_print_list
                  ~pp_sep:(fun format () -> Format.pp_print_char format ',')
                  pp_ty
              in
              Format.fprintf format "[%a] " pp_list ty_args
        in
        let pp_expressions =
          Format.pp_print_list
            ~pp_sep:(fun format () -> Format.pp_print_char format ',')
            pp_expression
        in
        let pp_either =
          Format.pp_print_either ~left:FnIdent.pp ~right:TermIdent.pp
        in
        Format.fprintf format "%a%a(%a)" pp_either fn_name pp_ty_args ty_args
          pp_expressions args

  and pp_expressions format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_char format ',')
      pp_expression format

  let pp_statement format = function
    | StDeclaration { variable; expression } ->
        Format.fprintf format "let %a = %a in" TermIdent.pp variable
          pp_expression expression
    | StConstructor { variable; ty; expressions } ->
        Format.fprintf format "let %a = %a {%a} in" TermIdent.pp variable pp_ty
          ty pp_expressions expressions
    | SLetPLus { variable; expression; ands } ->
        let pp_ands =
          Format.pp_print_list
            ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
            (fun format (id, expression) ->
              Format.fprintf format "and+ %a = %a" TermIdent.pp id pp_expression
                expression)
        in
        Format.fprintf format "let+ %a = %a%a in" TermIdent.pp variable
          pp_expression expression pp_ands ands

  let pp_function_decl format decl =
    let { fn_name; parameters; return_type; body = { statements; expression } }
        =
      decl
    in
    let pp_args =
      Format.pp_print_list
        ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
        (fun format (id, expression) ->
          Format.fprintf format "%a: %a" TermIdent.pp id pp_ty expression)
    in
    let pp_statements =
      Format.pp_print_list ~pp_sep:Format.pp_print_newline pp_statement
    in
    Format.fprintf format "def %a(%a) -> %a =%a%a%a%a" FnIdent.pp fn_name
      pp_args parameters pp_ty return_type Format.pp_print_newline ()
      pp_statements statements Format.pp_print_newline () pp_expression
      expression

  let pp_type_decl format type_decl =
    let { ty_vars; ty_name; definition } = type_decl in
    let pp_ty_args format ty_args =
      match ty_args with
      | [] -> ()
      | _ :: _ as ty_args ->
          let pp_list =
            Format.pp_print_list
              ~pp_sep:(fun format () -> Format.pp_print_char format ',')
              TyIdent.pp
          in
          Format.fprintf format "(%a) " pp_list ty_args
    in
    Format.fprintf format "type %a%a = %a" pp_ty_args ty_vars TyDeclIdent.pp
      ty_name pp_ty definition

  let pp_node format = function
    | KnFundecl function_decl -> pp_function_decl format function_decl
    | KnTypedecl type_decl -> pp_type_decl format type_decl

  let pp_module format =
    Format.pp_print_list
      ~pp_sep:(fun format () ->
        Format.(fprintf format "%a%a" pp_print_newline () pp_print_newline ()))
      pp_node format
end

module Ty = struct
  let bool = TyBool
  let app name ty_args = TyApp { name; ty_args }
  let tuple size ty = TyTuple { size; ty }
  let fn args ret = TyFun (args, ret)
  let v name = TyVarApp { name; ty_args = [] }
  let varapp name ty_args = TyVarApp { name; ty_args }
end

module Expression = struct
  let true' = ETrue
  let false' = EFalse

  let e_indexing e slice index =
    EIndexing { expression = e; indexing = { name = slice; index } }

  let indexing s slice index = e_indexing (EVar s) slice index

  let fn_call fn_name ty_args args =
    EFunctionCall { fn_name = Left fn_name; ty_args; args }

  let term_call fn_name ty_args args =
    EFunctionCall { fn_name = Right fn_name; ty_args; args }

  let ( land ) lhs rhs = EOp { op = BAnd (lhs, rhs) }
  let ( lor ) lhs rhs = EOp { op = BOr (lhs, rhs) }
  let ( lxor ) lhs rhs = EOp { op = BXor (lhs, rhs) }

  let ( |> ) e fn_name =
    EFunctionCall { fn_name = Either.left fn_name; ty_args = []; args = [ e ] }

  let lnot expr = EOp { op = Unot expr }
  let v s = EVar s
  let fv s = EFunVar s
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

  let let_plus variable expression ands k =
    let variable = TermIdent.fresh variable in
    let ands =
      List.map
        (fun (variable, expression) ->
          let variable = TermIdent.fresh variable in
          (variable, expression))
        ands
    in
    let statements, final = k variable (List.map fst ands) in
    (SLetPLus { variable; expression; ands } :: statements, final)
end

let gift =
  let row = TyDeclIdent.fresh "row" in
  let col = TyDeclIdent.fresh "col" in
  let keys = TyDeclIdent.fresh "keys" in
  let slice = TyDeclIdent.fresh "slice" in
  let state = TyDeclIdent.fresh "state" in
  let subcells = FnIdent.fresh "subcells" in
  let add_round_key = FnIdent.fresh "add_round_key" in
  let transpose = FnIdent.fresh "transpose" in
  let reindex_cols_row = FnIdent.fresh "reindex_cols_row" in
  let col_reverse = FnIdent.fresh "col_reverse" in
  let rev_rotate_0 = FnIdent.fresh "rev_rotate_0" in
  let rev_rotate_1 = FnIdent.fresh "rev_rotate_1" in
  let rev_rotate_2 = FnIdent.fresh "rev_rotate_2" in
  let rev_rotate_3 = FnIdent.fresh "rev_rotate_3" in
  let permbits = FnIdent.fresh "permbits" in
  let row_ror_0 = FnIdent.fresh "row_ror_0" in
  let row_ror_1 = FnIdent.fresh "row_ror_1" in
  let row_ror_2 = FnIdent.fresh "row_ror_2" in
  let row_ror_3 = FnIdent.fresh "row_ror_3" in
  let fxor = FnIdent.fresh "fxor" in
  let round = FnIdent.fresh "round" in
  let gift = FnIdent.fresh "gift" in
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
        definition = Ty.(app slice [ app col [ app row [ bool ] ] ]);
      };
    KnTypedecl
      {
        ty_vars = [];
        ty_name = keys;
        definition = Ty.(tuple 28 @@ app state []);
      };
    (let alpha = TyIdent.fresh "'a" in
     let beta = TyIdent.fresh "'b" in
     let charly = TyIdent.fresh "'c" in
     let ctrl = TyIdent.fresh "#t" in
     let ty_alpha = Ty.(v alpha) in
     let ty_beta = Ty.(v beta) in
     let ty_charly = Ty.(v charly) in
     let ty_ctrl_alpha = Ty.(varapp ctrl [ ty_alpha ]) in
     let ty_ctrl_beta = Ty.(varapp ctrl [ ty_beta ]) in
     let ty_ctrl_charly = Ty.(varapp ctrl [ ty_charly ]) in
     let ty_fn = Ty.(fn [ ty_alpha; ty_beta ] ty_charly) in
     let f = TermIdent.fresh "f" in
     let xs = TermIdent.fresh "xs" in
     let ys = TermIdent.fresh "ys" in
     let statements, expression =
       Statement.let_plus "x" Expression.(v xs) Expression.[ ("y", v ys) ]
       @@ fun x ands ->
       let y = match ands with [] -> assert false | t :: _ -> t in
       ([], Expression.term_call f [] Expression.[ v x; v y ])
     in
     KnFundecl
       {
         fn_name = map2;
         parameters = [ (f, ty_fn); (xs, ty_ctrl_alpha); (ys, ty_ctrl_beta) ];
         return_type = ty_ctrl_charly;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let lhs = TermIdent.fresh "lhs" in
     let rhs = TermIdent.fresh "rhs" in
     KnFundecl
       {
         fn_name = fxor;
         parameters = [ (lhs, ty_alpha); (rhs, ty_alpha) ];
         return_type = ty_alpha;
         body = { statements = []; expression = Expression.(v lhs lxor v rhs) };
       });
    (let s = TermIdent.fresh "s" in
     let alpha = TyIdent.fresh "'a" in
     let ty_slice = Ty.(app slice [ v alpha ]) in
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
         parameters = [ (s, ty_slice) ];
         return_type = ty_slice;
         body = { statements; expression };
       });
    (let s = TermIdent.fresh "s" in
     let key = TermIdent.fresh "key" in
     let alpha = TyIdent.fresh "'a" in
     (* let ty_alpha = Ty.(v alpha) in *)
     let ty_slice = Ty.(app slice [ v alpha ]) in
     let statements, expression = ([], Expression.(v s lxor v key)) in
     KnFundecl
       {
         fn_name = add_round_key;
         parameters = [ (s, ty_slice); (key, ty_slice) ];
         return_type = ty_slice;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_col_alpha = Ty.(app col [ ty_alpha ]) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let ty_rows_cols = Ty.(app row [ ty_col_alpha ]) in
     let state = TermIdent.fresh "state" in
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
         parameters = [ (state, ty_cols_rows) ];
         return_type = ty_rows_cols;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_row_alpha = Ty.(app row [ ty_alpha ]) in
     let ty_row_cols = Ty.(app row [ app col [ ty_alpha ] ]) in
     let ty_col_rows = Ty.(app col [ ty_row_alpha ]) in
     let state = TermIdent.fresh "state" in
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
         parameters = [ (state, ty_row_cols) ];
         return_type = ty_col_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row [ ty_alpha ]) in
     let statements, expression = ([], Expression.v rows) in
     KnFundecl
       {
         fn_name = row_ror_0;
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row [ ty_alpha ]) in
     let index index = Expression.indexing rows row index in
     let statements, expression =
       Statement.cstr "rows" ty_rows [ index 3; index 0; index 1; index 2 ]
       @@ fun rows -> ([], Expression.v rows)
     in
     KnFundecl
       {
         fn_name = row_ror_1;
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row [ ty_alpha ]) in
     let index index = Expression.indexing rows row index in
     let statements, expression =
       Statement.cstr "rows" ty_rows [ index 2; index 3; index 0; index 1 ]
       @@ fun rows -> ([], Expression.v rows)
     in
     KnFundecl
       {
         fn_name = row_ror_2;
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let rows = TermIdent.fresh "rows" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_rows = Ty.(app row [ ty_alpha ]) in
     let index index = Expression.indexing rows row index in
     let statements, expression =
       Statement.cstr "rows" ty_rows [ index 1; index 2; index 3; index 0 ]
       @@ fun rows -> ([], Expression.v rows)
     in
     KnFundecl
       {
         fn_name = row_ror_3;
         parameters = [ (rows, ty_rows) ];
         return_type = ty_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let cols = TermIdent.fresh "cols" in
     let statements, expression =
       ( [],
         Expression.(
           v cols |> col_reverse |> transpose |> row_ror_1 |> reindex_cols_row)
       )
     in
     KnFundecl
       {
         fn_name = rev_rotate_0;
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let cols = TermIdent.fresh "cols" in
     let statements, expression =
       ( [],
         Expression.(
           v cols |> col_reverse |> transpose |> row_ror_2 |> reindex_cols_row)
       )
     in
     KnFundecl
       {
         fn_name = rev_rotate_1;
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let cols = TermIdent.fresh "cols" in
     let statements, expression =
       ( [],
         Expression.(
           v cols |> col_reverse |> transpose |> row_ror_3 |> reindex_cols_row)
       )
     in
     KnFundecl
       {
         fn_name = rev_rotate_3;
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let cols = TermIdent.fresh "cols" in
     let statements, expression =
       ( [],
         Expression.(
           v cols |> col_reverse |> transpose |> row_ror_0 |> reindex_cols_row)
       )
     in
     KnFundecl
       {
         fn_name = rev_rotate_1;
         parameters = [ (cols, ty_cols_rows) ];
         return_type = ty_cols_rows;
         body = { statements; expression };
       });
    (let cols = TermIdent.fresh "cols" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_col_alpha = Ty.(app col [ ty_alpha ]) in
     let index index = Expression.indexing cols col index in
     let statements, expression =
       Statement.cstr "cols" ty_col_alpha [ index 3; index 2; index 1; index 0 ]
       @@ fun cols -> ([], Expression.v cols)
     in
     KnFundecl
       {
         fn_name = col_reverse;
         parameters = [ (cols, ty_col_alpha) ];
         return_type = ty_col_alpha;
         body = { statements; expression };
       });
    (let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let ty_fn_row_cols__row_cols = Ty.(fn [ ty_cols_rows ] ty_cols_rows) in
     let ty_slice = Ty.(app slice [ ty_fn_row_cols__row_cols ]) in
     let statements, expression =
       Statement.cstr "slice" ty_slice
         Expression.
           [
             fv rev_rotate_0; fv rev_rotate_1; fv rev_rotate_2; fv rev_rotate_3;
           ]
       @@ fun s -> ([], Expression.v s)
     in
     KnFundecl
       {
         fn_name = permbits;
         parameters = [];
         return_type = ty_slice;
         body = { statements; expression };
       });
    (let s = TermIdent.fresh "s" in
     let key = TermIdent.fresh "key" in
     let alpha = TyIdent.fresh "'a" in
     let ty_alpha = Ty.(v alpha) in
     let _ty_slice = Ty.(app slice [ v alpha ]) in
     let ty_state = Ty.(app state []) in
     let ty_cols_rows = Ty.(app col [ app row [ ty_alpha ] ]) in
     let ty_fn_row_cols__row_cols = Ty.(fn [ ty_cols_rows ] ty_cols_rows) in
     let ty_slice = Ty.(app slice [ ty_fn_row_cols__row_cols ]) in
     let statements, expression =
       Statement.cstr "permbits" ty_slice
         Expression.
           [
             fv rev_rotate_0; fv rev_rotate_1; fv rev_rotate_2; fv rev_rotate_3;
           ]
       @@ fun permbits ->
       Statement.decl "state" Expression.(fn_call subcells [] [ v s ])
       @@ fun state ->
       Statement.decl "state"
         Expression.(fn_call app [] [ v permbits; v state ])
       @@ fun state ->
       ([], Expression.(fn_call add_round_key [] [ v state; v key ]))
     in
     KnFundecl
       {
         fn_name = round;
         parameters = [ (s, ty_state); (key, ty_state) ];
         return_type = ty_state;
         body = { statements; expression };
       });
    (let vstate = TermIdent.fresh "state" in
     let vkeys = TermIdent.fresh "keys" in
     let ty_state = Ty.(app state []) in
     let ty_keys = Ty.(app keys []) in
     let expression =
       List.init 28 Fun.id
       |> List.fold_left
            (fun acc i ->
              Expression.(fn_call round [] [ acc; indexing vkeys keys i ]))
            (Expression.v vstate)
     in
     KnFundecl
       {
         fn_name = gift;
         parameters = [ (vstate, ty_state); (vkeys, ty_keys) ];
         return_type = ty_state;
         body = { statements = []; expression };
       });
  ]
