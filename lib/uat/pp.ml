let pp_list_ty = Format.pp_print_list Ast.TyDeclIdent.pp

let rec pp_term' format term = pp_term format (fst term)

and pp_term format = function
  | Ast.TFalse -> Format.fprintf format "false"
  | Ast.TTrue -> Format.fprintf format "true"
  | Ast.TVar variable -> Ast.TermIdent.pp format variable
  | TLet { variable; term; k } ->
      Format.fprintf format "let %a = %a in %a" Ast.TermIdent.pp variable
        pp_term' term pp_term' k
  | TFn { fn_ident; _ } -> Ast.FnIdent.pp format fn_ident
  | TLookup { lterm; index } ->
      Format.fprintf format "%a[%u]" pp_lterm' lterm index
  | TThunk { lterm } -> Format.fprintf format "# %a" pp_lterm' lterm
  | TLog { k; _ } -> pp_term' format k
  | TLift { tys; term } ->
      Format.fprintf format "lift[%a](%a)" pp_list_ty tys pp_term' term
  | TOperator operation -> pp_operation format operation
  | TFnCall { fn_name; ty_resolve; args } ->
      let pp_fn_name =
        Format.pp_print_either ~left:Ast.FnIdent.pp ~right:Ast.TermIdent.pp
      in
      let pp_ty_resolve =
        Format.pp_print_option (fun format ty ->
            Format.fprintf format "[%a]" Ua0.Pp.pp_ty ty)
      in
      let pp_args =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.fprintf format ", ")
          pp_term'
      in
      Format.fprintf format "%a.%a(%a)" pp_fn_name fn_name pp_ty_resolve
        ty_resolve pp_args args

and pp_operation format = function
  | Ua0.Ast.ONot term -> Format.fprintf format "! %a" pp_term' term
  | Ua0.Ast.OAnd (lhs, rhs) ->
      Format.fprintf format "(%a & %a)" pp_term' lhs pp_term' rhs
  | Ua0.Ast.OXor (lhs, rhs) ->
      Format.fprintf format "(%a ^ %a)" pp_term' lhs pp_term' rhs
  | Ua0.Ast.OOr (lhs, rhs) ->
      Format.fprintf format "(%a | %a)" pp_term' lhs pp_term' rhs

and pp_lterm' format lterm = pp_lterm format (fst lterm)

and pp_lterm format = function
  | Ast.LLetPlus { variable; lterm; ands; term } ->
      let pp_and format (variable, lterm) =
        Format.fprintf format "and %a = %a" Ast.TermIdent.pp variable pp_lterm'
          lterm
      in
      let pp_ands = Format.pp_print_list pp_and in
      Format.fprintf format "let+ %a = %a %a in %a" Ast.TermIdent.pp variable
        pp_lterm' lterm pp_ands ands pp_term' term
  | LConstructor { ty; terms } ->
      let pp_terms =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.fprintf format ", ")
          pp_term'
      in
      Format.fprintf format "%a (%a)" Ast.TyDeclIdent.pp ty pp_terms terms
  | LRange { ty; term } ->
      Format.fprintf format "range[%a](%a)" pp_list_ty ty pp_term' term
  | LReindex { lhs; rhs; lterm } ->
      Format.fprintf format "reindex[%a | %a](%a)" pp_list_ty lhs pp_list_ty rhs
        pp_lterm' lterm
  | LCirc lterm -> Format.fprintf format "circ(%a)" pp_lterm' lterm

let pp_fn format fn =
  let Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  let pp_parameter format (variable, ty) =
    Format.fprintf format "%a : %a" Ast.TermIdent.pp variable Ua0.Pp.pp_ty ty
  in
  let pp_tyvars =
    Format.pp_print_option (fun format ty ->
        Format.fprintf format "[%a]" Ast.TyIdent.pp ty)
  in
  let pp_parameters =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.fprintf format ", ")
      pp_parameter
  in
  Format.fprintf format "fn %a %a(%a) %a = %a" Ast.FnIdent.pp fn_name pp_tyvars
    tyvars pp_parameters parameters Ua0.Pp.pp_ty return_type pp_term' body

let pp_tydecl format ty =
  let Ua0.Ast.{ size; name; tyvar = _ } = ty in
  Format.fprintf format "type %a = tuple[%u]" Ast.TyDeclIdent.pp name size

let pp_node format = function
  | Ast.NFun fn -> pp_fn format fn
  | Ast.NTy ty -> pp_tydecl format ty

let pp_prog format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.fprintf format "\n\n")
    pp_node format
