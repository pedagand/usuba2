open Ast

let pp_tyvars format ty_vars =
  match ty_vars with
  | [] -> ()
  | _ :: _ as ty_vars ->
      let pp_list =
        Format.pp_print_list ~pp_sep:(fun format () ->
            Format.fprintf format ", ")
        @@ fun format id -> Format.fprintf format "%a" TyIdent.pp id
      in
      Format.fprintf format "%a. " pp_list ty_vars

let pp_tyvar_opt format = Format.pp_print_option TyIdent.pp format

let rec pp_ty format = function
  | Ty.Bool -> Format.fprintf format "bool"
  | App { name; ty } ->
      Format.fprintf format "%a %a" TyDeclIdent.pp name pp_ty ty
  | Fun { tyvars; parameters; return_type } ->
      Format.fprintf format "fn %a(%a) -> %a" pp_tyvar_opt tyvars pp_tys
        parameters pp_ty return_type
  | Var name -> Format.fprintf format "%a" TyIdent.pp name

and pp_tys format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
    pp_ty format

and pp_ty_args format ty_args =
  match ty_args with
  | [] -> ()
  | (Ty.Fun _ as ty) :: [] -> Format.fprintf format "(%a) " pp_ty ty
  | ty :: [] -> Format.fprintf format "%a " pp_ty ty
  | _ :: _ as ty_args -> Format.fprintf format "(%a) " pp_tys ty_args

and pp_ty_opt_args format ty_args =
  match ty_args with
  | None -> ()
  | Some (Ty.Fun _ as ty) -> Format.fprintf format "(%a) " pp_ty ty
  | Some ty -> Format.fprintf format "%a " pp_ty ty

let pp_list_ty = Format.pp_print_list Ast.TyDeclIdent.pp

let rec pp_cterm format = function
  | False -> Format.fprintf format "false"
  | True -> Format.fprintf format "true"
  | Let { variable; term; k } ->
      Format.fprintf format "let %a = %a in %a" Ast.TermIdent.pp variable
        pp_sterm term pp_cterm k
  | LetPlus { variable; lterm; ands; term } ->
      let pp_and format (variable, lterm) =
        Format.fprintf format "and %a = %a" Ast.TermIdent.pp variable pp_sterm
          lterm
      in
      let pp_ands = Format.pp_print_list pp_and in
      Format.fprintf format "let+ %a = %a %a in %a" Ast.TermIdent.pp variable
        pp_sterm lterm pp_ands ands pp_cterm term
  | Constructor { ty; terms } ->
      let pp_terms =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.fprintf format ", ")
          pp_cterm
      in
      Format.fprintf format "%a (%a)" Ast.TyDeclIdent.pp ty pp_terms terms
  | Log { k; _ } -> pp_cterm format k
  | Synth t -> pp_sterm format t

and pp_sterm format = function
  | Var variable -> Ast.TermIdent.pp format variable
  | Fn { fn_ident; _ } -> Ast.FnIdent.pp format fn_ident
  | Lookup { lterm; index } ->
      Format.fprintf format "%a[%u]" pp_sterm lterm index
  (*  | Lift { tys; term } ->
      Format.fprintf format "lift[%a](%a)" pp_list_ty tys pp_term' term*)
  | Operator operation -> pp_operation format operation
  | Reindex { lhs; rhs; lterm } ->
      Format.fprintf format "reindex[%a | %a](%a)" pp_list_ty lhs pp_list_ty rhs
        pp_sterm lterm
  | Circ lterm -> Format.fprintf format "circ(%a)" pp_sterm lterm
  | FnCall { fn_name; ty_resolve; args } ->
      let pp_fn_name =
        Format.pp_print_either ~left:Ast.FnIdent.pp ~right:Ast.TermIdent.pp
      in
      let pp_ty_resolve =
        Format.pp_print_option (fun format ty ->
            Format.fprintf format "[%a]" pp_ty ty)
      in
      let pp_args =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.fprintf format ", ")
          pp_cterm
      in
      Format.fprintf format "%a.%a(%a)" pp_fn_name fn_name pp_ty_resolve
        ty_resolve pp_args args
  | Ann (tm, ty) -> Format.fprintf format "(%a : %a)" pp_cterm tm pp_ty ty

and pp_operation format = function
  | Operator.Not term -> Format.fprintf format "! %a" pp_cterm term
  | And (lhs, rhs) ->
      Format.fprintf format "(%a & %a)" pp_cterm lhs pp_cterm rhs
  | Xor (lhs, rhs) ->
      Format.fprintf format "(%a ^ %a)" pp_cterm lhs pp_cterm rhs
  | Or (lhs, rhs) -> Format.fprintf format "(%a | %a)" pp_cterm lhs pp_cterm rhs

let pp_fn format fn =
  let { fn_name; signature; args; body } = fn in
  let pp_parameter format (variable, ty) =
    Format.fprintf format "%a : %a" Ast.TermIdent.pp variable pp_ty ty
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
  let parameters = List.combine args signature.parameters in
  Format.fprintf format "fn %a %a(%a) %a = %a" Ast.FnIdent.pp fn_name pp_tyvars
    signature.tyvars pp_parameters parameters pp_ty signature.return_type
    pp_cterm body

let pp_tydecl format ty =
  let Ast.{ size; name; tyvar = _ } = ty in
  Format.fprintf format "type %a = tuple[%u]" Ast.TyDeclIdent.pp name size

let pp_node format = function
  | Ast.NFun fn -> pp_fn format fn
  | Ast.NTy ty -> pp_tydecl format ty

let pp_prog format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.fprintf format "\n\n")
    pp_node format
