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

let rec pp_ty format = Ty.pp TyIdent.pp TyDeclIdent.pp format

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

let pp_fn_name =
  Format.pp_print_either ~left:Ast.FnIdent.pp ~right:Ast.TermIdent.pp

let pp_cterm =
  Term.pp Ast.TermIdent.pp Ast.TyIdent.pp Ast.TyDeclIdent.pp Ast.FnIdent.pp

let pp_sterm =
  Term.pp_sterm Ast.TermIdent.pp Ast.TyIdent.pp Ast.TyDeclIdent.pp
    Ast.FnIdent.pp

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
