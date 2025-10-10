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
