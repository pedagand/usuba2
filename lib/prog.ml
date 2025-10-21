type 't fndecl_ = {
  fn_name : 'fn_ident;
  signature : 't Ty.signature;
  args : 'term_id list;
  body : 't Term.t;
}
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >
(** [fn f [a](x1: ty1, x2: ty2, ...) ty = t] *)

let pp_fndecl_ pp_var pp_ty_var pp_ty_decl pp_fn_ident format fn =
  let pp_ty = Ty.pp pp_ty_var pp_ty_decl in
  let pp_term = Term.pp pp_var pp_ty_var pp_ty_decl pp_fn_ident in
  let { fn_name; signature; args; body } = fn in
  let pp_parameter format (variable, ty) =
    Format.fprintf format "%a : %a" pp_var variable pp_ty ty
  in
  let pp_tyvars =
    Format.pp_print_option (fun format ty ->
        Format.fprintf format "[%a]" pp_ty_var ty)
  in
  let pp_parameters =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.fprintf format ", ")
      pp_parameter
  in
  let parameters = List.combine args signature.parameters in
  Format.fprintf format "fn %a %a(%a) %a = %a" pp_fn_ident fn_name pp_tyvars
    signature.tyvars pp_parameters parameters pp_ty signature.return_type
    pp_term body

(* Type decl only create alias. *)
type 't tydecl_ = {
  (* XXX: what's this `ty_var` doing here? *)
  tyvar : 'ty_var;
  name : 'ty_decl;
  size : int;
}
  constraint 't = < ty_decl : 'ty_decl ; ty_var : 'ty_var ; .. >
(** [type ty = tuple[i]] *)

let pp_tydecl_ pp_tydecl format ty =
  Format.fprintf format "type %a = tuple[%u]" pp_tydecl ty.name ty.size

type 't node_ = NFun of 't fndecl_ | NTy of 't tydecl_

let pp_node_ pp_var pp_ty_var pp_ty_decl pp_fn_ident format = function
  | NFun fn -> pp_fndecl_ pp_var pp_ty_var pp_ty_decl pp_fn_ident format fn
  | NTy ty -> pp_tydecl_ pp_ty_decl format ty

type 't prog_ = 't node_ list

let pp_prog_ pp_var pp_ty_var pp_ty_decl pp_fn_ident format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.fprintf format "\n\n")
    (pp_node_ pp_var pp_ty_var pp_ty_decl pp_fn_ident)
    format

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

type pre =
  < ty_decl : string ; fn_ident : string ; ty_var : string ; term_id : string >
(** Parser produces pre-things, before scope checking *)

type pre_term = pre Term.t
type pre_tydecl = pre tydecl_
type pre_fndecl = pre fndecl_
type pre_node = pre node_
type pre_prog = pre prog_

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

module TermIdent = Ident.Make ()
module TyIdent = Ident.Make ()
module TyDeclIdent = Ident.Make ()
module FnIdent = Ident.Make ()

type scoped =
  < ty_decl : TyDeclIdent.t
  ; fn_ident : FnIdent.t
  ; ty_var : TyIdent.t
  ; term_id : TermIdent.t >
(** First pass check scope and generate unique identifiers *)

type ty = scoped Ty.t
type term = scoped Term.t
type tydecl = scoped tydecl_
type fndecl = scoped fndecl_
type node = scoped node_
type prog = scoped prog_

let pp_ty format = Ty.pp TyIdent.pp TyDeclIdent.pp format

let pp_cterm format =
  Term.pp TermIdent.pp TyIdent.pp TyDeclIdent.pp FnIdent.pp format

let pp_sterm format =
  Term.pp_sterm TermIdent.pp TyIdent.pp TyDeclIdent.pp FnIdent.pp format

let pp_fndecl format =
  pp_fndecl_ TermIdent.pp TyIdent.pp TyDeclIdent.pp FnIdent.pp format

let pp_tydecl format = pp_tydecl_ TyDeclIdent.pp format

let pp_node format =
  pp_node_ TermIdent.pp TyIdent.pp TyDeclIdent.pp FnIdent.pp format

let pp_prog format =
  pp_prog_ TermIdent.pp TyIdent.pp TyDeclIdent.pp FnIdent.pp format
