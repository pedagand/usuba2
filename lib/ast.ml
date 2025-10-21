module TermIdent = Ident.Make ()
module TyIdent = Ident.Make ()
module TyDeclIdent = Ident.Make ()
module FnIdent = Ident.Make ()

type 't fn_declaration_ = {
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

(* Type decl only create alias. *)
type 't ty_declaration_ = {
  (* XXX: what's this `ty_var` doing here? *)
  tyvar : 'ty_var;
  name : 'ty_decl;
  size : int;
}
  constraint 't = < ty_decl : 'ty_decl ; ty_var : 'ty_var ; .. >
(** [type ty = tuple[i]] *)

type 't node_ = NFun of 't fn_declaration_ | NTy of 't ty_declaration_
type 't prog_ = 't node_ list

type pre =
  < ty_decl : string ; fn_ident : string ; ty_var : string ; term_id : string >

type pre_term = pre Term.t
type pre_ty_declaration = pre ty_declaration_
type pre_fn_declaration = pre fn_declaration_
type pre_node = pre node_
type pre_prog = pre prog_

type scoped =
  < ty_decl : TyDeclIdent.t
  ; fn_ident : FnIdent.t
  ; ty_var : TyIdent.t
  ; term_id : TermIdent.t >

type term = scoped Term.t
type ty_declaration = scoped ty_declaration_
type fn_declaration = scoped fn_declaration_
type node = scoped node_
type prog = scoped prog_
