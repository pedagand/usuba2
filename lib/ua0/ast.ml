module Ident () = struct
  type t = { id : int; pretty : string }

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let compare lhs rhs = Int.compare lhs.id rhs.id
  let equal lhs rhs = Int.equal lhs.id rhs.id
  let pp format { id; pretty } = Format.fprintf format "%s(%u)" pretty id
end

module TermIdent = Ident ()
module TyIdent = Ident ()
module TyDeclIdent = Ident ()
module FnIdent = Ident ()

type ('ty_decl, 'ty_var) ty =
  | TyBool
  | TyVar of 'ty_var
  | TyApp of { name : 'ty_decl; ty : ('ty_decl, 'ty_var) ty }
  | TyFun of ('ty_decl, 'ty_var) signature

and lty =
  | Lty of {
      t : (TyDeclIdent.t * int) list;
      ty : (TyDeclIdent.t, TyIdent.t) ty;
    }

and ('ty_decl, 'ty_var) signature = {
  tyvars : 'ty_var option;
  parameters : ('ty_decl, 'ty_var) ty list;
  return_type : ('ty_decl, 'ty_var) ty;
}

type 'a operator =
  | ONot of 'a
  | OXor of ('a * 'a)
  | OAnd of ('a * 'a)
  | OOr of ('a * 'a)

type ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm =
  | LLetPlus of {
      variable : 'term_id;
      lterm : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm;
      ands : ('term_id * ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm) list;
      term : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
    }
  | LConstructor of {
      ty : 'ty_decl;
      terms : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term list;
    }
  | LRange of {
      ty : 'ty_decl list;
      term : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
    }
  | LReindex of {
      lhs : 'ty_decl list;
      rhs : 'ty_decl list;
      lterm : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm;
    }
  | LCirc of ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm

and ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term =
  | TFalse
  | TTrue
  | TVar of 'term_id
  | TFn of { fn_ident : 'fn_ident; tyresolve : ('ty_decl, 'ty_var) ty option }
  | TLet of {
      variable : 'term_id;
      term : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
      k : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
    }
  | TLookup of {
      lterm : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm;
      index : int;
    }
  | TThunk of { lterm : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) lterm }
  | TLog of {
      message : string;
      variables : 'term_id list;
      k : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
    }
  | TOperator of ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term operator
  | TFnCall of {
      fn_name : ('fn_ident, 'term_id) Either.t;
      ty_resolve : ('ty_decl, 'ty_var) ty option;
      args : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term list;
    }

type ('ty_decl, 'fn_ident, 'ty_var, 'term_id) fn_declaration = {
  fn_name : 'fn_ident;
  tyvars : 'ty_var option;
  parameters : ('term_id * ('ty_decl, 'ty_var) ty) list;
  return_type : ('ty_decl, 'ty_var) ty;
  body : ('ty_decl, 'fn_ident, 'ty_var, 'term_id) term;
}

(* Type decl only create alias. *)
type ('ty_decl, 'ty_var) ty_declaration = {
  tyvar : 'ty_var;
  name : 'ty_decl;
  size : int;
}

type ('ty_decl, 'fn_ident, 'ty_var, 'term_id) node =
  | NFun of ('ty_decl, 'fn_ident, 'ty_var, 'term_id) fn_declaration
  | NTy of ('ty_decl, 'ty_var) ty_declaration

type ('ty_decl, 'fn_ident, 'ty_var, 'term_id) gmodule' =
  ('ty_decl, 'fn_ident, 'ty_var, 'term_id) node list

type module_ast = (string, string, string, string) gmodule'
type module' = (TyDeclIdent.t, FnIdent.t, TyIdent.t, TermIdent.t) gmodule'
