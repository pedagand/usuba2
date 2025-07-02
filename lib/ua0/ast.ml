module Ident () = struct
  type t = { id : int; pretty : string }

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let compare lhs rhs = Int.compare lhs.id rhs.id
  let equal lhs rhs = Int.equal lhs.id rhs.id
  let pp format { id = _; pretty } = Format.fprintf format "%s" pretty
end

module TermIdent = Ident ()
module LTermIdent = Ident ()
module TyIdent = Ident ()
module TyDeclIdent = Ident ()
module FnIdent = Ident ()

type ty =
  | TyBool
  | TyVar of TyIdent.t
  | TyApp of { name : TyDeclIdent.t; ty : ty }
  | TyFun of signature

and signature = {
  tyvars : TyIdent.t list;
  parameters : ty list;
  return_type : ty;
}

type 'a operator =
  | ONot of 'a
  | OXor of ('a * 'a)
  | OAnd of ('a * 'a)
  | OOr of ('a * 'a)

type lterm =
  | LLetPlus of {
      variable : TermIdent.t;
      lterm : lterm;
      ands : (TermIdent.t * lterm) list;
      term : term;
    }
  | LConstructor of { ty : TyDeclIdent.t; terms : term list }
  | LRange of { ty : TyDeclIdent.t list; term : term }
  | LCirc of lterm

and term =
  | TFalse
  | TTrue
  | TVar of TermIdent.t
  | TFn of { fn_ident : FnIdent.t; tyresolve : ty list }
  | TLet of { variable : TermIdent.t; term : term; k : term }
  | TLookup of { lterm : lterm; index : int }
  | TThunk of { lterm : lterm }
  | TLog of { message : string; variables : TermIdent.t list; k : term }
  | TOperator of term operator
  | TFnCall of {
      fn_name : (FnIdent.t, TermIdent.t) Either.t;
      ty_resolve : ty list;
      args : term list;
    }

type fn_declaration = {
  fn_name : FnIdent.t;
  tyvars : TyIdent.t list;
  parameters : (TermIdent.t * ty) list;
  return_type : ty;
  body : term;
}

(* Type decl only create alias. *)
type ty_declaration = { tyvar : TyIdent.t; name : TyDeclIdent.t; size : int }
type node = NFun of fn_declaration | NTy of ty_declaration
type module' = node list
