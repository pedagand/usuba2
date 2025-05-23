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

module TyIdent = Ident ()
module TyDeclIdent = Ident ()
module TermIdent = Ident ()
module FnIdent = Ident ()

(*let circ = FnIdent.fresh "@circ"
let anti_circ = FnIdent.fresh "@anti_circ"
let map2 = FnIdent.fresh "@map2"
let pure = FnIdent.fresh "@pure"
let app = FnIdent.fresh "@app"*)
(* type 'a = 'a Util.Position.loc *)

(* type tykind = KType | KArrow of { parameters : tykind list; return : tykind } *)

type tykind = KType | KArrow of (tykind * tykind)
type builtin = BCirc | BAntiCirc | BPure

type signature = {
  ty_vars : (TyIdent.t * tykind) list;
  parameters : ty list;
  return_type : ty;
}

and ty =
  | TyApp of { name : TyDeclIdent.t; ty_args : ty option }
  | TyVarApp of { name : TyIdent.t; ty_args : ty option }
  | TyTuple of { size : int; ty : ty }
  | TyFun of signature
  | TyBool

type indexing = { name : TyDeclIdent.t; index : int }

type 'a op =
  | Unot of 'a
  | BAnd of ('a * 'a)
  | BOr of ('a * 'a)
  | BXor of ('a * 'a)

type expression =
  | ETrue
  | EFalse
  | EVar of TermIdent.t
  | EFunVar of FnIdent.t * ty list option
  | EIndexing of { expression : expression; indexing : indexing }
  | EOp of expression op
  | EBuiltinCall of {
      builtin : builtin;
      ty_args : ty list;
      args : expression list;
    }
  | SLetPLus of {
      variable : TermIdent.t;
      ty_arg : ty;
      ty_ret : ty;
      expression : expression;
      ands : (TermIdent.t * expression) list;
      body : body;
    }
  | EFunctionCall of {
      fn_name : (FnIdent.t, TermIdent.t) Either.t;
      ty_args : ty list;
      args : expression list;
    }

and statement =
  | StDeclaration of { variable : TermIdent.t; expression : expression }
  | StLog of TermIdent.t list
  | StConstructor of {
      variable : TermIdent.t;
      ty : ty;
      expressions : expression list;
    }

and body = { statements : statement list; expression : expression }

type kasumi_type_decl = {
  ty_vars : TyIdent.t list;
  ty_name : TyDeclIdent.t;
  definition : ty;
}

type kasumi_function_decl = {
  fn_name : FnIdent.t;
  ty_vars : (TyIdent.t * tykind) list;
  parameters : (TermIdent.t * ty) list;
  return_type : ty;
  body : body;
}

type kasumi_node =
  | KnTypedecl of kasumi_type_decl
  | KnFundecl of kasumi_function_decl

type ksm_module = kasumi_node list
