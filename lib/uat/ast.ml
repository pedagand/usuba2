open Ua0
module TyDeclIdent = Ast.TyDeclIdent
module TermIdent = Ast.TermIdent
module FnIdent = Ast.FnIdent
module TyIdent = Ast.TyIdent

type ty = (TyDeclIdent.t, TyIdent.t) Ast.ty
type lty = Ast.lty
type signature = (TyDeclIdent.t, TyIdent.t) Ast.signature
type 'a tys = 'a * ty
type 'a ltys = 'a * lty
type 'a operator = 'a Ast.operator

type lterm =
  | LLetPlus of {
      variable : TermIdent.t;
      lterm : lterm ltys;
      ands : (TermIdent.t * lterm ltys) list;
      term : term tys;
    }
  | LConstructor of { ty : TyDeclIdent.t; terms : term tys list }
  | LRange of { ty : TyDeclIdent.t list; term : term tys }
  | LReindex of {
      lhs : TyDeclIdent.t list;
      rhs : TyDeclIdent.t list;
      lterm : lterm ltys;
    }
  | LCirc of lterm ltys

and term =
  | TFalse
  | TTrue
  | TVar of TermIdent.t
  | TFn of { fn_ident : FnIdent.t }
  | TLet of { variable : TermIdent.t; term : term tys; k : term tys }
  | TLookup of { lterm : lterm ltys; index : int }
  | TThunk of { lterm : lterm ltys }
  | TLog of { message : string; variables : TermIdent.t tys list; k : term tys }
  | TOperator of term tys operator
  | TFnCall of {
      fn_name : (FnIdent.t, TermIdent.t) Either.t;
      ty_resolve : ty option;
      args : term tys list;
    }

type fn_declaration = {
  fn_name : FnIdent.t;
  tyvars : TyIdent.t option;
  parameters : (TermIdent.t * ty) list;
  return_type : ty;
  body : term tys;
}

type ty_declaration = Ua0.Ast.ty_declaration
type node = NFun of fn_declaration | NTy of ty_declaration
type prog = node list
