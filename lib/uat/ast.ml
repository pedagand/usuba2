open Ua0
module TyDeclIdent = Ast.TyDeclIdent
module TermIdent = Ast.TermIdent
module FnIdent = Ast.FnIdent
module TyIdent = Ast.TyIdent

type ty = (TyDeclIdent.t, TyIdent.t) Ast.ty
type lty = Ast.lty
type signature = (TyDeclIdent.t, TyIdent.t) Ast.signature
