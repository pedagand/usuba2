(*
  
// https://github.com/Lelio-Brun/Obelisk
// bnf grammar generator from .mly file

<parenthesis(X)> ::= LPARENT X RPARENT

<bracketed(X)> ::= LBRACE X RBRACE

<sqrbracketed(X)> ::= LSQBRACE X RSQBRACE

<splitted(lhs, sep, rhs)> ::= lhs sep rhs

<module_> ::= <node>* EOF

<node> ::= <type_decl>
         | <fn_decl>

<type_decl> ::= TYPE TypeCstrIdentifier EQUAL TUPLE
                <sqrbracketed(IntegerLitteral)>

<fn_decl> ::= FUNCTION Identifier [<sqrbracketed(TypeVariable)>]
              <parenthesis([<splitted(Identifier, COLON, <ty>)> (COMMA
              <splitted(Identifier, COLON, <ty>)>)*])> <ty> EQUAL <term>

<ty> ::= TypeCstrIdentifier <ty>
       | TypeVariable
       | BOOL
       | FUNCTION <signature>

<signature> ::= [<sqrbracketed(TypeVariable)>] <parenthesis([<ty> (COMMA
                <ty>)*])> MINUS_SUP <ty>

<fn_identifier> ::= Identifier DOT [<sqrbracketed(<ty>)>]

<term> ::= TRUE
         | FALSE
         | Identifier
         | AMPERSAND Identifier
         | LET Identifier EQUAL <term> IN <term>
         | <lterm> <sqrbracketed(IntegerLitteral)>
         | FOLD <sqrbracketed(IntegerLitteral)> <parenthesis(<fn_identifier>
           [<parenthesis([<term> (COMMA <term>)*])>])>
           <parenthesis(<splitted(<term>, COMMA, <lterm>)>)>
         | HASH <lterm>
         | <fn_identifier> <parenthesis([<term> (COMMA <term>)*])>
         | <parenthesis(<term>)>
         | <operator>

<operator> ::= EXCLAMATION <term>
             | <term> PIPE <term>
             | <term> AMPERSAND <term>
             | <term> CARET <term>

<lterm> ::= LET_PLUS Identifier EQUAL <lterm> (AND <splitted(Identifier,
            EQUAL, <lterm>)>)* IN <term>
          | TypeCstrIdentifier <parenthesis(<term> (COMMA <term>)* )>
          | RANGE [<sqrbracketed(TypeCstrIdentifier* )>] <parenthesis(<term>)>
          | REINDEX <sqrbracketed(<splitted(TypeCstrIdentifier+, PIPE,
            TypeCstrIdentifier+)>)> <parenthesis(<lterm>)>
          | CIRC <parenthesis(<lterm>)>
          | <parenthesis(<lterm>)>
          
TypeVariable ::= '<lower_identifier>
<lower_identifier> ::= (a-z)+

TypeCstrIdentifier ::= <type_cstr_identifier>
<type_cstr_identifier> ::= [A-Z][a-zA-Z0-9_]*

Identifier ::= <identifiant>
<identifiant> ::= [a-z][a-zA-Z0-9_]*

*)

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

and ('ty_decl, 'ty_var) signature = {
  tyvars : 'ty_var option;
  parameters : ('ty_decl, 'ty_var) ty list;
  return_type : ('ty_decl, 'ty_var) ty;
}

type lty = {
  t : (TyDeclIdent.t * int) list;
  ty : (TyDeclIdent.t, TyIdent.t) ty;
}

type 'a operator =
  | ONot of 'a
  | OXor of ('a * 'a)
  | OAnd of ('a * 'a)
  | OOr of ('a * 'a)

type 't lterm =
  | LLetPlus of {
      variable : 'term_id;
      lterm : 't lterm;
      ands : ('term_id * 't lterm) list;
      term : 't term;
    }
  | LConstructor of { ty : 'ty_decl; terms : 't term list }
  | LRange of { ty : 'ty_decl list; term : 't term }
  | LReindex of { lhs : 'ty_decl list; rhs : 'ty_decl list; lterm : 't lterm }
  | LCirc of 't lterm
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

and 't term =
  | TFalse
  | TTrue
  | TVar of 'term_id
  | TFn of { fn_ident : 'fn_ident; tyresolve : ('ty_decl, 'ty_var) ty option }
  | TLet of { variable : 'term_id; term : 't term; k : 't term }
  | TLookup of { lterm : 't lterm; index : int }
  | TThunk of { lterm : 't lterm }
  | TLog of { message : string; variables : 'term_id list; k : 't term }
  | TOperator of 't term operator
  | TFnCall of {
      fn_name : ('fn_ident, 'term_id) Either.t;
      ty_resolve : ('ty_decl, 'ty_var) ty option;
      args : 't term list;
    }
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

type 't fn_declaration_ = {
  fn_name : 'fn_ident;
  tyvars : 'ty_var option;
  parameters : ('term_id * ('ty_decl, 'ty_var) ty) list;
  return_type : ('ty_decl, 'ty_var) ty;
  body : 't term;
}
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

(* Type decl only create alias. *)
type 't ty_declaration_ = {
  tyvar : 'ty_var;
  name : 'ty_decl;
  size : int;
}
  constraint 't = < ty_decl : 'ty_decl ; ty_var : 'ty_var ; .. >

type 't node_ = NFun of 't fn_declaration_ | NTy of 't ty_declaration_
type 't prog_ = 't node_ list

type pre =
  < ty_decl : string ; fn_ident : string ; ty_var : string ; term_id : string >

type pre_ty_declaration = pre ty_declaration_
type pre_fn_declaration = pre fn_declaration_
type pre_node = pre node_
type pre_prog = pre prog_

type scoped =
  < ty_decl : TyDeclIdent.t
  ; fn_ident : FnIdent.t
  ; ty_var : TyIdent.t
  ; term_id : TermIdent.t >

type ty_declaration = scoped ty_declaration_
type fn_declaration = scoped fn_declaration_
type node = scoped node_
type prog = scoped prog_
