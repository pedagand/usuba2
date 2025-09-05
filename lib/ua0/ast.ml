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
  | TyBool  (** [bool] *)
  | TyVar of 'ty_var  (** ['a] *)
  | TyApp of { name : 'ty_decl; ty : ('ty_decl, 'ty_var) ty }  (** [tname ty] *)
  | TyFun of ('ty_decl, 'ty_var) signature

and ('ty_decl, 'ty_var) signature = {
  tyvars : 'ty_var option;
  parameters : ('ty_decl, 'ty_var) ty list;
  return_type : ('ty_decl, 'ty_var) ty;
}
(** [['a]^? (ty1, ty2, ...) -> ty] *)

type lty = {
  t : (TyDeclIdent.t * int) list;
  ty : (TyDeclIdent.t, TyIdent.t) ty;
}

type 'a operator =
  | ONot of 'a  (** [!t] *)
  | OXor of ('a * 'a)  (** [t1 ^ t2] *)
  | OAnd of ('a * 'a)  (** [t1 & t2] *)
  | OOr of ('a * 'a)  (** [t1 | t2] *)

type 't lterm =
  | LLetPlus of {
      variable : 'term_id;
      lterm : 't lterm;
      ands : ('term_id * 't lterm) list;
      term : 't term;
    }  (** [let+ x = l {and y1 = l1 and y2 = l2 ...}^? in t] *)
  | LConstructor of { ty : 'ty_decl; terms : 't term list }
      (** [F(t1, t2, ...)] *)
  | LRange of { ty : 'ty_decl list; term : 't term }
      (** [range[F1 F2 ...](t)] *)
  | LReindex of { lhs : 'ty_decl list; rhs : 'ty_decl list; lterm : 't lterm }
      (** [reindex[ F1 F2 ... | G1 G2 ... ](l) *)
  | LCirc of 't lterm  (** [circ(l)] *)
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

and 't term =
  | TFalse  (** [false] *)
  | TTrue  (** [true] *)
  | TVar of 'term_id
  | TFn of { fn_ident : 'fn_ident; tyresolve : ('ty_decl, 'ty_var) ty option }
      (** [&f] *)
  | TLet of { variable : 'term_id; term : 't term; k : 't term }
      (** [let x = t1 in t2] *)
  | TLookup of { lterm : 't lterm; index : int }  (** [l[i]] *)
  | TThunk of { lterm : 't lterm }  (** [#l] *)
  | TLog of { message : string; variables : 'term_id list; k : 't term }
  | TFnCall of {
      fn_name : ('fn_ident, 'term_id) Either.t;
      ty_resolve : ('ty_decl, 'ty_var) ty option;
      args : 't term list;
    }  (** [f.[ty](t1, t2, ...)] *)
  | TOperator of 't term operator
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
(** [fn f [a](x1: ty1, x2: ty2, ...) ty = t] *)

(* Type decl only create alias. *)
type 't ty_declaration_ = {
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
